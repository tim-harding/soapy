use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote, quote_spanned, ToTokens};
use std::fmt::{self, Display, Formatter};
use syn::{
    parse_macro_input, punctuated::Punctuated, token::Comma, Data, DeriveInput, Field, Fields,
    Ident, Index, Visibility,
};

#[proc_macro_derive(Soapy)]
pub fn soa(input: TokenStream) -> TokenStream {
    let input: DeriveInput = parse_macro_input!(input);
    let span = input.ident.span();
    match soa_inner(input) {
        Ok(tokens) => tokens,
        Err(e) => {
            let s: &str = e.into();
            quote_spanned! {
                span => compile_error!(#s);
            }
        }
    }
    .into()
}

fn soa_inner(input: DeriveInput) -> Result<TokenStream2, SoapyError> {
    let DeriveInput {
        ident, vis, data, ..
    } = input;
    match data {
        Data::Struct(strukt) => match strukt.fields {
            Fields::Named(fields) => fields_struct(ident, vis, fields.named, FieldKind::Named),
            Fields::Unit => zst_struct(ident, vis, ZstKind::Unit),
            Fields::Unnamed(fields) => {
                fields_struct(ident, vis, fields.unnamed, FieldKind::Unnamed)
            }
        },
        Data::Enum(_) | Data::Union(_) => Err(SoapyError::NotAStruct),
    }
}

fn fields_struct(
    ident: Ident,
    vis: Visibility,
    fields: Punctuated<Field, Comma>,
    kind: FieldKind,
) -> Result<TokenStream2, SoapyError> {
    let (vis_all, (ty_all, ident_all)): (Vec<_>, (Vec<_>, Vec<FieldIdent>)) = fields
        .into_iter()
        .enumerate()
        .map(|(i, field)| (field.vis, (field.ty, (i, field.ident).into())))
        .unzip();

    let (vis_head, ident_head, ty_head) = match (
        vis_all.first().cloned(),
        ty_all.first().cloned(),
        ident_all.first().cloned(),
    ) {
        (Some(vis), Some(ty), Some(ident)) => (vis, ident, ty),
        _ => {
            let zst_kind = match kind {
                FieldKind::Named => ZstKind::Empty,
                FieldKind::Unnamed => ZstKind::EmptyTuple,
            };
            return zst_struct(ident, vis, zst_kind);
        }
    };

    let vis_tail: Vec<_> = vis_all.iter().skip(1).cloned().collect();
    let ty_tail: Vec<_> = ty_all.iter().skip(1).cloned().collect();
    let ident_tail: Vec<_> = ident_all.iter().skip(1).cloned().collect();

    let tail_len = vis_tail.len();

    let item_ref = format_ident!("{ident}SoaRef");
    let item_ref_mut = format_ident!("{ident}SoaRefMut");
    let slice = format_ident!("{ident}SoaSlice");

    let slice_body = match kind {
        FieldKind::Named => quote! {
            {
                #( #vis_tail #ident_tail: ::std::ptr::NonNull<#ty_tail>, )*
                #vis_head #ident_head: [#ty_head],
            }
        },
        FieldKind::Unnamed => quote! {
            (
                #( #vis_tail ::std::ptr::NonNull<#ty_tail>, )*
                #vis_head [#ty_head],
            )
        },
    };

    let item_ref_def = match kind {
        FieldKind::Named => quote! {
            { #(#[allow(unused)] #vis_all #ident_all: &'a #ty_all),* }
        },
        FieldKind::Unnamed => quote! {
            ( #(#[allow(unused)] #vis_all &'a #ty_all),* );
        },
    };

    let item_ref_mut_def = match kind {
        FieldKind::Named => quote! {
            { #(#[allow(unused)] #vis_all #ident_all: &'a mut #ty_all),* }
        },
        FieldKind::Unnamed => quote! {
            ( #(#[allow(unused)] #vis_all &'a mut #ty_all),* );
        },
    };

    let offset_vars: Vec<_> = ident_tail
        .iter()
        .enumerate()
        .map(|(i, ident)| match ident {
            FieldIdent::Named(ident) => ident.clone(),
            FieldIdent::Unnamed(_) => format_ident!("f{}", i),
        })
        .collect();

    Ok(quote! {
        #[automatically_derived]
        impl ::soapy_shared::Soapy for #ident {
            type SoaSlice = #slice;
        }

        #[automatically_derived]
        #vis struct #slice #slice_body

        #[automatically_derived]
        #vis struct #item_ref<'a> #item_ref_def
        #[automatically_derived]
        #vis struct #item_ref_mut<'a> #item_ref_mut_def

        #[automatically_derived]
        unsafe impl ::soapy_shared::SoaSlice<#ident> for #slice {
            type Ref<'a> = #item_ref<'a> where Self: 'a;
            type RefMut<'a> = #item_ref_mut<'a> where Self: 'a;

            unsafe fn from_ptr(ptr: *mut u8) -> *mut Self {
                let slice = ::std::slice::from_raw_parts_mut(ptr, 0);
                slice as *mut [u8] as *mut Self
            }

            #[inline]
            fn layout_and_offsets(capacity: usize)
                -> Result<(::std::alloc::Layout, &'static [usize]), ::std::alloc::LayoutError>
            {
                // First tail_len fields are pointers into the allocation
                let layout = ::std::alloc::Layout::array::<::std::ptr::NonNull<u8>>(#tail_len)?;

                // Don't need an offset for the first array as it will just be
                // at self.#head_ident, the dynamically-sized field
                let array = ::std::alloc::Layout::array::<#ty_head>(capacity)?;
                let (layout, _) = layout.extend(array)?;

                #(
                    let array = ::std::alloc::Layout::array::<#ty_tail>(capacity)?;
                    let (layout, #offset_vars) = layout.extend(array)?;
                )*

                Ok((layout, &[#(#offset_vars),*]))
            }

            #[inline]
            unsafe fn copy(&mut self, src: usize, dst: usize, count: usize) {
                let ptr = self.#ident_head.as_ptr().cast_mut();
                ::std::ptr::copy(ptr.add(src), ptr.add(dst), count);
                #(
                    let ptr = self.#ident_tail.as_ptr();
                    ::std::ptr::copy(ptr.add(src), ptr.add(dst), count);
                )*
            }

            #[inline]
            unsafe fn set(&mut self, index: usize, element: #ident) {
                self.#ident_head.as_ptr().cast_mut().add(index).write(element.#ident_head);
                #(self.#ident_tail.as_ptr().add(index).write(element.#ident_tail);)*
            }

            #[inline]
            unsafe fn get(&self, index: usize) -> #ident {
                #ident {
                    #ident_head: self.#ident_head.as_ptr().cast_mut().add(index).read(),
                    #(#ident_tail: self.#ident_tail.as_ptr().add(index).read(),)*
                }
            }

            #[inline]
            unsafe fn get_ref<'a>(&self, index: usize) -> #item_ref<'a> {
                #item_ref {
                    #ident_head: self.#ident_head.as_ptr().cast_mut().add(index).as_ref().unwrap_unchecked(),
                    #(#ident_tail: self.#ident_tail.as_ptr().add(index).as_ref().unwrap_unchecked(),)*
                }
            }

            #[inline]
            unsafe fn get_mut<'a>(&self, index: usize) -> #item_ref_mut<'a> {
                #item_ref_mut {
                    #ident_head: self.#ident_head.as_ptr().cast_mut().add(index).as_mut().unwrap_unchecked(),
                    #(#ident_tail: self.#ident_tail.as_ptr().add(index).as_mut().unwrap_unchecked(),)*
                }
            }
        }
    })
}

fn zst_struct(ident: Ident, vis: Visibility, kind: ZstKind) -> Result<TokenStream2, SoapyError> {
    let slice = format_ident!("{ident}SoaSlice");
    let unit_construct = match kind {
        ZstKind::Unit => quote! {},
        ZstKind::Empty => quote! { {} },
        ZstKind::EmptyTuple => quote! { () },
    };

    Ok(quote! {
        #[automatically_derived]
        impl ::soapy_shared::Soapy for #ident {
            type SoaSlice = #slice;
        }

        #[automatically_derived]
        #[derive(Copy, Clone)]
        #vis struct #slice;

        #[automatically_derived]
        unsafe impl ::soapy_shared::SoaSlice<#ident> for #slice {
            type Ref<'a> = #ident;
            type RefMut<'a> = #ident;

            #[inline]
            fn layout_and_offsets(capacity: usize)
                -> Result<(::std::alloc::Layout, &'static [usize]), ::std::alloc::LayoutError>
            {
                Ok((
                    ::std::alloc::Layout::new::<()>(),
                    &[],
                ))
            }

            #[inline]
            unsafe fn copy(&mut self, src: usize, dst: usize, count: usize) { }
            #[inline]
            unsafe fn set(&mut self, index: usize, element: #ident) { }
            #[inline]
            unsafe fn get(&self, index: usize) -> #ident { #ident #unit_construct }
            #[inline]
            unsafe fn get_ref<'a>(&self, index: usize) -> Self::Ref<'a> { #ident #unit_construct }
            #[inline]
            unsafe fn get_mut<'a>(&self, index: usize) -> Self::RefMut<'a> { #ident #unit_construct }
            unsafe fn from_ptr(ptr: *mut u8) -> *mut Self { ::std::ptr::null() }
        }
    })
}

#[derive(Clone, PartialEq, Eq)]
enum FieldIdent {
    Named(Ident),
    Unnamed(Index),
}

impl From<(usize, Option<Ident>)> for FieldIdent {
    fn from(value: (usize, Option<Ident>)) -> Self {
        match value {
            (_, Some(ident)) => Self::Named(ident),
            (i, None) => Self::Unnamed(Index::from(i)),
        }
    }
}

impl ToTokens for FieldIdent {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match self {
            FieldIdent::Named(ident) => ident.to_tokens(tokens),
            FieldIdent::Unnamed(i) => i.to_tokens(tokens),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum FieldKind {
    Named,
    Unnamed,
}

enum ZstKind {
    /// struct Unit;
    Unit,
    /// struct Unit {};
    Empty,
    #[allow(unused)]
    /// struct Unit();
    EmptyTuple,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum SoapyError {
    NotAStruct,
}

impl std::error::Error for SoapyError {}

impl Display for SoapyError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s: &str = (*self).into();
        write!(f, "{}", s)
    }
}

impl From<SoapyError> for &str {
    fn from(value: SoapyError) -> Self {
        match value {
            SoapyError::NotAStruct => "Soapy only applies to structs",
        }
    }
}
