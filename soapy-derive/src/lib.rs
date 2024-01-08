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
    let fields_len = fields.len();
    let (vis_all, (ty_all, ident_all)): (Vec<_>, (Vec<_>, Vec<FieldIdent>)) = fields
        .into_iter()
        .enumerate()
        .map(|(i, field)| (field.vis, (field.ty, (i, field.ident).into())))
        .unzip();
    let ident_rev: Vec<_> = ident_all.iter().cloned().rev().collect();

    let (_vis_head, ident_head, ty_head) = match (
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

    let _vis_tail: Vec<_> = vis_all.iter().skip(1).cloned().collect();
    let ty_tail: Vec<_> = ty_all.iter().skip(1).cloned().collect();
    let ident_tail: Vec<_> = ident_all.iter().skip(1).cloned().collect();

    let offsets = format_ident!("{ident}SoaOffsets");
    let slices = format_ident!("{ident}SoaSlices");
    let slices_mut = format_ident!("{ident}SoaSlicesMut");
    let item_ref = format_ident!("{ident}SoaRef");
    let item_ref_mut = format_ident!("{ident}SoaRefMut");
    let raw = format_ident!("{ident}RawSoa");

    let raw_body = match kind {
        FieldKind::Named => quote! {
            { #(#vis_all #ident_all: ::std::ptr::NonNull<#ty_all>,)* }
        },
        FieldKind::Unnamed => quote! {
            ( #(#vis_all ::std::ptr::NonNull<#ty_all>),* );
        },
    };

    let offsets_body = match kind {
        FieldKind::Named => quote! {
            { #(#ident_tail: usize),* }
        },
        FieldKind::Unnamed => {
            let tuple_fields = std::iter::repeat(quote! { usize }).take(fields_len - 1);
            quote! {
                ( #(#tuple_fields),* );
            }
        }
    };

    let slices_def = match kind {
        FieldKind::Named => quote! {
            { #(#[allow(unused)] #vis_all #ident_all: &'a [#ty_all]),* }
        },
        FieldKind::Unnamed => quote! {
            ( #(#[allow(unused)] #vis_all &'a [#ty_all]),* );
        },
    };

    let slices_mut_def = match kind {
        FieldKind::Named => quote! {
            { #(#[allow(unused)] #vis_all #ident_all: &'a mut [#ty_all]),* }
        },
        FieldKind::Unnamed => quote! {
            ( #(#[allow(unused)] #vis_all &'a mut [#ty_all]),* );
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

    let offsets_vars: Vec<_> = ident_tail
        .iter()
        .enumerate()
        .map(|(i, ident)| match ident {
            FieldIdent::Named(ident) => ident.clone(),
            FieldIdent::Unnamed(_) => format_ident!("f{}", i),
        })
        .collect();

    let offsets_idents: Vec<FieldIdent> = ident_tail
        .iter()
        .enumerate()
        .map(|(i, ident)| {
            let ident = match ident {
                FieldIdent::Named(ident) => Some(ident.clone()),
                FieldIdent::Unnamed(_) => None,
            };
            (i, ident).into()
        })
        .collect();

    let construct_offsets = match kind {
        FieldKind::Named => quote! {
            { #(#offsets_vars),* }
        },
        FieldKind::Unnamed => quote! {
            ( #(#offsets_vars),* )
        },
    };

    Ok(quote! {
        #[automatically_derived]
        impl ::soapy_shared::Soapy for #ident {
            type RawSoa = #raw;
        }

        // TODO: Remove and just use a tuple
        #[automatically_derived]
        #[derive(Copy, Clone)]
        struct #offsets #offsets_body

        #[automatically_derived]
        #[derive(Copy, Clone)]
        #vis struct #raw #raw_body

        #[automatically_derived]
        #vis struct #slices<'a> #slices_def
        #[automatically_derived]
        #vis struct #slices_mut<'a> #slices_mut_def
        #[automatically_derived]
        #vis struct #item_ref<'a> #item_ref_def
        #[automatically_derived]
        #vis struct #item_ref_mut<'a> #item_ref_mut_def

        #[automatically_derived]
        impl #raw {
            #[inline]
            fn layout_and_offsets(cap: usize) -> (::std::alloc::Layout, #offsets) {
                // TODO: Replace unwraps with unwrap_unchecked
                let layout = ::std::alloc::Layout::array::<#ty_head>(cap).unwrap();
                #(
                    let array = ::std::alloc::Layout::array::<#ty_tail>(cap).unwrap();
                    let (layout, #offsets_vars) = layout.extend(array).unwrap();
                )*
                let offsets = #offsets #construct_offsets;
                (layout, offsets)
            }

            #[inline]
            unsafe fn with_offsets(ptr: *mut u8, offsets: #offsets) -> Self {
                Self {
                    #ident_head: ::std::ptr::NonNull::new_unchecked(ptr as *mut #ty_head),
                    #(
                        #ident_tail: ::std::ptr::NonNull::new_unchecked(
                            ptr.add(offsets.#offsets_idents) as *mut #ty_tail,
                        ),
                    )*
                }
            }
        }

        #[automatically_derived]
        impl ::soapy_shared::RawSoa<#ident> for #raw {
            type Ref<'a> = #item_ref<'a> where Self: 'a;
            type RefMut<'a> = #item_ref_mut<'a> where Self: 'a;

            #[inline]
            fn dangling() -> Self {
                Self {
                    #(#ident_all: ::std::ptr::NonNull::dangling(),)*
                }
            }

            #[inline]
            fn as_ptr(self) -> *mut u8 {
                self.#ident_head.as_ptr() as *mut u8
            }

            #[inline]
            unsafe fn from_parts(ptr: *mut u8, capacity: usize) -> Self {
                let (_, offsets) = Self::layout_and_offsets(capacity);
                Self::with_offsets(ptr, offsets)
            }

            #[inline]
            unsafe fn alloc(capacity: usize) -> Self {
                let (new_layout, new_offsets) = Self::layout_and_offsets(capacity);
                let ptr = ::std::alloc::alloc(new_layout);
                assert_ne!(ptr as *const u8, ::std::ptr::null());
                Self::with_offsets(ptr, new_offsets)
            }

            #[inline]
            unsafe fn realloc_grow(&mut self, old_capacity: usize, new_capacity: usize, length: usize) {
                let (new_layout, new_offsets) = Self::layout_and_offsets(new_capacity);
                let (old_layout, old_offsets) = Self::layout_and_offsets(old_capacity);
                // Grow allocation first
                let ptr = self.#ident_head.as_ptr() as *mut u8;
                let ptr = ::std::alloc::realloc(ptr, old_layout, new_layout.size());
                assert_ne!(ptr as *const u8, ::std::ptr::null());
                // Pointer may have moved, can't reuse self
                let old = Self::with_offsets(ptr, old_offsets);
                let new = Self::with_offsets(ptr, new_offsets);
                // Copy do destination in reverse order to avoid
                // overwriting data
                #(::std::ptr::copy(old.#ident_rev.as_ptr(), new.#ident_rev.as_ptr(), length);)*
                *self = new;
            }

            #[inline]
            unsafe fn realloc_shrink(&mut self, old_capacity: usize, new_capacity: usize, length: usize) {
                let (old_layout, _) = Self::layout_and_offsets(old_capacity);
                let (new_layout, new_offsets) = Self::layout_and_offsets(new_capacity);
                // Move data before reallocating as some data
                // may be past the end of the new allocation.
                // Copy from front to back to avoid overwriting data.
                let ptr = self.#ident_head.as_ptr() as *mut u8;
                let dst = Self::with_offsets(ptr, new_offsets);
                #(::std::ptr::copy(self.#ident_all.as_ptr(), dst.#ident_all.as_ptr(), length);)*
                let ptr = ::std::alloc::realloc(ptr, old_layout, new_layout.size());
                assert_ne!(ptr as *const u8, ::std::ptr::null());
                // Pointer may have moved, can't reuse dst
                *self = Self::with_offsets(ptr, new_offsets);
            }

            #[inline]
            unsafe fn dealloc(self, old_capacity: usize) {
                let (layout, _) = Self::layout_and_offsets(old_capacity);
                ::std::alloc::dealloc(self.as_ptr(), layout);
            }

            #[inline]
            unsafe fn copy(&mut self, src: usize, dst: usize, count: usize) {
                #(
                    let ptr = self.#ident_all.as_ptr();
                    ::std::ptr::copy(ptr.add(src), ptr.add(dst), count);
                )*
            }

            #[inline]
            unsafe fn set(&mut self, index: usize, element: #ident) {
                #(self.#ident_all.as_ptr().add(index).write(element.#ident_all);)*
            }

            #[inline]
            unsafe fn get(&self, index: usize) -> #ident {
                #ident {
                    #(#ident_all: self.#ident_all.as_ptr().add(index).read(),)*
                }
            }

            #[inline]
            unsafe fn get_ref<'a>(&self, index: usize) -> #item_ref<'a> {
                #item_ref {
                    #(#ident_all: self.#ident_all.as_ptr().add(index).as_ref().unwrap_unchecked(),)*
                }
            }

            #[inline]
            unsafe fn get_mut<'a>(&self, index: usize) -> #item_ref_mut<'a> {
                #item_ref_mut {
                    #(#ident_all: self.#ident_all.as_ptr().add(index).as_mut().unwrap_unchecked(),)*
                }
            }
        }
    })
}

fn zst_struct(ident: Ident, vis: Visibility, kind: ZstKind) -> Result<TokenStream2, SoapyError> {
    let raw = format_ident!("{ident}RawSoa");
    let unit_construct = match kind {
        ZstKind::Unit => quote! {},
        ZstKind::Empty => quote! { {} },
        ZstKind::EmptyTuple => quote! { () },
    };

    Ok(quote! {
        #[automatically_derived]
        impl ::soapy_shared::Soapy for #ident {
            type RawSoa = #raw;
        }

        #[automatically_derived]
        #[derive(Copy, Clone)]
        #vis struct #raw;

        #[automatically_derived]
        impl ::soapy_shared::RawSoa<#ident> for #raw {
            type Ref<'a> = #ident;
            type RefMut<'a> = #ident;

            #[inline]
            fn dangling() -> Self { Self }
            #[inline]
            fn as_ptr(self) -> *mut u8 { ::std::ptr::null::<u8>() as *mut _ }
            #[inline]
            unsafe fn from_parts(ptr: *mut u8, capacity: usize) -> Self { Self }
            #[inline]
            unsafe fn alloc(capacity: usize) -> Self { Self }
            #[inline]
            unsafe fn realloc_grow(&mut self, old_capacity: usize, new_capacity: usize, length: usize) { }
            #[inline]
            unsafe fn realloc_shrink(&mut self, old_capacity: usize, new_capacity: usize, length: usize) { }
            #[inline]
            unsafe fn dealloc(self, old_capacity: usize) { }
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
