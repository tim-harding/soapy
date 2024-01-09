use std::alloc::{Layout, LayoutError};

pub trait Soapy: Sized {
    type SoaSlice: SoaSlice<Self> + ?Sized;
}

/// A low-level utility providing fundamental operations needed by `Soa<T>`
///
/// In particular, it manages an allocation and a set of pointers into
/// the allocation. Each of the pointers corresponds to a field of the type `T`
/// and is treated as an array of values of that field's type.
///
/// # Safety
///
/// Use of this type is inherently unsafe and should be restricted to the
/// implementation of `Soa`. There is no guarantee of contract stability between
/// versions. Further, this type will **neither** deallocate its memory **nor**
/// drop its contents when it is dropped. Special care must be taken to avoid
/// unsound use.
///
/// In the method documentation, it is established that `PREV_CAP` is
///
/// - 0 if no previous calls to [`RawSoa::realloc_grow`] or [`RawSoa::realloc_shrink`] have been
/// made, or
/// - the same value as was used for `new_capacity` in previous calls
/// to [`RawSoa::realloc_grow`] and [`RawSoa::realloc_shrink`]
pub unsafe trait SoaSlice<T> {
    /// For each field with type `F` in `T`, `Ref` has a field with type
    /// `&F`
    type Ref<'a>
    where
        Self: 'a;

    /// For each field with type `F` in `T`, `RefMut` has a field with type
    /// `&mut F`
    type RefMut<'a>
    where
        Self: 'a;

    unsafe fn from_ptr(ptr: *mut u8) -> *mut Self;

    /// Gets the layout and offsets to the arrays from the beginning of an
    /// allocation made with this layout.
    fn layout_and_offsets(capacity: usize) -> Result<(Layout, &'static [usize]), LayoutError>;

    /// Copies `count` elements from `src` index to `dst` index in each of the
    /// arrays.
    ///
    /// # Safety
    ///
    /// The caller must ensure that
    ///
    /// - `src < PREV_CAP`
    /// - `dst < PREV_CAP`
    /// - `src + count <= PREV_CAP`
    /// - `dst + count <= PREV_CAP`
    unsafe fn copy(&mut self, src: usize, dst: usize, count: usize);

    /// Sets the element at `index` to `element`.
    ///
    /// # Safety
    ///
    /// The caller must ensure that
    ///
    /// - `index < PREV_CAP`
    unsafe fn set(&mut self, index: usize, element: T);

    /// Gets the element at `index`.
    ///
    /// # Safety
    ///
    /// After calling `get`, the element at `index` should be treated as having
    /// been moved out of `Self` and into the caller. Therefore, it is no longer
    /// valid to reference this array element either by value or by reference.
    /// The caller must ensure that
    ///
    /// - `index < PREV_CAP`
    unsafe fn get(&self, index: usize) -> T;

    /// Gets a reference to the element at `index`.
    ///
    /// # Safety
    ///
    /// The caller must ensure that
    ///
    /// - `index < PREV_CAP`
    unsafe fn get_ref<'a>(&self, index: usize) -> Self::Ref<'a>;

    /// Gets a mutable reference to the element at `index`.
    ///
    /// # Safety
    ///
    /// The caller must ensure that
    ///
    /// - `index < PREV_CAP`
    unsafe fn get_mut<'a>(&self, index: usize) -> Self::RefMut<'a>;
}
