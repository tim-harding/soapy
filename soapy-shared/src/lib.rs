pub trait Soapy: Sized {
    type RawSoa: RawSoa<Self>;
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
pub trait RawSoa<T>: Copy + Clone {
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

    /// Creates a `Self` with dangling pointers for all its fields and without
    /// allocating memory.
    fn dangling() -> Self;

    /// Returns the pointer that contains the allocated capacity.
    ///
    /// The pointer will point to invalid memory in these circumstances:
    /// - `PREV_CAP == 0`
    /// - `size_of::<T>() == 0`
    fn as_ptr(self) -> *mut u8;

    /// Construct a new `Self` with the given pointer and capacity.
    ///
    /// # Safety
    ///
    /// The pointer should come from a previous instance of `Self` with
    /// `PREV_CAP == capacity`.
    unsafe fn from_parts(ptr: *mut u8, capacity: usize) -> Self;

    /// Allocates room for `capacity` elements.
    ///
    /// # Safety
    ///
    /// The caller must ensure that
    ///
    /// - `size_of::<T>() > 0`
    /// - `capacity > 0`
    /// - `PREV_CAP == 0` (Otherwise use [`RawSoa::realloc_grow`])
    unsafe fn alloc(capacity: usize) -> Self;

    /// Grows the allocation with room for `old_capacity` elements to fit
    /// `new_capacity` elements and moves `length` number of array elements to
    /// their new locations.
    ///
    /// # Safety
    ///
    /// The caller must ensure that
    ///
    /// - `size_of::<T>() > 0`
    /// - `new_capacity > old_capacity`
    /// - `length <= old_capacity`
    /// - `old_capacity > 0` (Otherwise use [`RawSoa::alloc`])
    unsafe fn realloc_grow(&mut self, old_capacity: usize, new_capacity: usize, length: usize);

    /// Shrinks the allocation with room for `old_capacity` elements to fit
    /// `new_capacity` elements and moves `length` number of array elements to
    /// their new locations.
    ///
    /// # Safety
    ///
    /// The caller must ensure that
    ///
    /// - `size_of::<T>() > 0`
    /// - `new_capacity < old_capacity`
    /// - `length <= new_capacity`
    /// - `old_capacity > 0` (Otherwise use [`RawSoa::dealloc`])
    unsafe fn realloc_shrink(&mut self, old_capacity: usize, new_capacity: usize, length: usize);

    /// Deallocates the allocation with room for `capacity` elements. The state
    /// after calling this method is equivalent to [`RawSoa::dangling`].
    ///
    /// # Safety
    ///
    /// `Self` no longer valid after calling this function. The caller must ensure that
    ///
    /// - `size_of::<T>() > 0`
    /// - `old_capacity > 0`
    unsafe fn dealloc(self, old_capacity: usize);

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
