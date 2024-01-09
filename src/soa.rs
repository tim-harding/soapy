use crate::{IntoIter, Iter, IterMut};
use soapy_shared::{SoaSlice, Soapy};
use std::{
    alloc::{alloc, dealloc, handle_alloc_error, realloc, Layout, LayoutError},
    cmp::Ordering,
    fmt::{self, Formatter},
    marker::PhantomData,
    mem::{size_of, ManuallyDrop},
    ops::{ControlFlow, Deref},
    ptr::NonNull,
};

pub struct Soa<T>
where
    T: Soapy,
{
    pub(crate) length: usize,
    pub(crate) capacity: usize,
    pub(crate) raw: NonNull<T::SoaSlice>,
}

unsafe impl<T> Send for Soa<T> where T: Send + Soapy {}
unsafe impl<T> Sync for Soa<T> where T: Sync + Soapy {}

impl<T> Soa<T>
where
    T: Soapy,
{
    const SMALL_CAPACITY: usize = 4;

    fn layout_and_offsets(capacity: usize) -> Result<(Layout, &'static [usize]), LayoutError> {
        <T::SoaSlice as SoaSlice<T>>::layout_and_offsets(capacity)
    }

    unsafe fn set_array_pointers(ptr: *mut u8, offsets: &[usize]) {
        for (i, &offset) in offsets.iter().enumerate() {
            let array_ptr = ptr.cast::<NonNull<u8>>().add(i).as_mut().unwrap_unchecked();
            *array_ptr = NonNull::new_unchecked(ptr.add(offset));
        }
    }

    fn alloc(capacity: usize) -> NonNull<T::SoaSlice> {
        debug_assert_ne!(size_of::<T>(), 0);
        let (layout, offsets) = Self::layout_and_offsets(capacity).unwrap();

        let ptr = unsafe { alloc(layout) };
        if ptr.is_null() {
            handle_alloc_error(layout);
        }

        unsafe {
            Self::set_array_pointers(ptr, offsets);
            // let slice = std::slice::from_raw_parts_mut(ptr, 0);
            // let ptr = slice as *mut [u8] as *mut T::SoaSlice;
            NonNull::new_unchecked(<T::SoaSlice as SoaSlice<T>>::from_ptr(ptr))
        }
    }

    fn realloc_grow(&mut self, new_capacity: usize) {
        debug_assert_ne!(size_of::<T>(), 0);
        debug_assert!(new_capacity > self.capacity);
        debug_assert_ne!(self.capacity, 0);

        // SAFETY: We have already constructed this layout successfully for a
        // previous allocation
        let (old_layout, old_offsets) =
            unsafe { Self::layout_and_offsets(self.capacity).unwrap_unchecked() };
        let (new_layout, new_offsets) = Self::layout_and_offsets(new_capacity).unwrap();
        debug_assert_eq!(new_offsets.len(), old_offsets.len());

        // Grow allocation first
        let ptr = self.raw.as_ptr() as *mut u8;
        let ptr = unsafe { realloc(ptr, old_layout, new_layout.size()) };
        if ptr.is_null() {
            handle_alloc_error(new_layout);
        }

        // Copy to destination in reverse order to avoid overwriting data
        for (i, (&new_offset, &old_offset)) in
            new_offsets.iter().zip(old_offsets.iter()).enumerate().rev()
        {
            unsafe {
                let src = ptr.add(old_offset);
                let dst = ptr.add(new_offset);
                src.copy_to(dst, self.length);
                // Update array pointer
                *ptr.cast::<NonNull<u8>>().add(i).as_mut().unwrap_unchecked() =
                    NonNull::new_unchecked(dst);
            }
        }

        self.raw = unsafe { NonNull::new_unchecked(<T::SoaSlice as SoaSlice<T>>::from_ptr(ptr)) };
        self.capacity = new_capacity;
    }

    fn realloc_shrink(&mut self, new_capacity: usize) {
        debug_assert_ne!(size_of::<T>(), 0);
        debug_assert!(new_capacity < self.capacity);
        debug_assert_ne!(new_capacity, 0);

        // SAFETY: We have already constructed this layout successfully for a
        // previous allocation
        let (old_layout, _) = unsafe { Self::layout_and_offsets(self.capacity).unwrap_unchecked() };
        let (new_layout, new_offsets) = Self::layout_and_offsets(new_capacity).unwrap();

        // Move data before reallocating as some data may be past the end of the
        // new allocation. Copy from front to back to avoid overwriting data.
        let ptr = self.raw.as_ptr() as *mut u8;
        for (i, &new_offset) in new_offsets.iter().enumerate() {
            unsafe {
                let src = *self.raw.as_ptr().cast::<NonNull<u8>>().add(i);
                let dst = ptr.add(new_offset);
                src.as_ptr().copy_to(dst, self.length);
                // Can't set the new array pointers here like we can in
                // realloc_grow because the pointer might move during realloc
            }
        }

        let ptr = unsafe { ::std::alloc::realloc(ptr, old_layout, new_layout.size()) };
        if ptr.is_null() {
            handle_alloc_error(new_layout);
        }

        unsafe {
            Self::set_array_pointers(ptr, new_offsets);
        }

        self.raw = unsafe { NonNull::new_unchecked(<T::SoaSlice as SoaSlice<T>>::from_ptr(ptr)) };
        self.capacity = new_capacity;
    }

    fn dealloc(&mut self) {
        debug_assert_ne!(size_of::<T>(), 0);
        debug_assert!(self.capacity > 0);
        let (layout, _) = <T::SoaSlice as SoaSlice<T>>::layout_and_offsets(self.capacity).unwrap();
        unsafe { dealloc(self.raw.as_ptr() as *mut u8, layout) };
        self.capacity = 0;
        self.raw = NonNull::dangling();
    }

    /// Constructs a new, empty `Soa<T>`.
    ///
    /// The container will not allocate until elements are pushed onto it.
    pub fn new() -> Self {
        Self {
            length: 0,
            capacity: if size_of::<T>() == 0 { usize::MAX } else { 0 },
            raw: NonNull::dangling(),
        }
    }

    /// Construct a new, empty `Soa<T>` with at least the specified capacity.
    ///
    /// The container will be able to hold `capacity` elements without
    /// reallocating. If the `capacity` is 0, the container will not allocate.
    /// Note that although the returned vector has the minimum capacity
    /// specified, the vector will have a zero length. The capacity will be as
    /// specified unless `T` is zero-sized, in which case the capacity will be
    /// `usize::MAX`.
    pub fn with_capacity(capacity: usize) -> Self {
        match capacity {
            0 => Self::new(),
            capacity => {
                if size_of::<T>() == 0 {
                    Self {
                        length: 0,
                        capacity: usize::MAX,
                        raw: NonNull::dangling(),
                    }
                } else {
                    Self {
                        length: 0,
                        capacity,
                        raw: Self::alloc(capacity),
                    }
                }
            }
        }
    }

    /// Returns the number of elements in the vector, also referred to as its
    /// length.
    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns true if the container contains no elements.
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// Returns the total number of elements the container can hold without
    /// reallocating.
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Appends an element to the back of a collection.
    pub fn push(&mut self, element: T) {
        self.maybe_grow();
        unsafe {
            self.raw.as_mut().set(self.length, element);
        }
        self.length += 1;
    }

    /// Removes the last element from a vector and returns it, or [`None`] if it
    /// is empty.
    pub fn pop(&mut self) -> Option<T> {
        if self.length == 0 {
            None
        } else {
            self.length -= 1;
            Some(unsafe { self.raw.as_mut().get(self.length) })
        }
    }

    /// Inserts an element at position `index`, shifting all elements after it
    /// to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`
    pub fn insert(&mut self, index: usize, element: T) {
        assert!(index <= self.length, "index out of bounds");
        self.maybe_grow();
        unsafe {
            let raw = self.raw.as_mut();
            raw.copy(index, index + 1, self.length - index);
            raw.set(index, element);
        }
        self.length += 1;
    }

    /// Removes and returns the element at position index within the vector,
    /// shifting all elements after it to the left.
    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.length, "index out of bounds");
        self.length -= 1;
        unsafe {
            let raw = self.raw.as_mut();
            let out = raw.get(index);
            raw.copy(index + 1, index, self.length - index);
            out
        }
    }

    /// Reserves capacity for at least additional more elements to be inserted
    /// in the given `Soa<T>`. The collection may reserve more space to
    /// speculatively avoid frequent reallocations. After calling reserve,
    /// capacity will be greater than or equal to `self.len() + additional`. Does
    /// nothing if capacity is already sufficient.
    pub fn reserve(&mut self, additional: usize) {
        if additional == 0 {
            return;
        }
        let new_capacity = (self.length + additional)
            // Ensure exponential growth
            .max(self.capacity * 2)
            .max(Self::SMALL_CAPACITY);
        self.grow(new_capacity);
    }

    /// Reserves the minimum capacity for at least additional more elements to
    /// be inserted in the given `Soa<T>`. Unlike [`Soa::reserve`], this will not
    /// deliberately over-allocate to speculatively avoid frequent allocations.
    /// After calling `reserve_exact`, capacity will be greater than or equal to
    /// self.len() + additional. Does nothing if the capacity is already
    /// sufficient.
    pub fn reserve_exact(&mut self, additional: usize) {
        if additional == 0 {
            return;
        }
        let new_capacity = (additional + self.length).max(self.capacity);
        self.grow(new_capacity);
    }

    /// Shrinks the capacity of the container as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.shrink(self.length);
    }

    /// Shrinks the capacity of the vector with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length and the
    /// supplied value. If the current capacity is less than the lower limit,
    /// this is a no-op.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        let new_capacity = self.length.max(min_capacity);
        if new_capacity < self.capacity {
            self.shrink(new_capacity);
        }
    }

    /// Shortens the vector, keeping the first len elements and dropping the rest.
    ///
    /// If len is greater or equal to the vector’s current length, this has no
    /// effect. Note that this method has no effect on the allocated capacity of
    /// the vector.
    pub fn truncate(&mut self, len: usize) {
        while len < self.length {
            self.pop();
        }
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector. This
    /// does not preserve ordering, but is O(1). If you need to preserve the
    /// element order, use remove instead.
    ///
    /// # Panics
    ///
    /// Panics if index is out of bounds.
    pub fn swap_remove(&mut self, index: usize) -> T {
        unsafe {
            let raw = self.raw.as_mut();
            let out = unsafe { raw.get(index) };
            let last = unsafe { raw.get(self.length - 1) };
            raw.set(index, last);
            out
        }
    }

    /// Moves all the elements of other into self, leaving other empty.
    pub fn append(&mut self, other: &mut Self) {
        for i in 0..other.length {
            let element = unsafe { other.raw.as_mut().get(i) };
            self.push(element);
        }
        other.length = 0;
    }

    /// Returns an iterator over the elements.
    ///
    /// The iterator yields all items from start to end.
    pub fn iter(&self) -> Iter<T> {
        Iter {
            raw: self.raw,
            start: 0,
            end: self.length,
            _marker: PhantomData,
        }
    }

    /// Returns an iterator over the elements that allows modifying each value.
    ///
    /// The iterator yields all items from start to end.
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            raw: self.raw,
            start: 0,
            end: self.length,
            _marker: PhantomData,
        }
    }

    pub fn try_fold<F, B>(&self, init: B, mut f: F) -> B
    where
        F: FnMut(B, &T) -> ControlFlow<B, B>,
    {
        let mut acc = init;
        for i in 0..self.length {
            // SAFETY:
            // Okay to construct an element and take its reference, so long as
            // we don't run its destructor.
            let element = ManuallyDrop::new(unsafe { self.raw.as_mut().get(i) });
            let result = f(acc, &element);
            match result {
                ControlFlow::Continue(b) => acc = b,
                ControlFlow::Break(b) => return b,
            }
        }
        acc
    }

    pub fn try_fold_zip<F, B, O>(&self, other: &Soa<O>, init: B, mut f: F) -> B
    where
        O: Soapy,
        F: FnMut(B, &T, &O) -> ControlFlow<B, B>,
    {
        let mut acc = init;
        let len = self.length.min(other.length);
        for i in 0..len {
            // SAFETY:
            // Okay to construct an element and take its reference, so long as
            // we don't run its destructor.
            let a = ManuallyDrop::new(unsafe { self.raw.as_mut().get(i) });
            let b = ManuallyDrop::new(unsafe { other.raw.as_mut().get(i) });
            let result = f(acc, &a, &b);
            match result {
                ControlFlow::Continue(b) => acc = b,
                ControlFlow::Break(b) => return b,
            }
        }
        acc
    }

    /// Calls a closure on each element of the collection.
    pub fn for_each<F>(&self, mut f: F)
    where
        F: FnMut(&T),
    {
        self.try_fold((), |_, item| {
            f(item);
            ControlFlow::Continue(())
        })
    }

    /// Calls a closure on each element of the collection.
    pub fn for_each_zip<F, O>(&self, other: &Soa<O>, mut f: F)
    where
        O: Soapy,
        F: FnMut(&T, &O),
    {
        self.try_fold_zip(other, (), |_, a, b| {
            f(a, b);
            ControlFlow::Continue(())
        })
    }

    /// Clears the vector, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity of the
    /// vector.
    pub fn clear(&mut self) {
        while self.pop().is_some() {}
    }

    /// Returns a clone of the element at the given index.
    ///
    /// # Panics
    ///
    /// Panics if `index >= len`.
    pub fn nth_cloned(&self, index: usize) -> T
    where
        T: Clone,
    {
        if index >= self.length {
            panic!("index out of bounds");
        }
        let el = ManuallyDrop::new(unsafe { self.raw.as_mut().get(index) });
        el.deref().clone()
    }

    /// Returns a reference to the element at the given index.
    ///
    /// # Panics
    ///
    /// Panics if `index >= len`.
    pub fn nth(&self, index: usize) -> <T::SoaSlice as SoaSlice<T>>::Ref<'_> {
        if index >= self.length {
            panic!("index out of bounds");
        }
        unsafe { self.raw.as_mut().get_ref(index) }
    }

    /// Returns a reference to the element at the given index.
    ///
    /// # Panics
    ///
    /// Panics if `index >= len`.
    pub fn nth_mut(&mut self, index: usize) -> <T::SoaSlice as SoaSlice<T>>::RefMut<'_> {
        if index >= self.length {
            panic!("index out of bounds");
        }
        unsafe { self.raw.as_mut().get_mut(index) }
    }

    /// Swaps the position of two elements.
    ///
    /// # Panics
    ///
    /// Panics if `a` or `b` is out of bounds.
    pub fn swap(&mut self, a: usize, b: usize) {
        if a >= self.length || b >= self.length {
            panic!("index out of bounds");
        }

        unsafe {
            let raw = self.raw.as_mut();
            let tmp = raw.get(a);
            raw.copy(b, a, 1);
            raw.set(b, tmp);
        }
    }

    /// Grows the allocated capacity if `len == cap`.
    fn maybe_grow(&mut self) {
        if self.length < self.capacity {
            return;
        }
        let new_capacity = match self.capacity {
            0 => Self::SMALL_CAPACITY,
            old_cap => old_cap * 2,
        };
        self.grow(new_capacity);
    }

    // Shrinks the allocated capacity.
    fn shrink(&mut self, new_capacity: usize) {
        debug_assert!(new_capacity <= self.capacity);
        if self.capacity == 0 || new_capacity == self.capacity || size_of::<T>() == 0 {
            return;
        }

        if new_capacity == 0 {
            self.dealloc();
        } else {
            self.realloc_shrink(new_capacity);
        }
    }

    /// Grows the allocated capacity.
    fn grow(&mut self, new_capacity: usize) {
        debug_assert!(new_capacity > self.capacity);
        if size_of::<T>() == 0 {
            return;
        }

        if self.capacity == 0 {
            self.raw = Self::alloc(new_capacity);
            self.capacity = new_capacity;
        } else {
            self.realloc_grow(new_capacity);
        }
    }
}

impl<T> Drop for Soa<T>
where
    T: Soapy,
{
    fn drop(&mut self) {
        while self.pop().is_some() {}
        if size_of::<T>() > 0 && self.capacity > 0 {
            self.dealloc();
        }
    }
}

impl<T> IntoIterator for Soa<T>
where
    T: Soapy,
{
    type Item = T;

    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        // Make sure not to drop self and free the buffer
        let soa = ManuallyDrop::new(self);

        let len = soa.length;
        let cap = soa.capacity;
        let raw = soa.raw;

        IntoIter {
            start: 0,
            end: len,
            raw,
            cap,
        }
    }
}

impl<T> Clone for Soa<T>
where
    T: Soapy + Clone,
{
    fn clone(&self) -> Self {
        let mut out = Self::with_capacity(self.len());
        self.for_each(|el| {
            out.push(el.clone());
        });
        out
    }

    fn clone_from(&mut self, source: &Self) {
        self.clear();
        if self.capacity < source.length {
            self.reserve(source.length);
        }
        source.for_each(|el| {
            self.push(el.clone());
        });
    }
}

impl<T> Extend<T> for Soa<T>
where
    T: Soapy,
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            self.push(item);
        }
    }
}

impl<T> FromIterator<T> for Soa<T>
where
    T: Soapy,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let (hint_min, hint_max) = iter.size_hint();
        let cap = hint_max.unwrap_or(hint_min);
        let mut out = Self::with_capacity(cap);
        for item in iter {
            out.push(item);
        }
        out
    }
}

impl<T, const N: usize> From<[T; N]> for Soa<T>
where
    T: Soapy,
{
    /// Allocate a `Soa<T>` and move `value`'s items into it.
    fn from(value: [T; N]) -> Self {
        value.into_iter().collect()
    }
}

impl<T, const N: usize> From<&[T; N]> for Soa<T>
where
    T: Soapy + Clone,
{
    /// Allocate a `Soa<T>` and fill it by cloning `value`'s items.
    fn from(value: &[T; N]) -> Self {
        value.iter().cloned().collect()
    }
}

impl<T, const N: usize> From<&mut [T; N]> for Soa<T>
where
    T: Soapy + Clone,
{
    /// Allocate a `Soa<T>` and fill it by cloning `value`'s items.
    fn from(value: &mut [T; N]) -> Self {
        value.iter().cloned().collect()
    }
}

impl<T> From<&[T]> for Soa<T>
where
    T: Soapy + Clone,
{
    /// Allocate a `Soa<T>` and fill it by cloning `value`'s items.
    fn from(value: &[T]) -> Self {
        value.iter().cloned().collect()
    }
}

impl<T> From<&mut [T]> for Soa<T>
where
    T: Soapy + Clone,
{
    /// Allocate a `Soa<T>` and fill it by cloning `value`'s items.
    fn from(value: &mut [T]) -> Self {
        value.iter().cloned().collect()
    }
}

impl<T> PartialEq for Soa<T>
where
    T: Soapy + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.length != other.length {
            return false;
        }

        self.try_fold_zip(other, true, |_, a, b| {
            if a == b {
                ControlFlow::Continue(true)
            } else {
                ControlFlow::Break(false)
            }
        })
    }
}

impl<T> Eq for Soa<T> where T: Soapy + Eq {}

impl<T> fmt::Debug for Soa<T>
where
    T: Soapy + fmt::Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut list = f.debug_list();
        self.for_each(|item| {
            list.entry(&item);
        });
        list.finish()
    }
}

impl<T> PartialOrd for Soa<T>
where
    T: Soapy + PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let element_wise = self.try_fold_zip(other, Some(Ordering::Equal), |_, a, b| {
            match a.partial_cmp(b) {
                ord @ (None | Some(Ordering::Less | Ordering::Greater)) => ControlFlow::Break(ord),
                Some(Ordering::Equal) => ControlFlow::Continue(Some(Ordering::Equal)),
            }
        });
        match element_wise {
            ord @ (None | Some(Ordering::Less | Ordering::Greater)) => ord,
            Some(Ordering::Equal) => Some(self.length.cmp(&other.length)),
        }
    }
}

impl<T> Ord for Soa<T>
where
    T: Soapy + Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        let element_wise = self.try_fold_zip(other, Ordering::Equal, |_, a, b| match a.cmp(b) {
            ord @ (Ordering::Greater | Ordering::Less) => ControlFlow::Break(ord),
            Ordering::Equal => ControlFlow::Continue(Ordering::Equal),
        });
        match element_wise {
            ord @ (Ordering::Less | Ordering::Greater) => ord,
            Ordering::Equal => self.length.cmp(&other.length),
        }
    }
}

impl<T> Default for Soa<T>
where
    T: Soapy,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T> std::hash::Hash for Soa<T>
where
    T: Soapy + std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.length.hash(state);
        self.for_each(|item| item.hash(state));
    }
}
