use soapy_shared::{RawSoa, Soapy};
use std::{
    cmp::Ordering,
    fmt::{self, Formatter},
    marker::PhantomData,
    mem::{size_of, ManuallyDrop},
    ops::{ControlFlow, Deref},
};

use crate::{IntoIter, Iter, IterMut};

pub struct Soa<T>
where
    T: Soapy,
{
    pub(crate) len: usize,
    pub(crate) cap: usize,
    pub(crate) raw: T::RawSoa,
}

unsafe impl<T> Send for Soa<T> where T: Send + Soapy {}
unsafe impl<T> Sync for Soa<T> where T: Sync + Soapy {}

impl<T> Soa<T>
where
    T: Soapy,
{
    const SMALL_CAPACITY: usize = 4;

    /// Constructs a new, empty `Soa<T>`.
    ///
    /// The container will not allocate until elements are pushed onto it.
    pub fn new() -> Self {
        Self {
            len: 0,
            cap: if size_of::<T>() == 0 { usize::MAX } else { 0 },
            raw: T::RawSoa::dangling(),
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
                        len: 0,
                        cap: usize::MAX,
                        raw: T::RawSoa::dangling(),
                    }
                } else {
                    Self {
                        len: 0,
                        cap: capacity,
                        raw: unsafe { T::RawSoa::alloc(capacity) },
                    }
                }
            }
        }
    }

    /// Returns the number of elements in the vector, also referred to as its
    /// length.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the container contains no elements.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the total number of elements the container can hold without
    /// reallocating.
    pub fn capacity(&self) -> usize {
        self.cap
    }

    /// Appends an element to the back of a collection.
    pub fn push(&mut self, element: T) {
        self.maybe_grow();
        unsafe {
            self.raw.set(self.len, element);
        }
        self.len += 1;
    }

    /// Removes the last element from a vector and returns it, or [`None`] if it
    /// is empty.
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            Some(unsafe { self.raw.get(self.len) })
        }
    }

    /// Inserts an element at position `index`, shifting all elements after it
    /// to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`
    pub fn insert(&mut self, index: usize, element: T) {
        assert!(index <= self.len, "index out of bounds");
        self.maybe_grow();
        unsafe {
            self.raw.copy(index, index + 1, self.len - index);
            self.raw.set(index, element);
        }
        self.len += 1;
    }

    /// Removes and returns the element at position index within the vector,
    /// shifting all elements after it to the left.
    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len, "index out of bounds");
        self.len -= 1;
        let out = unsafe { self.raw.get(index) };
        unsafe {
            self.raw.copy(index + 1, index, self.len - index);
        }
        out
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
        let new_cap = (self.len + additional)
            // Ensure exponential growth
            .max(self.cap * 2)
            .max(Self::SMALL_CAPACITY);
        self.grow(new_cap);
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
        let new_cap = (additional + self.len).max(self.cap);
        self.grow(new_cap);
    }

    /// Shrinks the capacity of the container as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.shrink(self.len);
    }

    /// Shrinks the capacity of the vector with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length and the
    /// supplied value. If the current capacity is less than the lower limit,
    /// this is a no-op.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        let new_cap = self.len.max(min_capacity);
        if new_cap < self.cap {
            self.shrink(new_cap);
        }
    }

    /// Shortens the vector, keeping the first len elements and dropping the rest.
    ///
    /// If len is greater or equal to the vector’s current length, this has no
    /// effect. Note that this method has no effect on the allocated capacity of
    /// the vector.
    pub fn truncate(&mut self, len: usize) {
        while len < self.len {
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
        let out = unsafe { self.raw.get(index) };
        let last = unsafe { self.raw.get(self.len - 1) };
        unsafe {
            self.raw.set(index, last);
        }
        out
    }

    /// Moves all the elements of other into self, leaving other empty.
    pub fn append(&mut self, other: &mut Self) {
        for i in 0..other.len {
            let element = unsafe { other.raw.get(i) };
            self.push(element);
        }
        other.len = 0;
    }

    /// Returns an iterator over the elements.
    ///
    /// The iterator yields all items from start to end.
    pub fn iter(&self) -> Iter<T> {
        Iter {
            raw: self.raw,
            start: 0,
            end: self.len,
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
            end: self.len,
            _marker: PhantomData,
        }
    }

    pub fn try_fold<F, B>(&self, init: B, mut f: F) -> B
    where
        F: FnMut(B, &T) -> ControlFlow<B, B>,
    {
        let mut acc = init;
        for i in 0..self.len {
            // SAFETY:
            // Okay to construct an element and take its reference, so long as
            // we don't run its destructor.
            let element = ManuallyDrop::new(unsafe { self.raw.get(i) });
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
        let len = self.len.min(other.len);
        for i in 0..len {
            // SAFETY:
            // Okay to construct an element and take its reference, so long as
            // we don't run its destructor.
            let a = ManuallyDrop::new(unsafe { self.raw.get(i) });
            let b = ManuallyDrop::new(unsafe { other.raw.get(i) });
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
        if index >= self.len {
            panic!("index out of bounds");
        }
        let el = ManuallyDrop::new(unsafe { self.raw.get(index) });
        el.deref().clone()
    }

    /// Returns a reference to the element at the given index.
    ///
    /// # Panics
    ///
    /// Panics if `index >= len`.
    pub fn nth(&self, index: usize) -> <T::RawSoa as RawSoa<T>>::Ref<'_> {
        if index >= self.len {
            panic!("index out of bounds");
        }
        unsafe { self.raw.get_ref(index) }
    }

    /// Returns a reference to the element at the given index.
    ///
    /// # Panics
    ///
    /// Panics if `index >= len`.
    pub fn nth_mut(&mut self, index: usize) -> <T::RawSoa as RawSoa<T>>::RefMut<'_> {
        if index >= self.len {
            panic!("index out of bounds");
        }
        unsafe { self.raw.get_mut(index) }
    }

    /// Swaps the position of two elements.
    ///
    /// # Panics
    ///
    /// Panics if `a` or `b` is out of bounds.
    pub fn swap(&mut self, a: usize, b: usize) {
        if a >= self.len || b >= self.len {
            panic!("index out of bounds");
        }

        unsafe {
            let tmp = self.raw.get(a);
            self.raw.copy(b, a, 1);
            self.raw.set(b, tmp);
        }
    }

    /// Grows the allocated capacity if `len == cap`.
    fn maybe_grow(&mut self) {
        if self.len < self.cap {
            return;
        }
        let new_cap = match self.cap {
            0 => Self::SMALL_CAPACITY,
            old_cap => old_cap * 2,
        };
        self.grow(new_cap);
    }

    // Shrinks the allocated capacity.
    fn shrink(&mut self, new_cap: usize) {
        debug_assert!(new_cap <= self.cap);
        if self.cap == 0 || new_cap == self.cap || size_of::<T>() == 0 {
            return;
        }

        if new_cap == 0 {
            debug_assert!(self.cap > 0);
            unsafe {
                self.raw.dealloc(self.cap);
            }
            self.raw = T::RawSoa::dangling();
        } else {
            debug_assert!(new_cap < self.cap);
            debug_assert!(self.len <= new_cap);
            unsafe {
                self.raw.realloc_shrink(self.cap, new_cap, self.len);
            }
        }

        self.cap = new_cap;
    }

    /// Grows the allocated capacity.
    fn grow(&mut self, new_cap: usize) {
        debug_assert!(size_of::<T>() > 0);
        debug_assert!(new_cap > self.cap);

        if self.cap == 0 {
            debug_assert!(new_cap > 0);
            self.raw = unsafe { T::RawSoa::alloc(new_cap) };
        } else {
            debug_assert!(self.len <= self.cap);
            unsafe {
                self.raw.realloc_grow(self.cap, new_cap, self.len);
            }
        }

        self.cap = new_cap;
    }
}

impl<T> Drop for Soa<T>
where
    T: Soapy,
{
    fn drop(&mut self) {
        while self.pop().is_some() {}
        if size_of::<T>() > 0 && self.cap > 0 {
            unsafe {
                self.raw.dealloc(self.cap);
            }
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

        let len = soa.len;
        let cap = soa.cap;
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
        if self.cap < source.len {
            self.reserve(source.len);
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
        if self.len != other.len {
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
            Some(Ordering::Equal) => Some(self.len.cmp(&other.len)),
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
            Ordering::Equal => self.len.cmp(&other.len),
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
        self.len.hash(state);
        self.for_each(|item| item.hash(state));
    }
}
