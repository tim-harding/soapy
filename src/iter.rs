use crate::{Ref, Slice, SliceRef, SoaRaw, Soapy};
use std::{iter::FusedIterator, marker::PhantomData};

/// Immutable [`Soa`] iterator.
///
/// This struct is created by the [`iter`] method.
///
/// [`Soa`]: crate::Soa
/// [`iter`]: crate::Soa::iter
pub struct Iter<'a, T>
where
    T: 'a + Soapy,
{
    pub(crate) raw: T::Raw,
    pub(crate) len: usize,
    pub(crate) _marker: PhantomData<&'a T>,
}

impl<'a, T> Iter<'a, T>
where
    T: 'a + Soapy,
{
    pub fn as_slice(&self) -> SliceRef<'a, T> {
        SliceRef(
            unsafe { Slice::from_raw_parts(self.raw, self.len) },
            PhantomData,
        )
    }
}

impl<'a, T> Iterator for Iter<'a, T>
where
    T: 'a + Soapy,
{
    type Item = Ref<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            let out = Some(Ref(unsafe { self.raw.get_ref() }));
            self.raw = unsafe { self.raw.offset(1) };
            out
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.len
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if n >= self.len {
            self.raw = unsafe { self.raw.offset(self.len) };
            self.len = 0;
            None
        } else {
            self.len -= n;
            self.raw = unsafe { self.raw.offset(n) };
            Some(Ref(unsafe { self.raw.get_ref() }))
        }
    }

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        if self.len == 0 {
            None
        } else {
            Some(Ref(unsafe { self.raw.offset(self.len - 1).get_ref() }))
        }
    }

    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let Self { raw, len, _marker } = self;
        if len == 0 {
            return init;
        }
        let mut acc = init;
        let mut i = 0;
        loop {
            acc = f(acc, Ref(unsafe { raw.offset(i).get_ref() }));
            i += 1;
            if i == len {
                break;
            }
        }
        acc
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T>
where
    T: 'a + Soapy,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            Some(Ref(unsafe { self.raw.offset(self.len).get_ref() }))
        }
    }
}

impl<'a, T> FusedIterator for Iter<'a, T> where T: 'a + Soapy {}
impl<'a, T> ExactSizeIterator for Iter<'a, T> where T: 'a + Soapy {}
