use soapy_shared::{SoaSlice, Soapy};
use std::{marker::PhantomData, ptr::NonNull};

pub struct Iter<'a, T: 'a>
where
    T: Soapy,
{
    pub(crate) raw: NonNull<T::SoaSlice>,
    pub(crate) start: usize,
    pub(crate) end: usize,
    pub(crate) _marker: PhantomData<&'a T>,
}

impl<'a, T> Iterator for Iter<'a, T>
where
    T: Soapy,
{
    type Item = <<T as Soapy>::SoaSlice as SoaSlice<T>>::Ref<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start >= self.end {
            None
        } else {
            let out = unsafe { self.raw.as_mut().get_ref(self.start) };
            self.start += 1;
            Some(out)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.end - self.start;
        (len, Some(len))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T>
where
    T: Soapy,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start >= self.end {
            None
        } else {
            self.end -= 1;
            Some(unsafe { self.raw.as_mut().get_ref(self.end) })
        }
    }
}
