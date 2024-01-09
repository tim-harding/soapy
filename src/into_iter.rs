use soapy_shared::{SoaSlice, Soapy};
use std::{alloc::dealloc, mem::size_of, ptr::NonNull};

pub struct IntoIter<T>
where
    T: Soapy,
{
    pub(crate) raw: NonNull<T::SoaSlice>,
    pub(crate) cap: usize,
    pub(crate) start: usize,
    pub(crate) end: usize,
}

impl<T> Iterator for IntoIter<T>
where
    T: Soapy,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start >= self.end {
            None
        } else {
            let out = unsafe { self.raw.as_mut().get(self.start) };
            self.start += 1;
            Some(out)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.end - self.start;
        (len, Some(len))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T>
where
    T: Soapy,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start >= self.end {
            None
        } else {
            self.end -= 1;
            Some(unsafe { self.raw.as_mut().get(self.end) })
        }
    }
}

impl<T> Drop for IntoIter<T>
where
    T: Soapy,
{
    fn drop(&mut self) {
        for _ in self.by_ref() {}
        if size_of::<T>() > 0 && self.cap > 0 {
            unsafe {
                let (layout, _) =
                    <T::SoaSlice as SoaSlice<T>>::layout_and_offsets(self.cap).unwrap();
                dealloc(self.raw.as_ptr() as *mut u8, layout);
            }
        }
    }
}
