//! Soapy makes it simple to work with structure-of-arrays memory layout. What `Vec<T>`
//! is to array-of-structures (AoS), `Soa<T>` is to structure-of-arrays (SoA).
//!
//! # What is SoA?
//!
//! The following types illustrate the difference between AoS and Soa:
//! ```text
//! [(u8,   u64)] // AoS
//! ([u8], [u64]) // Soa
//! ```
//!
//! Whereas AoS stores all the fields of a type in each element of the array,
//! SoA splits each field into its own array. This has several benefits:
//!
//! - There is no padding required between instances of the same type. In the
//! above example, each AoS element requires 128 bits to satisfy memory
//! alignment requirements, whereas each SoA element only takes 72. This can
//! mean better cache locality and lower memory usage.
//! - SoA can be more amenable to vectorization. With SoA, multiple values can
//! be direcly loaded into SIMD registers in bulk, as opposed to shuffling
//! struct fields into and out of different SIMD registers.
//!
//! SoA is a popular technique in data-oriented design. Andrew Kelley gives a
//! wonderful [talk](https://vimeo.com/649009599) describing how SoA and other
//! data-oriented design patterns earned him a 39% reduction in wall clock time
//! in the Zig compiler.
//!
//! Note that SoA does not offer performance wins in all cases. SoA is most
//! appropriate when either
//! - Sequential access is the common access pattern
//! - You are frequently accessing or modifying only a subset of the fields
//!
//! As always, it is best to profile both for your use case.
//!
//! # Derive
//!
//! Soapy provides the [`Soapy`] derive macro to generate SoA compatibility for
//! structs automatically. When deriving Soapy, several new structs are
//! created. Because of the way SoA data is stored, iterators and getters often
//! yield these types instead of the original struct. If each field of some
//! struct `Example` has type `F`, our new structs have the same fields but
//! different types:
//!
//! | Struct             | Field type | Use                                   |
//! |--------------------|------------|---------------------------------------|
//! | `ExampleRawSoa`    | `*mut F`   | Low-level, unsafe interface for `Soa` |
//! | `ExampleRef`       | `&F`       | `.iter()`, `nth()`, `.get()`          |
//! | `ExampleRefMut`    | `&mut F`   | `.iter_mut()`, `nth_mut`, `get_mut()` |
//! | `ExampleSlices`    | `&[F]`     | `.slices()`, `.get()`                 |
//! | `ExampleSlicesMut` | `&mut [F]` | `.slices_mut()`, `.get_mut()`         |
//!
//! These types are included as associated types on the [`Soapy`] trait as well.
//! Generally, you won't need to think about these them as [`Soa`] picks them up
//! automatically. However, since they inherit the visibility of the derived
//! struct, you should consider whether to include them in the `pub` items of
//! your module.

mod into_iter;
mod iter;
mod iter_mut;
mod soa;

pub use into_iter::IntoIter;
pub use iter::Iter;
pub use iter_mut::IterMut;
pub use soa::Soa;
pub use soapy_derive::Soapy;
pub use soapy_shared::Soapy;

#[cfg(test)]
mod tests {
    use crate::{Soa, Soapy};

    #[derive(Soapy, Debug, Clone, Copy, PartialEq, Eq, Hash)]
    struct El {
        foo: u64,
        bar: u8,
        baz: [u32; 2],
    }

    const A: El = El {
        foo: 0,
        bar: 1,
        baz: [2, 3],
    };

    const B: El = El {
        foo: 4,
        bar: 5,
        baz: [6, 7],
    };

    const C: El = El {
        foo: 8,
        bar: 9,
        baz: [10, 11],
    };

    const D: El = El {
        foo: 12,
        bar: 13,
        baz: [14, 15],
    };

    const E: El = El {
        foo: 16,
        bar: 17,
        baz: [18, 19],
    };

    const ABCDE: [El; 5] = [A, B, C, D, E];

    #[derive(Soapy, Debug, Clone, Copy, PartialEq, Eq, Default)]
    struct Unit;

    #[derive(Soapy, Debug, Clone, Copy, PartialEq, Eq, Default)]
    struct Empty {}

    #[derive(Soapy, Debug, Clone, Copy, PartialEq, Eq, Default)]
    struct EmptyTuple();

    #[derive(Soapy, Debug, Clone, Copy, PartialEq, Eq, Default)]
    struct ZstFields {
        a: Unit,
        b: (),
    }

    #[derive(Soapy, Debug, Clone, Copy, PartialEq, Eq, Default)]
    struct Tuple(u8, u16, u32);

    #[test]
    pub fn tuple() {
        let mut soa = Soa::new();
        let elements = [Tuple(0, 1, 2), Tuple(3, 4, 5), Tuple(6, 7, 8)];
        for element in elements {
            soa.push(element);
        }
        assert!(elements.into_iter().eq(soa.into_iter()));
    }

    #[test]
    pub fn zst_fields() {
        let mut soa = Soa::new();
        for _ in 0..5 {
            soa.push(ZstFields::default());
        }
        for _ in 0..5 {
            assert_eq!(soa.pop(), Some(ZstFields::default()));
        }
        assert_eq!(soa.pop(), None);
    }

    #[test]
    pub fn empty_tuple() {
        let mut soa = Soa::new();
        for _ in 0..5 {
            soa.push(EmptyTuple());
        }
        for _ in 0..5 {
            assert_eq!(soa.pop(), Some(EmptyTuple()));
        }
        assert_eq!(soa.pop(), None);
    }

    #[test]
    pub fn empty_struct() {
        let mut soa = Soa::new();
        for _ in 0..5 {
            soa.push(Empty {});
        }
        for _ in 0..5 {
            assert_eq!(soa.pop(), Some(Empty {}));
        }
        assert_eq!(soa.pop(), None);
    }

    #[test]
    pub fn unit_struct() {
        let mut soa = Soa::new();
        for _ in 0..5 {
            soa.push(Unit);
        }
        for _ in 0..5 {
            assert_eq!(soa.pop(), Some(Unit));
        }
        assert_eq!(soa.pop(), None);
    }

    #[test]
    pub fn push_and_pop() {
        let mut soa = Soa::new();
        for element in ABCDE.into_iter() {
            soa.push(element);
        }
        for element in ABCDE.into_iter().rev() {
            assert_eq!(Some(element), soa.pop());
        }
    }

    #[test]
    pub fn insert() {
        test_insert(0, [B, A, A, A]);
        test_insert(1, [A, B, A, A]);
        test_insert(2, [A, A, B, A]);
        test_insert(3, [A, A, A, B]);
    }

    fn test_insert(index: usize, expected: [El; 4]) {
        let mut soa = Soa::new();
        for element in [A, A, A].into_iter() {
            soa.push(element);
        }
        soa.insert(index, B);
        assert!(soa.into_iter().eq(expected.into_iter()));
    }

    #[test]
    pub fn remove() {
        test_remove(0, A, [B, C, D, E]);
        test_remove(1, B, [A, C, D, E]);
        test_remove(2, C, [A, B, D, E]);
        test_remove(3, D, [A, B, C, E]);
        test_remove(4, E, [A, B, C, D]);
    }

    fn test_remove(index: usize, expected_return: El, expected_contents: [El; 4]) {
        let mut soa = Soa::new();
        for element in ABCDE.into_iter() {
            soa.push(element);
        }
        assert_eq!(expected_return, soa.remove(index));
        assert!(soa.into_iter().eq(expected_contents.into_iter()));
    }

    #[test]
    pub fn with_capacity() {
        let mut soa = Soa::with_capacity(5);
        assert_eq!(soa.capacity(), 5);
        assert_eq!(soa.len(), 0);
        for element in ABCDE.into_iter() {
            soa.push(element);
        }
        assert_eq!(soa.capacity(), 5);
        assert_eq!(soa.len(), 5);
    }

    #[test]
    pub fn from_iter() {
        let soa: Soa<_> = ABCDE.into_iter().collect();
        assert!(soa.into_iter().eq(ABCDE.into_iter()));
    }

    #[test]
    pub fn iter() {
        let soa: Soa<_> = ABCDE.into();
        for (borrowed, owned) in soa.iter().zip(ABCDE.into_iter()) {
            assert_eq!(borrowed.foo, &owned.foo);
            assert_eq!(borrowed.bar, &owned.bar);
            assert_eq!(borrowed.baz, &owned.baz);
        }
    }

    #[test]
    pub fn iter_mut() {
        let mut soa: Soa<_> = ABCDE.into();
        for el in soa.iter_mut() {
            *el.foo += 1;
            *el.bar += 2;
            let [a, b] = *el.baz;
            *el.baz = [a + 3, b + 4];
        }
        for (borrowed, owned) in soa.iter().zip(ABCDE.into_iter()) {
            assert_eq!(borrowed.foo, &(owned.foo + 1));
            assert_eq!(borrowed.bar, &(owned.bar + 2));
            assert_eq!(borrowed.baz, &[owned.baz[0] + 3, owned.baz[1] + 4]);
        }
    }

    #[test]
    pub fn from_impls() {
        let expected: Soa<_> = ABCDE.into_iter().collect();
        let array: [El; 5] = ABCDE;
        let array_ref: &[El; 5] = &ABCDE;
        let mut tmp = ABCDE;
        let array_ref_mut: &mut [El; 5] = &mut tmp;
        let slice: &[El] = ABCDE.as_slice();
        let mut tmp = ABCDE;
        let slice_mut: &mut [El] = tmp.as_mut_slice();
        assert_eq!(expected, array.into());
        assert_eq!(expected, array_ref.into());
        assert_eq!(expected, array_ref_mut.into());
        assert_eq!(expected, slice.into());
        assert_eq!(expected, slice_mut.into());
    }

    #[test]
    pub fn extend() {
        let mut soa: Soa<_> = [A, B].into();
        soa.extend([C, D]);
        assert!(soa.into_iter().eq([A, B, C, D].into_iter()));
    }

    #[test]
    pub fn clone() {
        let expected: Soa<_> = ABCDE.into();
        let actual = expected.clone();
        assert_eq!(expected, actual);
    }

    #[test]
    pub fn clone_from() {
        let mut dst: Soa<_> = ABCDE.into();
        let src: Soa<_> = [A, A, A].into();
        dst.clone_from(&src);
        assert_eq!(dst, src);
    }

    #[test]
    pub fn partial_ordering_and_equality() {
        #[derive(Soapy, Debug, PartialEq, PartialOrd, Clone, Copy)]
        struct F(f32);

        let cases = [
            (&[][..], &[][..]),
            (&[F(1.), F(2.), F(3.)][..], &[F(1.), F(2.), F(3.)][..]),
            (&[F(1.), F(2.), F(2.)][..], &[F(1.), F(2.), F(3.)][..]),
            (&[F(1.), F(2.), F(4.)][..], &[F(1.), F(2.), F(3.)][..]),
            (
                &[F(1.), F(2.), F(3.)][..],
                &[F(1.), F(2.), F(3.), F(0.)][..],
            ),
            (
                &[F(1.), F(2.), F(3.), F(0.)][..],
                &[F(1.), F(2.), F(3.)][..],
            ),
            (&[F(1.)][..], &[F(f32::NAN)][..]),
        ];

        for case in cases {
            let (l, r) = case;
            let expected_cmp = l.partial_cmp(r);
            let expected_eq = l == r;
            let l: Soa<_> = l.into();
            let r: Soa<_> = r.into();
            assert_eq!(l.partial_cmp(&r), expected_cmp);
            assert_eq!(l == r, expected_eq);
        }
    }

    #[test]
    pub fn ordering() {
        #[derive(Soapy, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
        struct F(u8);

        let cases = [
            (&[][..], &[][..]),
            (&[F(1), F(2), F(3)][..], &[F(1), F(2), F(3)][..]),
            (&[F(1), F(2), F(2)][..], &[F(1), F(2), F(3)][..]),
            (&[F(1), F(2), F(4)][..], &[F(1), F(2), F(3)][..]),
            (&[F(1), F(2), F(3)][..], &[F(1), F(2), F(3), F(0)][..]),
            (&[F(1), F(2), F(3), F(0)][..], &[F(1), F(2), F(3)][..]),
        ];

        for case in cases {
            let (l, r) = case;
            let expected = l.cmp(r);
            let l: Soa<_> = l.into();
            let r: Soa<_> = r.into();
            let actual = l.cmp(&r);
            assert_eq!(actual, expected);
        }
    }

    #[test]
    pub fn debug() {
        let slice = format!("{:?}", ABCDE);
        let soa = format!("{:?}", Soa::from(ABCDE));
        assert_eq!(slice, soa);
    }

    #[test]
    pub fn hashing() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut expected = DefaultHasher::new();
        ABCDE.hash(&mut expected);

        let mut actual = DefaultHasher::new();
        let soa: Soa<_> = ABCDE.into();
        soa.hash(&mut actual);

        assert_eq!(actual.finish(), expected.finish());
    }

    #[test]
    pub fn swap() {
        let mut soa: Soa<_> = [A, B, C].into();
        soa.swap(0, 2);
        assert!([C, B, A].into_iter().eq(soa.into_iter()));
    }
}
