use std::{
    array::IntoIter,
    ops::{Add, Deref, DerefMut, Mul},
    slice::Iter,
};

use criterion::{criterion_group, criterion_main, Criterion};
use rand::{rngs::StdRng, RngCore, SeedableRng};
use soapy::{SliceRef, Soa, Soapy};

struct Rng(StdRng);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(StdRng::seed_from_u64(seed))
    }

    fn next_f32(&mut self) -> f32 {
        f32::from_ne_bytes(self.0.next_u32().to_ne_bytes())
    }
}

#[derive(Soapy, Debug, Clone, Copy, PartialEq, PartialOrd)]
struct Vec4(
    #[align(64)] f32,
    #[align(64)] f32,
    #[align(64)] f32,
    #[align(64)] f32,
);

impl Vec4 {
    fn new_rng(rng: &mut Rng) -> Self {
        Self(
            rng.next_f32(),
            rng.next_f32(),
            rng.next_f32(),
            rng.next_f32(),
        )
    }
}

fn make_vec4_list<T>(rng: &mut Rng, count: usize) -> T
where
    T: FromIterator<Vec4>,
{
    std::iter::repeat_with(|| Vec4::new_rng(rng))
        .take(count)
        .collect()
}

fn sum_dots_vec(a: &[Vec4], b: &[Vec4]) -> f32 {
    a.iter()
        .zip(b.iter())
        .map(|(a, b)| a.0 * b.0 + a.1 * b.1 + a.2 * b.2 + a.3 * b.3)
        .sum()
}

fn sum_dots_soa(a: SliceRef<Vec4>, b: SliceRef<Vec4>) -> f32 {
    a.iter()
        .zip(b.iter())
        .map(|(a, b)| a.0 * b.0 + a.1 * b.1 + a.2 * b.2 + a.3 * b.3)
        .sum()
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
struct Vec4Arrays<const N: usize>([f32; N], [f32; N], [f32; N], [f32; N]);

impl<const N: usize> Vec4Arrays<N> {
    fn new_rng(rng: &mut Rng) -> Self {
        let mut out = Self([0.0; N], [0.0; N], [0.0; N], [0.0; N]);
        for i in 0..N {
            out.0[i] = rng.next_f32();
            out.1[i] = rng.next_f32();
            out.2[i] = rng.next_f32();
            out.3[i] = rng.next_f32();
        }
        out
    }

    fn iter(&self) -> impl Iterator<Item = (&f32, &f32, &f32, &f32)> {
        self.0
            .iter()
            .zip(self.1.iter())
            .zip(self.2.iter())
            .zip(self.3.iter())
            .map(|(((a0, a1), a2), a3)| (a0, a1, a2, a3))
    }
}

fn sum_dots_arrays<const N: usize>(a: &Vec4Arrays<N>, b: &Vec4Arrays<N>) -> f32 {
    a.iter()
        .zip(b.iter())
        .map(|(a, b)| a.0 * b.0 + a.1 * b.1 + a.2 * b.2 + a.3 * b.3)
        .sum()
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
#[repr(align(64))]
struct AlignedArray<const N: usize>([f32; N]);

impl<const N: usize> AlignedArray<N> {
    fn new_rng(rng: &mut Rng) -> Self {
        let mut out = [0.0; N];
        for el in out.iter_mut() {
            *el = rng.next_f32();
        }
        Self(out)
    }
}

impl<const N: usize> Deref for AlignedArray<N> {
    type Target = [f32; N];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const N: usize> DerefMut for AlignedArray<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
struct Vec4ArraysAligned<const N: usize>(
    AlignedArray<N>,
    AlignedArray<N>,
    AlignedArray<N>,
    AlignedArray<N>,
);

impl<const N: usize> Vec4ArraysAligned<N> {
    fn new_rng(rng: &mut Rng) -> Self {
        Self(
            AlignedArray::new_rng(rng),
            AlignedArray::new_rng(rng),
            AlignedArray::new_rng(rng),
            AlignedArray::new_rng(rng),
        )
    }

    fn iter(&self) -> impl Iterator<Item = (&f32, &f32, &f32, &f32)> {
        self.0
            .iter()
            .zip(self.1.iter())
            .zip(self.2.iter())
            .zip(self.3.iter())
            .map(|(((a, b), c), d)| (a, b, c, d))
    }
}

fn sum_dots_arrays_aligned<const N: usize>(
    a: &Vec4ArraysAligned<N>,
    b: &Vec4ArraysAligned<N>,
) -> f32 {
    a.iter()
        .zip(b.iter())
        .map(|(a, b)| a.0 * b.0 + a.1 * b.1 + a.2 * b.2 + a.3 * b.3)
        .sum()
}

#[repr(align(32))]
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
struct F32Group([f32; 8]);

impl Mul for F32Group {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self([
            self.0[0] * rhs.0[0],
            self.0[1] * rhs.0[1],
            self.0[2] * rhs.0[2],
            self.0[3] * rhs.0[3],
            self.0[4] * rhs.0[4],
            self.0[5] * rhs.0[5],
            self.0[6] * rhs.0[6],
            self.0[7] * rhs.0[7],
        ])
    }
}

impl Mul for &F32Group {
    type Output = F32Group;

    fn mul(self, rhs: Self) -> Self::Output {
        *self * *rhs
    }
}

impl Add for F32Group {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
            self.0[3] + rhs.0[3],
            self.0[4] + rhs.0[4],
            self.0[5] + rhs.0[5],
            self.0[6] + rhs.0[6],
            self.0[7] + rhs.0[7],
        ])
    }
}

impl Add for &F32Group {
    type Output = F32Group;

    fn add(self, rhs: Self) -> Self::Output {
        *self + *rhs
    }
}

impl IntoIterator for F32Group {
    type Item = f32;

    type IntoIter = IntoIter<f32, 8>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a F32Group {
    type Item = &'a f32;

    type IntoIter = Iter<'a, f32>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl F32Group {
    const ZERO: Self = Self([0.0; 8]);

    fn sum(self) -> f32 {
        self.0.into_iter().sum()
    }

    fn iter(&self) -> Iter<'_, f32> {
        self.0.iter()
    }

    fn new_rng(rng: &mut Rng) -> Self {
        Self([
            rng.next_f32(),
            rng.next_f32(),
            rng.next_f32(),
            rng.next_f32(),
            rng.next_f32(),
            rng.next_f32(),
            rng.next_f32(),
            rng.next_f32(),
        ])
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
struct Vec4ArraysGrouped<const N: usize>(
    [F32Group; N],
    [F32Group; N],
    [F32Group; N],
    [F32Group; N],
);

impl<const N: usize> Vec4ArraysGrouped<N> {
    fn new_rng(rng: &mut Rng) -> Self {
        let mut out = Self(
            [F32Group::ZERO; N],
            [F32Group::ZERO; N],
            [F32Group::ZERO; N],
            [F32Group::ZERO; N],
        );
        for i in 0..N {
            out.0[i] = F32Group::new_rng(rng);
            out.1[i] = F32Group::new_rng(rng);
            out.2[i] = F32Group::new_rng(rng);
            out.3[i] = F32Group::new_rng(rng);
        }
        out
    }

    fn iter(&self) -> impl Iterator<Item = (&F32Group, &F32Group, &F32Group, &F32Group)> {
        self.0
            .iter()
            .zip(self.1.iter())
            .zip(self.2.iter())
            .zip(self.3.iter())
            .map(|(((a, b), c), d)| (a, b, c, d))
    }
}

fn sum_dots_grouped<const N: usize>(a: &Vec4ArraysGrouped<N>, b: &Vec4ArraysGrouped<N>) -> f32 {
    a.iter()
        .zip(b.iter())
        .map(|(a, b)| (a.0 * b.0 + a.1 * b.1 + a.2 * b.2 + a.3 * b.3).sum())
        .sum()
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut rng = Rng::new(42);

    let array1 = <Vec4ArraysGrouped<{ 1 << 13 }>>::new_rng(&mut rng);
    let array2 = <Vec4ArraysGrouped<{ 1 << 13 }>>::new_rng(&mut rng);
    c.bench_function("grouped-array", |b| {
        b.iter(|| sum_dots_grouped(&array1, &array2))
    });

    let array1 = <Vec4Arrays<{ 1 << 16 }>>::new_rng(&mut rng);
    let array2 = <Vec4Arrays<{ 1 << 16 }>>::new_rng(&mut rng);
    c.bench_function("array", |b| b.iter(|| sum_dots_arrays(&array1, &array2)));

    let array1 = <Vec4ArraysAligned<{ 1 << 16 }>>::new_rng(&mut rng);
    let array2 = <Vec4ArraysAligned<{ 1 << 16 }>>::new_rng(&mut rng);
    c.bench_function("aligned-array", |b| {
        b.iter(|| sum_dots_arrays_aligned(&array1, &array2))
    });

    let soa1: Soa<_> = make_vec4_list(&mut rng, 1 << 16);
    let soa2: Soa<_> = make_vec4_list(&mut rng, 1 << 16);
    c.bench_function("soa", |b| {
        b.iter(|| sum_dots_soa(soa1.as_slice(), soa2.as_slice()))
    });

    let vec1: Vec<_> = make_vec4_list(&mut rng, 1 << 16);
    let vec2: Vec<_> = make_vec4_list(&mut rng, 1 << 16);
    c.bench_function("vec", |b| {
        b.iter(|| sum_dots_vec(vec1.as_slice(), vec2.as_slice()))
    });

    c.bench_function("batched-soa", |b| {
        b.iter(|| {
            soa1.f0()
                .chunks_exact(8)
                .zip(soa1.f1().chunks_exact(8))
                .zip(soa1.f2().chunks_exact(8))
                .zip(soa1.f3().chunks_exact(8))
                .zip(soa2.f0().chunks_exact(8))
                .zip(soa2.f1().chunks_exact(8))
                .zip(soa2.f2().chunks_exact(8))
                .zip(soa2.f3().chunks_exact(8))
                .fold(
                    (0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0),
                    |acc, (((((((a0, a1), a2), a3), b0), b1), b2), b3)| {
                        (
                            acc.0 + a0[0] * b0[0] + a1[0] * b1[0] + a2[0] * b2[0] + a3[0] * b3[0],
                            acc.1 + a0[1] * b0[1] + a1[1] * b1[1] + a2[1] * b2[1] + a3[1] * b3[1],
                            acc.2 + a0[2] * b0[2] + a1[2] * b1[2] + a2[2] * b2[2] + a3[2] * b3[2],
                            acc.3 + a0[3] * b0[3] + a1[3] * b1[3] + a2[3] * b2[3] + a3[3] * b3[3],
                            acc.4 + a0[4] * b0[4] + a1[4] * b1[4] + a2[4] * b2[4] + a3[4] * b3[4],
                            acc.5 + a0[5] * b0[5] + a1[5] * b1[5] + a2[5] * b2[5] + a3[5] * b3[5],
                            acc.6 + a0[6] * b0[6] + a1[6] * b1[6] + a2[6] * b2[6] + a3[6] * b3[6],
                            acc.7 + a0[7] * b0[7] + a1[7] * b1[7] + a2[7] * b2[7] + a3[7] * b3[7],
                        )
                    },
                )
        })
    });

    c.bench_function("chunked-soa", |b| {
        b.iter(|| {
            soa1.chunks_exact(8).zip(soa2.chunks_exact(8)).fold(
                (0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0),
                |acc, (a, b)| {
                    (
                        acc.0
                            + a.idx(0).0 * b.idx(0).0
                            + a.idx(0).1 * b.idx(0).1
                            + a.idx(0).2 * b.idx(0).2
                            + a.idx(0).3 * b.idx(0).3,
                        acc.1
                            + a.idx(1).0 * b.idx(1).0
                            + a.idx(1).1 * b.idx(1).1
                            + a.idx(1).2 * b.idx(1).2
                            + a.idx(1).3 * b.idx(1).3,
                        acc.2
                            + a.idx(2).0 * b.idx(2).0
                            + a.idx(2).1 * b.idx(2).1
                            + a.idx(2).2 * b.idx(2).2
                            + a.idx(2).3 * b.idx(2).3,
                        acc.3
                            + a.idx(3).0 * b.idx(3).0
                            + a.idx(3).1 * b.idx(3).1
                            + a.idx(3).2 * b.idx(3).2
                            + a.idx(3).3 * b.idx(3).3,
                        acc.4
                            + a.idx(4).0 * b.idx(4).0
                            + a.idx(4).1 * b.idx(4).1
                            + a.idx(4).2 * b.idx(4).2
                            + a.idx(4).3 * b.idx(4).3,
                        acc.5
                            + a.idx(5).0 * b.idx(5).0
                            + a.idx(5).1 * b.idx(5).1
                            + a.idx(5).2 * b.idx(5).2
                            + a.idx(5).3 * b.idx(5).3,
                        acc.6
                            + a.idx(6).0 * b.idx(6).0
                            + a.idx(6).1 * b.idx(6).1
                            + a.idx(6).2 * b.idx(6).2
                            + a.idx(6).3 * b.idx(6).3,
                        acc.7
                            + a.idx(7).0 * b.idx(7).0
                            + a.idx(7).1 * b.idx(7).1
                            + a.idx(7).2 * b.idx(7).2
                            + a.idx(7).3 * b.idx(7).3,
                    )
                },
            )
        })
    });

    #[rustfmt::skip]
    c.bench_function("batched-vec", |b| {
        b.iter(|| {
            vec1.chunks_exact(8).zip(vec2.chunks_exact(8)).fold(
                (0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0),
                |acc, (a, b)| {
                    (
                        acc.0 + a[0].0 * b[0].0 + a[0].1 * b[0].1 + a[0].2 * b[0].2 + a[0].3 * b[0].3,
                        acc.1 + a[1].0 * b[1].0 + a[1].1 * b[1].1 + a[1].2 * b[1].2 + a[1].3 * b[1].3,
                        acc.2 + a[2].0 * b[2].0 + a[2].1 * b[2].1 + a[2].2 * b[2].2 + a[2].3 * b[2].3,
                        acc.3 + a[3].0 * b[3].0 + a[3].1 * b[3].1 + a[3].2 * b[3].2 + a[3].3 * b[3].3,
                        acc.4 + a[4].0 * b[4].0 + a[4].1 * b[4].1 + a[4].2 * b[4].2 + a[4].3 * b[4].3,
                        acc.5 + a[5].0 * b[5].0 + a[5].1 * b[5].1 + a[5].2 * b[5].2 + a[5].3 * b[5].3,
                        acc.6 + a[6].0 * b[6].0 + a[6].1 * b[6].1 + a[6].2 * b[6].2 + a[6].3 * b[6].3,
                        acc.7 + a[7].0 * b[7].0 + a[7].1 * b[7].1 + a[7].2 * b[7].2 + a[7].3 * b[7].3,
                    )
                },
            )
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
