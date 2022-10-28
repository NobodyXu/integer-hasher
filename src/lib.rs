// Copyright 2018-2020 Parity Technologies (UK) Ltd.
//
// Licensed under the Apache License, Version 2.0 or MIT license, at your option.
//
// A copy of the Apache License, Version 2.0 is included in the software as
// LICENSE-APACHE and a copy of the MIT license is included in the software
// as LICENSE-MIT. You may also obtain a copy of the Apache License, Version 2.0
// at https://www.apache.org/licenses/LICENSE-2.0 and a copy of the MIT license
// at https://opensource.org/licenses/MIT.

// only enables the nightly `doc_cfg` feature when
// the `docsrs` configuration attribute is defined
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![cfg_attr(not(feature = "std"), no_std)]

use core::{
    hash::{BuildHasherDefault, Hasher},
    marker::PhantomData,
    num,
};

/// A `HashMap` with an integer domain, using `IntHasher` to perform no hashing at all.
///
/// # Examples
///
/// See [`IsEnabled`] for use with custom types.
///
/// ```
/// use integer_hasher::IntMap;
///
/// let mut m: IntMap<u32, bool> = IntMap::default();
///
/// m.insert(0, false);
/// m.insert(1, true);
///
/// assert!(m.contains_key(&0));
/// assert!(m.contains_key(&1));
/// ```
#[cfg(feature = "std")]
pub type IntMap<K, V> = std::collections::HashMap<K, V, BuildIntHasher<K>>;

/// A `HashSet` of integers, using `IntHasher` to perform no hashing at all.
///
/// # Examples
///
/// See [`IsEnabled`] for use with custom types.
///
/// ```
/// use integer_hasher::IntSet;
///
/// let mut m = IntSet::default();
///
/// m.insert(0u32);
/// m.insert(1u32);
///
/// assert!(m.contains(&0));
/// assert!(m.contains(&1));
/// ```
#[cfg(feature = "std")]
pub type IntSet<T> = std::collections::HashSet<T, BuildIntHasher<T>>;

/// An alias for `BuildHasherDefault` for use with `IntHasher`.
///
/// # Examples
///
/// See also [`IntMap`] and [`IntSet`] for some easier usage examples.
///
/// ```
/// use integer_hasher::BuildIntHasher;
/// use std::collections::HashMap;
///
/// let mut m: HashMap::<u8, char, BuildIntHasher<u8>> =
///     HashMap::with_capacity_and_hasher(2, BuildIntHasher::default());
///
/// m.insert(0, 'a');
/// m.insert(1, 'b');
///
/// assert_eq!(Some(&'a'), m.get(&0));
/// assert_eq!(Some(&'b'), m.get(&1));
/// ```
pub type BuildIntHasher<T> = BuildHasherDefault<IntHasher<T>>;

/// For an enabled type `T`, a `IntHasher<T>` implements `std::hash::Hasher` and
/// uses the value set by one of the `write_{u8, u16, u32, u64, usize, i8, i16, i32,
/// i64, isize}` methods as its hash output.
///
/// `IntHasher` does not implement any hashing algorithm and can only be used
/// with types which can be mapped directly to a numeric value. Out of the box
/// `IntHasher` is enabled for `u8`, `u16`, `u32`, `u64`, `usize`, `i8`, `i16`,
/// `i32`, `i64`, and `isize`. Types that should be used with `IntHasher` need
/// to implement [`IsEnabled`] and by doing so assert that their `Hash` impl invokes
/// *only one* of the `Hasher::write_{u8, u16, u32, u64, usize, i8, i16, i32, i64,
/// isize}` methods *exactly once*.
///
/// # Examples
///
/// See also [`BuildIntHasher`], [`IntMap`] and [`IntSet`] for some easier
/// usage examples. See [`IsEnabled`] for use with custom types.
///
/// ```
/// use integer_hasher::IntHasher;
/// use std::{collections::HashMap, hash::BuildHasherDefault};
///
/// let mut m: HashMap::<u8, char, BuildHasherDefault<IntHasher<u8>>> =
///     HashMap::with_capacity_and_hasher(2, BuildHasherDefault::default());
///
/// m.insert(0, 'a');
/// m.insert(1, 'b');
///
/// assert_eq!(Some(&'a'), m.get(&0));
/// assert_eq!(Some(&'b'), m.get(&1));
/// ```
#[derive(Debug)]
pub struct IntHasher<T>(u64, #[cfg(debug_assertions)] bool, PhantomData<T>);

impl<T> Copy for IntHasher<T> {}

impl<T> Clone for IntHasher<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Default for IntHasher<T> {
    fn default() -> Self {
        Self(
            0,
            #[cfg(debug_assertions)]
            false,
            PhantomData,
        )
    }
}

/// Types which are safe to use with `IntHasher`.
///
/// This marker trait is an option for types to enable themselves for use
/// with `IntHasher`. In order to be safe, the `Hash` impl needs to
/// satisfy the following constraint:
///
/// > **One of the `Hasher::write_{u8,u16,u32,u64,usize,i8,i16,i32,i64,isize}`
/// methods is invoked exactly once.**
///
/// The best way to ensure this is to write a custom `Hash` impl even when
/// deriving `Hash` for a simple newtype of a single type which itself
/// implements `IsEnabled` may work as well.
///
/// # Example
///
/// ```
/// #[derive(PartialEq, Eq)]
/// struct SomeType(u32);
///
/// impl std::hash::Hash for SomeType {
///     fn hash<H: std::hash::Hasher>(&self, hasher: &mut H) {
///         hasher.write_u32(self.0)
///     }
/// }
///
/// impl integer_hasher::IsEnabled for SomeType {}
///
/// let mut m = integer_hasher::IntMap::default();
///
/// m.insert(SomeType(1), 't');
/// m.insert(SomeType(0), 'f');
///
/// assert_eq!(Some(&'t'), m.get(&SomeType(1)));
/// assert_eq!(Some(&'f'), m.get(&SomeType(0)));
/// ```
pub trait IsEnabled {}

impl IsEnabled for u8 {}
impl IsEnabled for u16 {}
impl IsEnabled for u32 {}
impl IsEnabled for u64 {}
impl IsEnabled for usize {}

impl IsEnabled for i8 {}
impl IsEnabled for i16 {}
impl IsEnabled for i32 {}
impl IsEnabled for i64 {}
impl IsEnabled for isize {}

impl IsEnabled for num::NonZeroU8 {}
impl IsEnabled for num::NonZeroU16 {}
impl IsEnabled for num::NonZeroU32 {}
impl IsEnabled for num::NonZeroU64 {}
impl IsEnabled for num::NonZeroUsize {}

impl IsEnabled for num::NonZeroI8 {}
impl IsEnabled for num::NonZeroI16 {}
impl IsEnabled for num::NonZeroI32 {}
impl IsEnabled for num::NonZeroI64 {}
impl IsEnabled for num::NonZeroIsize {}

impl IsEnabled for num::Wrapping<u8> {}
impl IsEnabled for num::Wrapping<u16> {}
impl IsEnabled for num::Wrapping<u32> {}
impl IsEnabled for num::Wrapping<u64> {}
impl IsEnabled for num::Wrapping<usize> {}

impl IsEnabled for num::Wrapping<i8> {}
impl IsEnabled for num::Wrapping<i16> {}
impl IsEnabled for num::Wrapping<i32> {}
impl IsEnabled for num::Wrapping<i64> {}
impl IsEnabled for num::Wrapping<isize> {}

impl<T> IntHasher<T> {
    fn precond_check(&mut self) {
        #[cfg(debug_assertions)]
        {
            assert!(!self.1, "IntHasher: second write attempt detected.");
            self.1 = true
        }
    }
}

impl<T: IsEnabled> Hasher for IntHasher<T> {
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of IntHasher")
    }

    fn write_u8(&mut self, n: u8) {
        self.precond_check();
        self.0 = u64::from(n)
    }
    fn write_u16(&mut self, n: u16) {
        self.precond_check();
        self.0 = u64::from(n)
    }
    fn write_u32(&mut self, n: u32) {
        self.precond_check();
        self.0 = u64::from(n)
    }
    fn write_u64(&mut self, n: u64) {
        self.precond_check();
        self.0 = n
    }
    fn write_usize(&mut self, n: usize) {
        self.precond_check();
        self.0 = n as u64
    }

    fn write_i8(&mut self, n: i8) {
        self.precond_check();
        self.0 = n as u64
    }
    fn write_i16(&mut self, n: i16) {
        self.precond_check();
        self.0 = n as u64
    }
    fn write_i32(&mut self, n: i32) {
        self.precond_check();
        self.0 = n as u64
    }
    fn write_i64(&mut self, n: i64) {
        self.precond_check();
        self.0 = n as u64
    }
    fn write_isize(&mut self, n: isize) {
        self.precond_check();
        self.0 = n as u64
    }

    fn finish(&self) -> u64 {
        #[cfg(debug_assertions)]
        {
            assert!(self.1, "IntHasher: no write is called before finish()");
        }

        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ok() {
        let mut h1 = IntHasher::<u8>::default();
        h1.write_u8(42);
        assert_eq!(42, h1.finish());

        let mut h2 = IntHasher::<u16>::default();
        h2.write_u16(42);
        assert_eq!(42, h2.finish());

        let mut h3 = IntHasher::<u32>::default();
        h3.write_u32(42);
        assert_eq!(42, h3.finish());

        let mut h4 = IntHasher::<u64>::default();
        h4.write_u64(42);
        assert_eq!(42, h4.finish());

        let mut h5 = IntHasher::<usize>::default();
        h5.write_usize(42);
        assert_eq!(42, h5.finish());

        let mut h6 = IntHasher::<i8>::default();
        h6.write_i8(42);
        assert_eq!(42, h6.finish());

        let mut h7 = IntHasher::<i16>::default();
        h7.write_i16(42);
        assert_eq!(42, h7.finish());

        let mut h8 = IntHasher::<i32>::default();
        h8.write_i32(42);
        assert_eq!(42, h8.finish());

        let mut h9 = IntHasher::<i64>::default();
        h9.write_i64(42);
        assert_eq!(42, h9.finish());

        let mut h10 = IntHasher::<isize>::default();
        h10.write_isize(42);
        assert_eq!(42, h10.finish())
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u8_double_usage() {
        let mut h = IntHasher::<u8>::default();
        h.write_u8(42);
        h.write_u8(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u16_double_usage() {
        let mut h = IntHasher::<u16>::default();
        h.write_u16(42);
        h.write_u16(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u32_double_usage() {
        let mut h = IntHasher::<u32>::default();
        h.write_u32(42);
        h.write_u32(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u64_double_usage() {
        let mut h = IntHasher::<u64>::default();
        h.write_u64(42);
        h.write_u64(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn usize_double_usage() {
        let mut h = IntHasher::<usize>::default();
        h.write_usize(42);
        h.write_usize(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn i8_double_usage() {
        let mut h = IntHasher::<i8>::default();
        h.write_i8(42);
        h.write_i8(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn i16_double_usage() {
        let mut h = IntHasher::<i16>::default();
        h.write_i16(42);
        h.write_i16(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn i32_double_usage() {
        let mut h = IntHasher::<i32>::default();
        h.write_i32(42);
        h.write_i32(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn i64_double_usage() {
        let mut h = IntHasher::<i64>::default();
        h.write_i64(42);
        h.write_i64(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn isize_double_usage() {
        let mut h = IntHasher::<isize>::default();
        h.write_isize(42);
        h.write_isize(43);
    }
}
