# integer-hasher

For an enabled type `T`, a `IntHasher<T>` implements `std::hash::Hasher` and
uses the value set by one of the `write_{u8, u16, u32, u64, usize, i8, i16, i32,
i64, isize}` methods as its hash output.

`IntHasher` does not implement any hashing algorithm and can only be used
with types which can be mapped directly to a numeric value. Out of the box
`IntHasher` is enabled for `u8`, `u16`, `u32`, `u64`, `usize`, `i8`, `i16`,
`i32`, `i64`, and `isize`. Types that should be used with `IntHasher` need
to implement [`IsEnabled`] and by doing so assert that their `Hash` impl invokes
*only one* of the `Hasher::write_{u8, u16, u32, u64, usize, i8, i16, i32, i64,
isize}` methods *exactly once*.

Note that for just like fxhash and other stable hashers, there are some
performance drawback according to
[this blob](https://morestina.net/blog/1843/the-stable-hashmap-trap).

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
