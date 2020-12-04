# bstr_parse

Adds the ability to parse numbers out of `&[u8]`s. Like so:

```rust
use bstr_parse::*;

let text: &[u8] = b"1234";
let num: u32 = text.parse().unwrap();
assert_eq!(num, 1234);
```

## Why?

When dealing with text that is guaranteed to be pure ASCII, writing code that operates over a `&[u8]` can often be faster than operating over a `&str`, as this avoids all Unicode-related overhead.

## So using this crate will be faster than `str::parse`?

Nope! The code in this crate has been copied straight out of std, with bits minimally modified. It turns out the parsing algorithm in std already operates over `&[u8]`s, there's just no way to call it without getting an `&str` first.

Parts were copied from:
* https://github.com/rust-lang/rust/blob/7eac88abb2e57e752f3302f02be5f3ce3d7adfb4/library/core/src/str/mod.rs#L2157
* https://github.com/rust-lang/rust/blob/7eac88abb2e57e752f3302f02be5f3ce3d7adfb4/library/core/src/str/traits.rs#L534
* https://github.com/rust-lang/rust/blob/7eac88abb2e57e752f3302f02be5f3ce3d7adfb4/library/core/src/num/mod.rs#L763
* https://github.com/rust-lang/rust/blob/7eac88abb2e57e752f3302f02be5f3ce3d7adfb4/library/core/src/num/error.rs#L48
* https://github.com/rust-lang/rust/blob/7eac88abb2e57e752f3302f02be5f3ce3d7adfb4/library/core/src/num/uint_macros.rs#L49
* https://github.com/rust-lang/rust/blob/7eac88abb2e57e752f3302f02be5f3ce3d7adfb4/library/std/src/error.rs#L412

## So...why use this crate?

Because often when parsing text you're doing more than just parsing out numbers. Many other common parsing operations will be faster over `&[u8]`s than over `&str`. However if you need to parse numbers in addition to these other things, without this crate you'd either have to operate entirely over `&str`s or construct them as needed, paying (potentially) unnescessary Unicode overhead at every step.

## Should I use this crate?

Probably not. In the vast majority of use cases the overhead of proper Unicode handling will be so minimal as to not matter. I made this crate specifically for benchmark games, where doing absurd things to eek out every microsecond of performance is worthwhile.
