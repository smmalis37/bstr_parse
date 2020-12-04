//! # bstr_parse
//!
//! Adds the ability to parse numbers out of `&[u8]`s. Like so:
//!
//! ```
//! use bstr_parse::*;
//!
//! let text: &[u8] = b"1234";
//! let num: u32 = text.parse().unwrap();
//! assert_eq!(num, 1234);
//! ```

#![warn(missing_docs)]
#![warn(missing_crate_level_docs)]
#![warn(private_doc_tests)]
#![warn(clippy::all)]
#![warn(clippy::cargo)]
#![forbid(unsafe_code)]

/// An extension trait for `parse`.
pub trait BStrParse {
    /// Parses this string slice into another type.
    ///
    /// Because `parse` is so general, it can cause problems with type
    /// inference. As such, `parse` is one of the few times you'll see
    /// the syntax affectionately known as the 'turbofish': `::<>`. This
    /// helps the inference algorithm understand specifically which type
    /// you're trying to parse into.
    ///
    /// `parse` can parse any type that implements the [`FromBStr`] trait.

    ///
    /// # Errors
    ///
    /// Will return [`Err`] if it's not possible to parse this string slice into
    /// the desired type.
    ///
    /// [`Err`]: FromBStr::Err
    ///
    /// # Examples
    ///
    /// Basic usage
    ///
    /// ```
    /// use bstr_parse::*;
    /// let four: u32 = b"4".parse().unwrap();
    ///
    /// assert_eq!(4, four);
    /// ```
    ///
    /// Using the 'turbofish' instead of annotating `four`:
    ///
    /// ```
    /// use bstr_parse::*;
    /// let four = b"4".parse::<u32>();
    ///
    /// assert_eq!(Ok(4), four);
    /// ```
    ///
    /// Failing to parse:
    ///
    /// ```
    /// use bstr_parse::*;
    /// let nope = b"j".parse::<u32>();
    ///
    /// assert!(nope.is_err());
    /// ```
    fn parse<F: FromBStr>(&self) -> Result<F, F::Err>;
}

impl BStrParse for [u8] {
    /// Parses this string slice into another type.
    ///
    /// Because `parse` is so general, it can cause problems with type
    /// inference. As such, `parse` is one of the few times you'll see
    /// the syntax affectionately known as the 'turbofish': `::<>`. This
    /// helps the inference algorithm understand specifically which type
    /// you're trying to parse into.
    ///
    /// `parse` can parse any type that implements the [`FromBStr`] trait.

    ///
    /// # Errors
    ///
    /// Will return [`Err`] if it's not possible to parse this string slice into
    /// the desired type.
    ///
    /// [`Err`]: FromBStr::Err
    ///
    /// # Examples
    ///
    /// Basic usage
    ///
    /// ```
    /// use bstr_parse::*;
    /// let four: u32 = b"4".parse().unwrap();
    ///
    /// assert_eq!(4, four);
    /// ```
    ///
    /// Using the 'turbofish' instead of annotating `four`:
    ///
    /// ```
    /// use bstr_parse::*;
    /// let four = b"4".parse::<u32>();
    ///
    /// assert_eq!(Ok(4), four);
    /// ```
    ///
    /// Failing to parse:
    ///
    /// ```
    /// use bstr_parse::*;
    /// let nope = b"j".parse::<u32>();
    ///
    /// assert!(nope.is_err());
    /// ```
    #[inline]
    fn parse<F: FromBStr>(&self) -> Result<F, F::Err> {
        FromBStr::from_bstr(self)
    }
}

/// Parse a value from a string
///
/// `FromBStr`'s [`from_bstr`] method is often used implicitly, through
/// `[u8]`'s [`parse`] method. See [`parse`]'s documentation for examples.
///
/// [`from_bstr`]: FromBStr::from_bstr
/// [`parse`]: BStrParse::parse
///
/// `FromBStr` does not have a lifetime parameter, and so you can only parse types
/// that do not contain a lifetime parameter themselves. In other words, you can
/// parse an `i32` with `FromBStr`, but not a `&i32`. You can parse a struct that
/// contains an `i32`, but not one that contains an `&i32`.
///
/// # Examples
///
/// Basic implementation of `FromBStr` on an example `Point` type:
///
/// ```
/// use bstr_parse::*;
///
/// #[derive(Debug, PartialEq)]
/// struct Point {
///     x: i32,
///     y: i32
/// }
///
/// impl FromBStr for Point {
///     type Err = ParseIntError;
///
///     fn from_bstr(s: &[u8]) -> Result<Self, Self::Err> {
///         let coords: Vec<&[u8]> = s.split(|&p| p == b'(' || p == b')' || p == b',')
///                                  .skip_while(|s| s.is_empty())
///                                  .take_while(|s| !s.is_empty())
///                                  .collect();
///
///         let x_frombstr = coords[0].parse::<i32>()?;
///         let y_frombstr = coords[1].parse::<i32>()?;
///
///         Ok(Point { x: x_frombstr, y: y_frombstr })
///     }
/// }
///
/// let p = Point::from_bstr(b"(1,2)");
/// assert_eq!(p.unwrap(), Point{ x: 1, y: 2} )
/// ```
pub trait FromBStr: Sized {
    /// The associated error which can be returned from parsing.
    type Err;

    /// Parses a string `s` to return a value of this type.
    ///
    /// If parsing succeeds, return the value inside [`Ok`], otherwise
    /// when the string is ill-formatted return an error specific to the
    /// inside [`Err`]. The error type is specific to implementation of the trait.
    ///
    /// # Examples
    ///
    /// Basic usage with [`i32`][ithirtytwo], a type that implements `FromBStr`:
    ///
    /// [ithirtytwo]: ../../std/primitive.i32.html
    ///
    /// ```
    /// use bstr_parse::*;
    ///
    /// let s = b"5";
    /// let x = i32::from_bstr(s).unwrap();
    ///
    /// assert_eq!(5, x);
    /// ```
    fn from_bstr(s: &[u8]) -> Result<Self, Self::Err>;
}

#[doc(hidden)]
trait FromBStrRadixHelper: PartialOrd + Copy {
    fn min_value() -> Self;
    fn max_value() -> Self;
    fn from_u32(u: u32) -> Self;
    fn checked_mul(&self, other: u32) -> Option<Self>;
    fn checked_sub(&self, other: u32) -> Option<Self>;
    fn checked_add(&self, other: u32) -> Option<Self>;
}

macro_rules! from_bstr_radix_int_impl {
    ($($t:ty)*) => {$(
        impl FromBStr for $t {
            type Err = ParseIntError;

            #[inline]
            fn from_bstr(src: &[u8]) -> Result<Self, ParseIntError> {
                from_bstr_radix(src, 10)
            }
        }
    )*}
}
from_bstr_radix_int_impl! { isize i8 i16 i32 i64 i128 usize u8 u16 u32 u64 u128 }

macro_rules! doit {
    ($($t:ty)*) => ($(impl FromBStrRadixHelper for $t {
        #[inline]
        fn min_value() -> Self { Self::MIN }
        #[inline]
        fn max_value() -> Self { Self::MAX }
        #[inline]
        fn from_u32(u: u32) -> Self { u as Self }
        #[inline]
        fn checked_mul(&self, other: u32) -> Option<Self> {
            Self::checked_mul(*self, other as Self)
        }
        #[inline]
        fn checked_sub(&self, other: u32) -> Option<Self> {
            Self::checked_sub(*self, other as Self)
        }
        #[inline]
        fn checked_add(&self, other: u32) -> Option<Self> {
            Self::checked_add(*self, other as Self)
        }
    })*)
}
doit! { i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize }

fn from_bstr_radix<T: FromBStrRadixHelper>(src: &[u8], radix: u32) -> Result<T, ParseIntError> {
    use self::IntErrorKind::*;
    use self::ParseIntError as PIE;

    assert!(
        radix >= 2 && radix <= 36,
        "from_bstr_radix_int: must lie in the range `[2, 36]` - found {}",
        radix
    );

    if src.is_empty() {
        return Err(PIE { kind: Empty });
    }

    let is_signed_ty = T::from_u32(0) > T::min_value();

    let (is_positive, digits) = match src[0] {
        b'+' => (true, &src[1..]),
        b'-' if is_signed_ty => (false, &src[1..]),
        _ => (true, src),
    };

    if digits.is_empty() {
        return Err(PIE { kind: Empty });
    }

    let mut result = T::from_u32(0);
    if is_positive {
        // The number is positive
        for &c in digits {
            let x = match (c as char).to_digit(radix) {
                Some(x) => x,
                None => return Err(PIE { kind: InvalidDigit }),
            };
            result = match result.checked_mul(radix) {
                Some(result) => result,
                None => return Err(PIE { kind: Overflow }),
            };
            result = match result.checked_add(x) {
                Some(result) => result,
                None => return Err(PIE { kind: Overflow }),
            };
        }
    } else {
        // The number is negative
        for &c in digits {
            let x = match (c as char).to_digit(radix) {
                Some(x) => x,
                None => return Err(PIE { kind: InvalidDigit }),
            };
            result = match result.checked_mul(radix) {
                Some(result) => result,
                None => return Err(PIE { kind: Underflow }),
            };
            result = match result.checked_sub(x) {
                Some(result) => result,
                None => return Err(PIE { kind: Underflow }),
            };
        }
    }
    Ok(result)
}

/// An error which can be returned when parsing an integer.
///
/// This error is used as the error type for the `from_bstr_radix()` functions
/// on the primitive integer types.
///
/// # Potential causes
///
/// Among other causes, `ParseIntError` can be thrown because of leading or trailing whitespace
/// in the string e.g., when it is obtained from the standard input.
///
/// [`i8::from_bstr_radix`]: i8::from_bstr_radix
///
/// # Example
///
/// ```
/// use bstr_parse::*;
///
/// if let Err(e) = i32::from_bstr_radix(b"a12", 10) {
///     println!("Failed conversion to i32: {}", e);
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseIntError {
    kind: IntErrorKind,
}

/// Enum to store the various types of errors that can cause parsing an integer to fail.
///
/// # Example
///
/// ```
/// use bstr_parse::*;
///
/// # fn main() {
/// if let Err(e) = i32::from_bstr_radix(b"a12", 10) {
///     println!("Failed conversion to i32: {:?}", e.kind());
/// }
/// # }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum IntErrorKind {
    /// Value being parsed is empty.
    ///
    /// Among other causes, this variant will be constructed when parsing an empty string.
    Empty,
    /// Contains an invalid digit.
    ///
    /// Among other causes, this variant will be constructed when parsing a string that
    /// contains a letter.
    InvalidDigit,
    /// Integer is too large to store in target integer type.
    Overflow,
    /// Integer is too small to store in target integer type.
    Underflow,
    /// Value was Zero
    ///
    /// This variant will be emitted when the parsing string has a value of zero, which
    /// would be illegal for non-zero types.
    Zero,
}

impl ParseIntError {
    /// Outputs the detailed cause of parsing an integer failing.
    pub fn kind(&self) -> &IntErrorKind {
        &self.kind
    }

    #[doc(hidden)]
    pub fn __description(&self) -> &str {
        match self.kind {
            IntErrorKind::Empty => "cannot parse integer from empty string",
            IntErrorKind::InvalidDigit => "invalid digit found in string",
            IntErrorKind::Overflow => "number too large to fit in target type",
            IntErrorKind::Underflow => "number too small to fit in target type",
            IntErrorKind::Zero => "number would be zero for non-zero type",
        }
    }
}

impl std::fmt::Display for ParseIntError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.__description().fmt(f)
    }
}

impl std::error::Error for ParseIntError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        self.__description()
    }
}

/// An extension trait for `from_bstr_radix`.
pub trait FromBStrRadix: Sized {
    /// Converts a string slice in a given base to an integer.
    ///
    /// The string is expected to be an optional `+` or `-` sign followed by digits.
    /// Leading and trailing whitespace represent an error. Digits are a subset of these characters,
    /// depending on `radix`:
    ///
    ///  * `0-9`
    ///  * `a-z`
    ///  * `A-Z`
    ///
    /// # Panics
    ///
    /// This function panics if `radix` is not in the range from 2 to 36.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr_parse::*;
    ///
    /// assert_eq!(u8::from_bstr_radix(b"A", 16), Ok(10));
    /// ```
    fn from_bstr_radix(src: &[u8], radix: u32) -> Result<Self, ParseIntError>;
}

macro_rules! doc_comment {
    ($x:expr, $($tt:tt)*) => {
        #[doc = $x]
        $($tt)*
    };
}

macro_rules! from_bstr_radix_impl {
    ($($t:ty)*) => {$(
    impl FromBStrRadix for $t {
        doc_comment! {
            concat!("Converts a string slice in a given base to an integer.

The string is expected to be an optional `+` or `-` sign followed by digits.
Leading and trailing whitespace represent an error. Digits are a subset of these characters,
depending on `radix`:

 * `0-9`
 * `a-z`
 * `A-Z`

# Panics

This function panics if `radix` is not in the range from 2 to 36.

# Examples

Basic usage:

```
use bstr_parse::*;

assert_eq!(", stringify!($t), "::from_bstr_radix(b\"A\", 16), Ok(10));
```"),
            #[inline]
            fn from_bstr_radix(src: &[u8], radix: u32) -> Result<Self, ParseIntError> {
                from_bstr_radix(src, radix)
            }
        }
    }
    )*}
}
from_bstr_radix_impl! { i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize }
