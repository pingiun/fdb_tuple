//! Implements [FoundationDB tuples](https://github.com/apple/foundationdb/blob/main/design/tuple.md)
//!
//! # Features
//!
//! - `uuid`: enables `ToBytes` and `FromBytes` for `uuid::Uuid`

use from_bytes::{FromBytes, Error};
use to_bytes::ToBytes;

pub mod to_bytes;
pub mod from_bytes;

/// Converts a value to a tuple-encoded byte vector.
///
/// # Examples
///
/// ```rust
/// use fdb_tuple::{to_bytes, from_bytes};
///
/// let bytes = to_bytes(("a", "b"));
/// assert_eq!(bytes, b"\x02a\x00\x02b\x00");
///
/// let tuple: (String, String) = from_bytes(&bytes).unwrap();
/// assert_eq!(tuple, ("a".to_string(), "b".to_string()));
/// ```
pub fn to_bytes<T: ToBytes>(value: T) -> Vec<u8> {
    value.to_bytes(0)
}

/// Converts a byte vector to a value.
///
/// # Examples
///
/// ```rust
/// use fdb_tuple::{to_bytes, from_bytes};
///
/// let bytes = to_bytes(("a", "b"));
/// assert_eq!(bytes, b"\x02a\x00\x02b\x00");
///
/// let tuple: (String, String) = from_bytes(&bytes).unwrap();
/// assert_eq!(tuple, ("a".to_string(), "b".to_string()));
/// ```
pub fn from_bytes<T>(bytes: &[u8]) -> Result<T, Error>
where
    T: FromBytes,
{
    let (res, rest) = T::from_bytes(bytes, 0)?;
    if !rest.is_empty() {
        return Err(Error { kind: from_bytes::ErrorKind::ExtraData })
    }
    Ok(res)
}

#[cfg(test)]
mod test {
    use crate::to_bytes;
    use crate::from_bytes;

    #[test]
    fn simple_unicode_string() {
        assert_eq!(to_bytes("foobar"), b"\x02foobar\x00");
        assert_eq!(from_bytes::<String>(b"\x02foobar\x00").unwrap(), "foobar".to_string());
    }

    #[test]
    fn simple_tuple() {
        assert_eq!(to_bytes(("a", "b")), b"\x02a\x00\x02b\x00");
        assert_eq!(from_bytes::<(String, String)>(b"\x02a\x00\x02b\x00").unwrap(), ("a".to_string(), "b".to_string()));
    }

    #[test]
    fn nested_tuple() {
        assert_eq!(
            to_bytes((("a", "b"), ("c", "d"))),
            b"\x05\x02a\x00\x02b\x00\x00\x05\x02c\x00\x02d\x00\x00"
        );
        assert_eq!(
            from_bytes::<((String, String), (String, String))>(b"\x05\x02a\x00\x02b\x00\x00\x05\x02c\x00\x02d\x00\x00").unwrap(),
            (("a".to_string(), "b".to_string()), ("c".to_string(), "d".to_string()))
        );
    }

    #[test]
    fn negative_i8() {
        assert_eq!(to_bytes(-1i8), b"\x13\xfe");
        assert_eq!(to_bytes(-128i8), b"\x13\x7f");
    }

    #[test]
    fn number_spec() {
        assert_eq!(to_bytes(-5551212), b"\x11\xabK\x93");
    }

    #[test]
    fn float_spec() {
        assert_eq!(to_bytes(-42f32), b"\x20\x3d\xd7\xff\xff");
    }

    #[test]
    fn decode() {
        let bytes = b"\x02cpki\x00\x18\\\xe2\xcc\xc2\x01\xe3\xd2!\x8c|\xc4x\xe7\xfd\x14\xfe\xd1.\x01u\xf9\x156\xdc\xb7\xc0_O\xc3\xc9\r\x99\xb6\xf3\xd1\xef\x99\x00\x15\t\x01\xfc0\x8e\x83\x1c\xbad\xf5Vf\x9b:2\x85\x91\xb6H!2>\x1dRL\x8b>\x00\xff\x00\xff\xad\x1d2P\xac\x00";
        let (tag, timestamp, pubkey, kind, id): (String, u64, Vec<u8>, u64, Vec<u8>) = from_bytes(bytes).unwrap();
        assert_eq!(tag, "cpki");
    }
}
