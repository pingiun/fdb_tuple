use std::num::TryFromIntError;

#[cfg(feature = "uuid")]
use uuid::Uuid;

#[derive(Debug)]
pub struct Error {
    pub kind: ErrorKind,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ErrorKind {
    UnexpectedEndOfInput,
    NotThisType,
    Utf8DecodeError,
    ExtraData,
    NumberDoesntFit,
}

impl From<TryFromIntError> for Error {
    fn from(_: TryFromIntError) -> Self {
        Error {
            kind: ErrorKind::NumberDoesntFit,
        }
    }
}

pub trait FromBytes: Sized {
    fn from_bytes(bytes: &[u8], nested: u8) -> Result<(Self, &[u8]), Error>;
}

fn eof() -> Error {
    Error {
        kind: ErrorKind::UnexpectedEndOfInput,
    }
}

impl FromBytes for Vec<u8> {
    fn from_bytes(bytes: &[u8], _nested: u8) -> Result<(Self, &[u8]), Error> {
        vec_from_bytes(bytes, 0x01)
    }
}

impl FromBytes for String {
    fn from_bytes(bytes: &[u8], _nested: u8) -> Result<(Self, &[u8]), Error> {
        let (bytes, rest) = vec_from_bytes(bytes, 0x02)?;
        Ok((
            String::from_utf8(bytes).map_err(|_| Error {
                kind: ErrorKind::Utf8DecodeError,
            })?,
            rest,
        ))
    }
}

fn vec_from_bytes(bytes: &[u8], typecode: u8) -> Result<(Vec<u8>, &[u8]), Error> {
    let mut new = Vec::new();
    if *bytes.first().ok_or_else(eof)? != typecode {
        return Err(Error {
            kind: ErrorKind::NotThisType,
        });
    }
    let mut rest = &bytes[1..];
    while !rest.is_empty() {
        if *rest.first().ok_or_else(eof)? == 0x00 && rest.get(1) == Some(&0xFF) {
            rest = &rest[2..];
            new.push(0x00);
        }
        if *rest.first().ok_or_else(eof)? == 0x00 {
            return Ok((new, &rest[1..]));
        }
        new.push(*rest.first().ok_or_else(eof)?);
        rest = &rest[1..];
    }
    Err(eof())
}

impl FromBytes for () {
    fn from_bytes(bytes: &[u8], nested: u8) -> Result<(Self, &[u8]), Error> {
        if nested > 0 {
            if *bytes.first().ok_or_else(eof)? != 0x05 {
                return Err(Error {
                    kind: ErrorKind::NotThisType,
                });
            }
            if *bytes.get(1).ok_or_else(eof)? != 0x05 {
                return Err(Error {
                    kind: ErrorKind::NotThisType,
                });
            }
            Ok(((), &bytes[2..]))
        } else {
            Ok(((), bytes))
        }
    }
}

macro_rules! impl_tuple {
    ($($var:ident $t:tt),+) => {
        impl<$($t),+> FromBytes for ($($t),+,) where $($t: FromBytes),+ {
            fn from_bytes(mut bytes: &[u8], nested: u8) -> Result<(Self, &[u8]), Error> {
                let requirenullbyte = if nested > 0 && bytes.first() == Some(&0x05) {
                    bytes = &bytes[1..];
                    true
                } else {
                    false
                };
                $(
                    let ($var, rest) = $t::from_bytes(bytes, nested + 1)?;
                    bytes = rest;
                )+
                if requirenullbyte {
                    if *bytes.first().ok_or_else(eof)? != 0x00 {
                        return Err(Error {
                            kind: ErrorKind::NotThisType,
                        });
                    }
                    return Ok((($($var,)+), &bytes[1..]))
                }
                Ok((($($var,)+), bytes))
            }
        }
    }
}

impl_tuple!(a A);
impl_tuple!(a A, b B);
impl_tuple!(a A, b B, c C);
impl_tuple!(a A, b B, c C, d D);
impl_tuple!(a A, b B, c C, d D, e E);
impl_tuple!(a A, b B, c C, d D, e E, f F);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L, m M);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L, m M, n N);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L, m M, n N, o O);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L, m M, n N, o O, p P);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L, m M, n N, o O, p P, q Q);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L, m M, n N, o O, p P, q Q, r R);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L, m M, n N, o O, p P, q Q, r R, s S);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L, m M, n N, o O, p P, q Q, r R, s S, t T);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L, m M, n N, o O, p P, q Q, r R, s S, t T, u U);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L, m M, n N, o O, p P, q Q, r R, s S, t T, u U, v V);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L, m M, n N, o O, p P, q Q, r R, s S, t T, u U, v V, w W);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L, m M, n N, o O, p P, q Q, r R, s S, t T, u U, v V, w W, x X);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L, m M, n N, o O, p P, q Q, r R, s S, t T, u U, v V, w W, x X, y Y);
impl_tuple!(a A, b B, c C, d D, e E, f F, g G, h H, i I, j J, k K, l L, m M, n N, o O, p P, q Q, r R, s S, t T, u U, v V, w W, x X, y Y, z Z);


macro_rules! impl_unsigned {
    ($t:ty, $size:literal, $min:literal, $max:literal) => {
        impl FromBytes for $t {
            fn from_bytes(bytes: &[u8], _nested: u8) -> Result<(Self, &[u8]), Error> {
                let first_byte = *bytes.first().ok_or_else(eof)?;
                if first_byte == 0x14 {
                    return Ok((0, &bytes[1..]));
                }
                if !($min..=$max).contains(&first_byte) {
                    return Err(Error {
                        kind: ErrorKind::NotThisType,
                    });
                }
                let num_bytes = (first_byte - 0x14) as usize;
                let mut num = [0x0; $size];
                num[($size-num_bytes)..].copy_from_slice(bytes.get(1..(1 + num_bytes)).ok_or_else(eof)?);
                Ok((
                    <$t>::from_be_bytes(num),
                    &bytes[(1 + num_bytes)..],
                ))
            }
        }
    };
}

impl_unsigned!(u8, 1, 0x15, 0x16);
impl_unsigned!(u16, 2, 0x15, 0x17);
impl_unsigned!(u32, 4, 0x15, 0x19);
impl_unsigned!(u64, 8, 0x15, 0x1c);

macro_rules! impl_signed {
    ($t:ty, $u:ty, $size:literal, $min:literal, $max:literal) => {
        impl FromBytes for $t {
            fn from_bytes(bytes: &[u8], _nested: u8) -> Result<(Self, &[u8]), Error> {
                let first_byte = *bytes.first().ok_or_else(eof)?;
                if first_byte == 0x14 {
                    return Ok((0, &bytes[1..]));
                }
                if !($min..=$max).contains(&first_byte) {
                    return Err(Error {
                        kind: ErrorKind::NotThisType,
                    });
                }
                let num_bytes = if first_byte > 0x14 {
                    (first_byte - 0x14) as usize
                } else {
                    (0x14 - first_byte) as usize
                };
                let mut num = [0x0; $size];
                num[($size-num_bytes)..].copy_from_slice(bytes.get(1..(1 + num_bytes)).ok_or_else(eof)?);
                if first_byte < 0x14 {
                    return Ok((
                        -(<$t>::try_from(!<$u>::from_be_bytes(num))?),
                        &bytes[(1 + num_bytes)..],
                    ));
                }
                Ok((
                    <$t>::from_be_bytes(num),
                    &bytes[(1 + num_bytes)..],
                ))
            }
        }
    };
}

impl_signed!(i8, u8, 1, 0x13, 0x15);
impl_signed!(i16, u16, 2, 0x12, 0x16);
impl_signed!(i32, u32, 4, 0x10, 0x18);
impl_signed!(i64, u64, 8, 0x0c, 0x1c);

impl FromBytes for f32 {
    fn from_bytes(bytes: &[u8], _nested: u8) -> Result<(Self, &[u8]), Error> {
        if *bytes.first().ok_or_else(eof)? != b'\x20' {
            return Err(Error {
                kind: ErrorKind::NotThisType,
            });
        }
        let mut bits = [0; 4];
        bits.copy_from_slice(bytes.get(1..5).ok_or_else(eof)?);
        let float = if bits[0] & 0x80 == 0 {
            f32::from_be_bytes(bits.map(|x| !x))
        } else {
            bits[0] ^= 0x80;
            f32::from_be_bytes(bits)
        };
        Ok((float, &bytes[5..]))
    }
}

impl FromBytes for f64 {
    fn from_bytes(bytes: &[u8], _nested: u8) -> Result<(Self, &[u8]), Error> {
        if *bytes.first().ok_or_else(eof)? != b'\x20' {
            return Err(Error {
                kind: ErrorKind::NotThisType,
            });
        }
        let mut bits = [0; 8];
        bits.copy_from_slice(bytes.get(1..9).ok_or_else(eof)?);
        let float = if bits[0] & 0x80 == 0 {
            f64::from_be_bytes(bits.map(|x| !x))
        } else {
            bits[0] ^= 0x80;
            f64::from_be_bytes(bits)
        };
        Ok((float, &bytes[5..]))
    }
}

impl FromBytes for bool {
    fn from_bytes(bytes: &[u8], _nested: u8) -> Result<(Self, &[u8]), Error> {
        Ok((match bytes.first().ok_or_else(eof)? {
            b'\x26' => false,
            b'\x27' => true,
            _ => return Err(Error {
                kind: ErrorKind::NotThisType,
            }),
        }, &bytes[1..]))
    }
}

#[cfg(feature = "uuid")]
impl FromBytes for Uuid {
    fn from_bytes(bytes: &[u8], _nested: u8) -> Result<(Self, &[u8]), Error> {
        if *bytes.first().ok_or_else(eof)? != b'\x30' {
            return Err(Error {
                kind: ErrorKind::NotThisType,
            });
        }
        let mut uuid = [0; 16];
        uuid.copy_from_slice(bytes.get(1..17).ok_or_else(eof)?);
        Ok((Uuid::from_bytes(uuid), &bytes[17..]))
    }
}

impl<T> FromBytes for Option<T> where T: FromBytes{
    fn from_bytes(bytes: &[u8], nested: u8) -> Result<(Self, &[u8]), Error> {
        if nested > 1 {
            if bytes.get(..2).ok_or_else(eof)? != b"\x00\xFF" {
                return Ok((None, &bytes[2..]));
            }
        } else {
            #[allow(clippy::collapsible_else_if)]
            if bytes.first().ok_or_else(eof)? != &0x00 {
                return Ok((None, bytes));
            }
        }
        let (sub_value, rest) = T::from_bytes(bytes, nested)?;
        Ok((Some(sub_value), rest))
    }
}
