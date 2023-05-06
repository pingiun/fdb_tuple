use seq_macro::seq;
#[cfg(feature = "uuid")]
use uuid::Uuid;

pub trait ToBytes {
    fn to_bytes(&self, nested: u8) -> Vec<u8>;
}

impl ToBytes for [u8] {
    fn to_bytes(&self, _nested: u8) -> Vec<u8> {
        let mut bytes = vec![b'\x01'];
        for byte in self {
            match byte {
                b'\x00' => bytes.extend(b"\x00\xFF"),
                x => bytes.push(*x),
            }
        }
        bytes.push(b'\x00');
        bytes
    }
}

impl<const N: usize> ToBytes for [u8; N] {
    fn to_bytes(&self, nested: u8) -> Vec<u8> {
        self[..].to_bytes(nested)
    }
}

impl ToBytes for &str {
    fn to_bytes(&self, _nested: u8) -> Vec<u8> {
        let mut bytes = vec![b'\x02'];
        bytes.extend(self.as_bytes());
        bytes.push(b'\x00');
        bytes
    }
}

impl ToBytes for () {
    fn to_bytes(&self, nested: u8) -> Vec<u8> {
        if nested > 0 {
            vec![b'\x05', b'\x00']
        } else {
            vec![]
        }
    }
}

macro_rules! impl_tuple {
    ($count:literal, $($t:tt),+) => {
        impl<$($t),+> ToBytes for ($($t),+,) where $($t: ToBytes),+ {
            fn to_bytes(&self, nested: u8) -> Vec<u8> {
                let mut bytes = Vec::new();
                if nested > 0 {
                    bytes.push(b'\x05');
                }
                seq!(N in 0..$count {
                    bytes.extend(self.N.to_bytes(nested + 1));
                });
                if nested > 0 {
                    bytes.push(b'\x00');
                }
                bytes
            }
        }
    };
}

impl_tuple!(1, A);
impl_tuple!(2, A, B);
impl_tuple!(3, A, B, C);
impl_tuple!(4, A, B, C, D);
impl_tuple!(5, A, B, C, D, E);
impl_tuple!(6, A, B, C, D, E, F);
impl_tuple!(7, A, B, C, D, E, F, G);
impl_tuple!(8, A, B, C, D, E, F, G, H);
impl_tuple!(9, A, B, C, D, E, F, G, H, I);
impl_tuple!(10, A, B, C, D, E, F, G, H, I, J);
impl_tuple!(11, A, B, C, D, E, F, G, H, I, J, K);
impl_tuple!(12, A, B, C, D, E, F, G, H, I, J, K, L);
impl_tuple!(13, A, B, C, D, E, F, G, H, I, J, K, L, M);
impl_tuple!(14, A, B, C, D, E, F, G, H, I, J, K, L, M, N);
impl_tuple!(15, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O);
impl_tuple!(16, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P);
impl_tuple!(17, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q);
impl_tuple!(18, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R);
impl_tuple!(19, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S);
impl_tuple!(20, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T);
impl_tuple!(21, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U);
impl_tuple!(22, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V);
impl_tuple!(23, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W);
impl_tuple!(24, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X);
impl_tuple!(25, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y);
impl_tuple!(26, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z);

macro_rules! impl_unsigned {
    ($t:ty, $size:literal) => {
        impl ToBytes for $t {
            #[allow(clippy::int_plus_one)]
            #[allow(unused_mut)]
            fn to_bytes(&self, _nested: u8) -> Vec<u8> {
                if *self == 0 {
                    return vec![b'\x14'];
                }
                let mut bytes = vec![];
                loop {
                seq!(N in 1..$size {
                    if *self <= (1 << (8 * N)) - 1 {
                        bytes.push(0x14 + N);
                        bytes.extend(self.to_be_bytes().iter().skip($size - N));
                        break;
                    }
                });
                break;
                }
                bytes
            }
        }
    };
}

impl_unsigned!(u8, 1);
impl_unsigned!(u16, 2);
impl_unsigned!(u32, 4);
impl_unsigned!(u64, 8);

macro_rules! impl_signed {
    ($t:ty, $size:literal) => {
        impl ToBytes for $t {
            #[allow(clippy::int_plus_one)]
            #[allow(unused_mut)]
            fn to_bytes(&self, _nested: u8) -> Vec<u8> {
                if *self == 0 {
                    return vec![b'\x14'];
                }
                let mut bytes = vec![];
                loop {
                seq!(N in 1..$size {
                    if *self >= -(1 << ((8 * N) - 1)) && *self < 0 {
                        bytes.push(0x14 - N);
                        bytes.extend((!self.unsigned_abs()).to_be_bytes().iter().skip($size - N));
                        break;
                    } else if *self > 0 && *self <= (1 << (8 * N) - 1) - 1 {
                        bytes.push(0x14 + N);
                        bytes.extend(self.to_be_bytes().iter().skip($size - N));
                        break;
                    }
                });
                if *self >= <$t>::MIN && *self < 0 {
                    bytes.push(0x14 - $size);
                    bytes.extend((!self.unsigned_abs()).to_be_bytes().iter());
                    break;
                } else if *self > 0 && *self <= <$t>::MAX {
                    bytes.push(0x14 + $size);
                    bytes.extend(self.to_be_bytes().iter());
                    break;
                }
                break;
                }
                bytes
            }
        }
    };
}

impl_signed!(i8, 1);
impl_signed!(i16, 2);
impl_signed!(i32, 4);
impl_signed!(i64, 8);

impl ToBytes for f32 {
    fn to_bytes(&self, _nested: u8) -> Vec<u8> {
        let mut bytes = vec![b'\x20'];
        let bits = self.to_be_bytes();
        if bits[0] & 0x80 != 0 {
            bytes.extend(bits.map(|x| !x));
        } else {
            bytes.push(0x80 ^ bits[0]);
            bytes.extend(&bits[1..]);
        }
        bytes
    }
}

impl ToBytes for f64 {
    fn to_bytes(&self, _nested: u8) -> Vec<u8> {
        let mut bytes = vec![b'\x21'];
        let bits = self.to_be_bytes();
        if bits[0] & 0x80 != 0 {
            bytes.extend(bits.map(|x| !x));
        } else {
            bytes.push(0x80 ^ bits[0]);
            bytes.extend(&bits[1..]);
        }
        bytes
    }
}

impl ToBytes for bool {
    #[allow(clippy::bool_comparison)]
    fn to_bytes(&self, _nested: u8) -> Vec<u8> {
        if *self == false {
            vec![b'\x26']
        } else {
            vec![b'\x27']
        }
    }
}

#[cfg(feature = "uuid")]
impl ToBytes for Uuid {
    fn to_bytes(&self, _nested: u8) -> Vec<u8> {
        let mut bytes = vec![b'\x30'];
        bytes.extend(self.as_bytes());
        bytes
    }
}

impl<T> ToBytes for Option<T>
where
    T: ToBytes,
{
    fn to_bytes(&self, nested: u8) -> Vec<u8> {
        match self {
            Some(x) => x.to_bytes(nested),
            None => {
                if nested > 1 {
                    vec![b'\x00', b'\xFF']
                } else {
                    vec![b'\x00']
                }
            }
        }
    }
}

macro_rules! deref_impl {
    (
        $(#[doc = $doc:tt])*
        <$($desc:tt)+
    ) => {
        $(#[doc = $doc])*
        impl <$($desc)+ {
            #[inline]
            fn to_bytes(&self, nested: u8) -> Vec<u8> {
                (**self).to_bytes(nested)
            }
        }
    };
}

deref_impl!(<'a, T: ?Sized> ToBytes for &'a T where T: ToBytes);
deref_impl!(<'a, T: ?Sized> ToBytes for &'a mut T where T: ToBytes);
deref_impl!(<T: ?Sized> ToBytes for Box<T> where T: ToBytes);

