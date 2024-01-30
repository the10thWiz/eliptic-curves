//
// eliptic_curve.rs
// Copyright (C) 2022 matthew <matthew@WINDOWS-05HIC4F>
// Distributed under terms of the MIT license.
//

use std::{fmt::Debug, str::FromStr};

use lazy_static::lazy_static;
use num_bigint::{BigInt, BigUint};

use crate::modulus::{ModN, PrimeMod, N_101};

macro_rules! impl_op {
    (CPt, $op:ident, $fn:ident, $mod:ident, $lhs:ident, $rhs:ident => $code: expr) => {
        impl<$mod: MontgomeryCurve> $op<CurvePoint<$mod>> for CurvePoint<$mod> {
            type Output = CurvePoint<$mod>;
            fn $fn(self, $rhs: CurvePoint<$mod>) -> Self::Output {
                let $lhs = self;
                $code
            }
        }
        impl<$mod: MontgomeryCurve> $op<CurvePoint<$mod>> for &CurvePoint<$mod> {
            type Output = CurvePoint<$mod>;
            fn $fn(self, $rhs: CurvePoint<$mod>) -> Self::Output {
                let $lhs = self;
                $code
            }
        }
        impl<$mod: MontgomeryCurve> $op<&CurvePoint<$mod>>
            for &CurvePoint<$mod>
        {
            type Output = CurvePoint<$mod>;
            fn $fn(self, $rhs: &CurvePoint<$mod>) -> Self::Output {
                let $lhs = self;
                $code
            }
        }
        impl<$mod: MontgomeryCurve> $op<&CurvePoint<$mod>> for CurvePoint<$mod> {
            type Output = CurvePoint<$mod>;
            fn $fn(self, $rhs: &CurvePoint<$mod>) -> Self::Output {
                let $lhs = self;
                $code
            }
        }
    };
}

pub trait MontgomeryCurve: Sized {
    type M: PrimeMod;
    fn on_curve(pt: &CurvePoint<Self>) -> bool;
    fn add_pts(lhs: &CurvePoint<Self>, rhs: &CurvePoint<Self>) -> CurvePoint<Self>;
}

pub enum CurvePoint<C: MontgomeryCurve> {
    Pt(ModN<C::M>),
    Inf,
}

impl<C: MontgomeryCurve> CurvePoint<C> {
    pub fn new(num: impl Into<BigUint>) -> Self {
        Self::Pt(ModN::new(num))
    }

    #[doc(hidden)]
    pub fn new_mod(num: ModN<C::M>) -> Self {
        Self::Pt(num)
    }

    pub fn inf() -> Self {
        Self::Inf
    }

    pub fn x(&self) -> Option<&ModN<C::M>> {
        match self {
            Self::Pt(x) => Some(x),
            Self::Inf => None,
        }
    }

    pub fn montgomery_ladder(self, rhs: BigUint) -> Self {
        let mut r0 = self;
        let mut r1 = &r0 + &r0;
        // Most sig bit MUST be one, three least should be zero
        for i in (rhs.bits() - 1)..=0 {
            if rhs.bit(i) {
                r1 = &r0 + &r1;
                r0 = &r0 + &r0;
            } else {
                r0 = &r0 + &r1;
                r1 = &r1 + &r1;
            }
        }
        r0
    }
}

#[test]
fn test_bits() {
    let t = BigUint::from(0b01101u8);
    assert_eq!(t.bits(), 4);
    assert_eq!(t.bit(3), true);
    assert_eq!(t.bit(2), true);
    assert_eq!(t.bit(1), false);
    assert_eq!(t.bit(0), true);
}

use std::ops::{Add, Mul, Neg};

impl_op!(CPt, Add, add, C, lhs, rhs => C::add_pts(&lhs, &rhs));
macro_rules! for_each {
    ($($t:ty $(,)?)*) => {
        $(
            impl<C: MontgomeryCurve> Mul<$t> for CurvePoint<C> {
                type Output = CurvePoint<C>;
                fn mul(self, mut rhs: $t) -> Self::Output {
                    rhs -= <$t>::from(1u8);
                    let mut ret = self.clone();
                    while rhs > <$t>::from(0u8) {
                        ret = ret + &self;
                        rhs -= <$t>::from(1u8);
                    }
                    ret
                }
            }
            impl<C: MontgomeryCurve> Mul<$t> for &CurvePoint<C> {
                type Output = CurvePoint<C>;
                fn mul(self, mut rhs: $t) -> Self::Output {
                    rhs -= <$t>::from(1u8);
                    let mut ret = self.clone();
                    while rhs > <$t>::from(0u8) {
                        ret = ret + self;
                        rhs -= <$t>::from(1u8);
                    }
                    ret
                }
            }
        )*
    };
}
for_each!(u8, u16, u32, u64);

impl<C: MontgomeryCurve> Neg for CurvePoint<C> {
    type Output = CurvePoint<C>;
    fn neg(self) -> Self::Output {
        match self {
            Self::Inf => Self::Inf,
            Self::Pt(x) => Self::Pt(x),
        }
    }
}
impl<C: MontgomeryCurve> Neg for &CurvePoint<C> {
    type Output = CurvePoint<C>;
    fn neg(self) -> Self::Output {
        match self {
            CurvePoint::Inf => CurvePoint::Inf,
            CurvePoint::Pt(x) => CurvePoint::Pt(x.clone()),
        }
    }
}

#[macro_export]
macro_rules! montgomery_curve {
    ($v:vis $name:ident { a: $a:literal, base: $b: literal, mod: $m:literal }) => {
        $crate::prime_mod!(INNER => $m);
        montgomery_curve!($v $name { a: $a, base: $b, mod: INNER });
    };
    ($v:vis $name:ident { a: $a:literal, base: $b:literal, mod: $m:ty }) => {
        $v struct $name;
        impl $name {
            fn get_a() -> &'static $crate::modulus::ModN<$m> {
                use std::str::FromStr;
                lazy_static::lazy_static! {
                    pub static ref A: $crate::modulus::ModN<$m> =
                        $crate::modulus::ModN::new(
                            $crate::modulus::BigUint::from_str(concat!($a)).unwrap()
                        );
                }
                &*A
            }

            fn get_base() -> &'static $crate::eliptic_curve::CurvePoint<Self> {
                use std::str::FromStr;
                lazy_static::lazy_static! {
                    pub static ref A: $crate::eliptic_curve::CurvePoint<$name> =
                        $crate::eliptic_curve::CurvePoint::new(
                                $crate::modulus::BigUint::from_str(concat!($a)).unwrap()
                        );
                }
                &*A
            }
        }

        impl $crate::eliptic_curve::MontgomeryCurve for $name {
            type M = $m;
            fn on_curve(pt: &$crate::eliptic_curve::CurvePoint<Self>) -> bool {
                todo!()
            }

            fn add_pts(
                p: &$crate::eliptic_curve::CurvePoint<Self>,
                q: &$crate::eliptic_curve::CurvePoint<Self>
            ) -> $crate::eliptic_curve::CurvePoint<Self> {
                use $crate::eliptic_curve::CurvePoint;
                use $crate::modulus::ModN;
                match (p.x(), q.x()) {
                    (None, None) => CurvePoint::inf(),
                    (Some(x), None) | (None, Some(x)) => CurvePoint::new_mod(x.clone()),
                    (Some(mx), Some(nx)) => {
                        if mx == nx {
                            let x = (mx*mx - ModN::new(1u8)).pow(2u8.into());
                            let z = ModN::new(4u8) * mx * mx * (mx*mx + Self::get_a() * mx + ModN::new(1u8)).pow(2u8.into());
                            CurvePoint::new_mod(x / z)
                        } else {
                            let x = (nx * mx - ModN::new(1u8)).pow(2u8.into());
                            let z = (nx - mx).pow(2u8.into());
                            //let inv = (mx - nx).mul_inverse();
                            //let slope = (todo!()) / (mx - nx);
                            todo!()
                        }
                    },
                }
            }
        }
    };
}

#[macro_export]
macro_rules! montgomery_curve2 {
    ($v:vis $name:ident { a: $a:literal, base: $b: literal, mod: $m:literal }) => {
        $crate::prime_mod!(INNER => $m);
        montgomery_curve2!($v $name { a: $a, base: $b, mod: INNER });
    };
    ($v:vis $name:ident { a: $a:literal, base: $b:literal, mod: $m:ty }) => {
        $v struct $name;
        impl $name {
            fn get_a() -> &'static $crate::modulus::ModN<$m> {
                use std::str::FromStr;
                lazy_static::lazy_static! {
                    pub static ref A: $crate::modulus::ModN<$m> =
                        $crate::modulus::ModN::new(
                            $crate::modulus::BigUint::from_str(concat!($a)).unwrap()
                        );
                }
                &*A
            }

            fn get_base() -> &'static $crate::eliptic_curve::CurvePoint<Self> {
                use std::str::FromStr;
                lazy_static::lazy_static! {
                    pub static ref A: $crate::eliptic_curve::CurvePoint<$name> =
                        $crate::eliptic_curve::CurvePoint::new(
                                $crate::modulus::BigUint::from_str(concat!($a)).unwrap()
                        );
                }
                &*A
            }
        }

        impl $crate::modulus::ElipticCurve for $name {
            type M = $m;
            fn on_curve(pt: &$crate::modulus::CurvePoint<Self>) -> bool {
                todo!()
            }

            fn add_pts(
                p: &$crate::modulus::CurvePoint<Self>,
                q: &$crate::modulus::CurvePoint<Self>
            ) -> $crate::modulus::CurvePoint<Self> {
                use $crate::modulus::{CurvePoint, ModN};
                match (p.coords(), q.coords()) {
                    (None, None) => CurvePoint::inf(),
                    (Some((x, z)), None) | (None, Some((x, z))) => unsafe { CurvePoint::new_unchecked(x.clone(), z.clone()) },
                    (Some((mx, mz)), Some((nx, nz))) => {
                        if mx == nx && mz == nz {
                            let x = (mx*mx - mz*mz).pow(2u8.into());
                            let z = ModN::new(4u8) * mx * mx * mz * (mx*mx + Self::get_a() * mx * mz + mz).pow(2u8.into());
                            unsafe { CurvePoint::new_unchecked(x, z) }
                        } else {
                            let x = (nx * mx - mz * nz).pow(2u8.into());
                            let z = (mx * nz - nx * mz).pow(2u8.into());
                            unsafe { CurvePoint::new_unchecked(x, z) }
                        }
                    },
                }
            }
        }
    };
}

mod derives {
    use super::*;
    use std::fmt::{Display, Debug};

    impl<E: MontgomeryCurve> Debug for CurvePoint<E> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Pt(x) => write!(f, "({:?})", x),
                Self::Inf => write!(f, "(inf)"),
            }
        }
    }
    impl<E: MontgomeryCurve> Display for CurvePoint<E> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Pt(x) => write!(f, "({:?})", x),
                Self::Inf => write!(f, "(inf)"),
            }
        }
    }

    impl<E: MontgomeryCurve> Clone for CurvePoint<E> {
        fn clone(&self) -> Self {
            match self {
                Self::Pt(x) => Self::Pt(x.clone()),
                Self::Inf => Self::Inf,
            }
        }
    }

    impl<E: MontgomeryCurve> PartialEq for CurvePoint<E> {
        fn eq(&self, rhs: &Self) -> bool {
            match (self, rhs) {
                (Self::Inf, Self::Inf) => true,
                (Self::Pt(lx), Self::Pt(rx)) => lx == rx,
                _ => false,
            }
        }
    }
    impl<E: MontgomeryCurve> Eq for CurvePoint<E> {}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        println!("Hello!");
    }

    // If gcd(the product of the two private keys, P - 1) != 1, then the shared secret will be 1
    //
    // We choose germain primes (p if 2p+1 is also prime) to minimize this chance. We choose the
    // 2p+1, since the only possible orders of a memeber of (2p+1) are 1, 2, p, and 2p+1. The
    // number with order 1 is 1, so we just need a number that isn't divisible 2 or p.
    //
    // Actually, a number divisible by p might be okay?

    #[test]
    fn diffie() {
        let prime = BigUint::from_str("199679").unwrap();
        let private_key_a = 10000u64.into();
        let public_key_a = BigUint::from(2u64).modpow(&private_key_a, &prime);
        let private_key_b = 20480u64.into();
        let public_key_b = BigUint::from(2u64).modpow(&private_key_b, &prime);

        let a_shared = public_key_b.modpow(&private_key_a, &prime);
        let b_shared = public_key_a.modpow(&private_key_b, &prime);
        assert_eq!(a_shared, b_shared);
    }
}
