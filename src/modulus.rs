//
// modulus.rs
// Copyright (C) 2022 matthew <matthew@WINDOWS-05HIC4F>
// Distributed under terms of the MIT license.
//

use std::{
    cmp::Ordering,
    marker::PhantomData,
    ops::Neg,
    str::FromStr,
};

pub use num_bigint::BigUint;

pub trait PrimeMod {
    fn get_modulus() -> &'static BigUint;
}

lazy_static::lazy_static! {
    pub static ref N_17: BigUint = BigUint::from_str("17").unwrap();
}

#[macro_export]
macro_rules! prime_mod {
    ($name:ident => $num:literal $(, $($tt:tt)*)?) => {
        lazy_static::lazy_static! {
            pub static ref $name: $crate::modulus::BigUint = {
                let tmp = <$crate::modulus::BigUint as std::str::FromStr>::from_str(concat!($num)).unwrap();
                assert!($crate::modulus::is_prime(&tmp), "Prime Modulus {} isn't prime", tmp);
                tmp
            };
        }

        impl $crate::modulus::PrimeMod for $name {
            fn get_modulus() -> &'static $crate::modulus::BigUint {
                &*$name
            }
        }
        $(
            prime_mod!($($tt)*);
        )?
    };
    () => {};
}

prime_mod!(
    N_5 => "5",
    N_7 => "7",
    N_101 => "101",
    CURVE_25519_PRIME => "57896044618658097711785492504343953926634992332820282019728792003956564819949"
);

pub fn is_prime(num: &BigUint) -> bool {
    // TODO
    true
}

pub struct ModN<M: PrimeMod>(BigUint, PhantomData<M>);

#[allow(unused)]
fn gcd(m: BigUint, n: BigUint) -> BigUint {
    if m == 0u64.into() {
        n
    } else {
        gcd(n % &m, m)
    }
}

impl<M: PrimeMod> ModN<M> {
    pub fn mul_inverse(self) -> Self {
        // Since PrimeMod is prime, gcd(self, M) = 1
        self.pow(M::get_modulus() - BigUint::from(2u64))
    }

    pub fn pow(mut self, mut exp: BigUint) -> Self {
        let modulus = M::get_modulus();
        let mut product = BigUint::from(1usize);
        while exp > BigUint::from(0usize) {
            if exp.bit(0) {
                product = (product * &self.0) % modulus;
            }
            self.0 = self.0.pow(2) % modulus;
            exp = exp >> 1u64;
        }
        Self(product, PhantomData)
    }

    pub fn new(u: impl Into<BigUint>) -> Self {
        Self(u.into() % M::get_modulus(), PhantomData)
    }
}

macro_rules! impl_op {
    (ModN, $op:ident, $fn:ident, $mod:ident, $lhs:ident, $rhs:ident => $code: expr) => {
        impl<$mod: PrimeMod> $op<ModN<$mod>> for ModN<$mod> {
            type Output = ModN<$mod>;
            fn $fn(self, $rhs: ModN<$mod>) -> Self::Output {
                let $lhs = self;
                ModN($code, PhantomData)
            }
        }
        impl<$mod: PrimeMod> $op<ModN<$mod>> for &ModN<$mod> {
            type Output = ModN<$mod>;
            fn $fn(self, $rhs: ModN<$mod>) -> Self::Output {
                let $lhs = self;
                ModN($code, PhantomData)
            }
        }
        impl<$mod: PrimeMod> $op<&ModN<$mod>> for &ModN<$mod> {
            type Output = ModN<$mod>;
            fn $fn(self, $rhs: &ModN<$mod>) -> Self::Output {
                let $lhs = self;
                ModN($code, PhantomData)
            }
        }
        impl<$mod: PrimeMod> $op<&ModN<$mod>> for ModN<$mod> {
            type Output = ModN<$mod>;
            fn $fn(self, $rhs: &ModN<$mod>) -> Self::Output {
                let $lhs = self;
                ModN($code, PhantomData)
            }
        }
    };
    (CPt, $op:ident, $fn:ident, $mod:ident, $lhs:ident, $rhs:ident => $code: expr) => {
        impl<$mod: ElipticCurve> $op<CurvePoint<$mod>> for CurvePoint<$mod> {
            type Output = CurvePoint<$mod>;
            fn $fn(self, $rhs: CurvePoint<$mod>) -> Self::Output {
                let $lhs = self;
                $code
            }
        }
        impl<$mod: ElipticCurve> $op<CurvePoint<$mod>> for &CurvePoint<$mod> {
            type Output = CurvePoint<$mod>;
            fn $fn(self, $rhs: CurvePoint<$mod>) -> Self::Output {
                let $lhs = self;
                $code
            }
        }
        impl<$mod: ElipticCurve> $op<&CurvePoint<$mod>>
            for &CurvePoint<$mod>
        {
            type Output = CurvePoint<$mod>;
            fn $fn(self, $rhs: &CurvePoint<$mod>) -> Self::Output {
                let $lhs = self;
                $code
            }
        }
        impl<$mod: ElipticCurve> $op<&CurvePoint<$mod>> for CurvePoint<$mod> {
            type Output = CurvePoint<$mod>;
            fn $fn(self, $rhs: &CurvePoint<$mod>) -> Self::Output {
                let $lhs = self;
                $code
            }
        }
    };
}

use std::ops::{Add, Div, Mul, Sub};
impl_op!(ModN, Add, add, M, lhs, rhs => (&lhs.0 + &rhs.0) % M::get_modulus());
impl_op!(ModN, Sub, sub, M, lhs, rhs => (&lhs.0 + &(-rhs).0) % M::get_modulus());
impl_op!(ModN, Mul, mul, M, lhs, rhs => (&lhs.0 * &rhs.0) % M::get_modulus());
impl_op!(ModN, Div, div, M, lhs, rhs => (&lhs.0 * rhs.clone().mul_inverse().0) % M::get_modulus());

impl<M: PrimeMod> std::ops::Neg for ModN<M> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self(M::get_modulus() - self.0, PhantomData)
    }
}

impl<M: PrimeMod> std::ops::Neg for &ModN<M> {
    type Output = ModN<M>;
    fn neg(self) -> Self::Output {
        ModN(M::get_modulus() - &self.0, PhantomData)
    }
}

pub trait ElipticCurve: Sized {
    type M: PrimeMod;
    fn on_curve(pt: &CurvePoint<Self>) -> bool;
    fn add_pts(lhs: &CurvePoint<Self>, rhs: &CurvePoint<Self>) -> CurvePoint<Self>;
}

pub enum CurvePoint<E: ElipticCurve> {
    Pt(ModN<E::M>, ModN<E::M>, PhantomData<E>),
    Inf(PhantomData<E>),
}

#[derive(Debug)]
pub enum CurveError {
    PointNotOnCurve,
}

impl<E: ElipticCurve> CurvePoint<E> {
    pub fn new(x: BigUint, y: BigUint) -> Result<Self, CurveError> {
        let ret = Self::Pt(ModN::new(x), ModN::new(y), PhantomData);
        if E::on_curve(&ret) {
            Ok(ret)
        } else {
            Err(CurveError::PointNotOnCurve)
        }
    }

    pub fn new_zero() -> Self {
        Self::Inf(PhantomData)
    }

    pub unsafe fn new_unchecked(x: ModN<E::M>, y: ModN<E::M>) -> Self {
        Self::Pt(x, y, PhantomData)
    }

    pub fn x(&self) -> Option<&ModN<E::M>> {
        match self {
            Self::Pt(x, _y, _) => Some(x),
            Self::Inf(_) => None,
        }
    }

    pub fn y(&self) -> Option<&ModN<E::M>> {
        match self {
            Self::Pt(_x, y, _) => Some(y),
            Self::Inf(_) => None,
        }
    }

    pub fn coords(&self) -> Option<(&ModN<E::M>, &ModN<E::M>)> {
        match self {
            Self::Pt(x, y, _) => Some((x, y)),
            Self::Inf(_) => None,
        }
    }
}

impl_op!(CPt, Add, add, C, lhs, rhs => C::add_pts(&lhs, &rhs));
macro_rules! for_each {
    ($($t:ty $(,)?)*) => {
        $(
            impl<C: ElipticCurve> Mul<$t> for CurvePoint<C> {
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
            impl<C: ElipticCurve> Mul<$t> for &CurvePoint<C> {
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
for_each!(u8, u16, u32, u64, BigUint);

impl<C: ElipticCurve> Neg for CurvePoint<C> {
    type Output = CurvePoint<C>;
    fn neg(self) -> Self::Output {
        match self {
            Self::Inf(_) => Self::Inf(PhantomData),
            Self::Pt(x, y, _) => Self::Pt(x, -y, PhantomData),
        }
    }
}
impl<C: ElipticCurve> Neg for &CurvePoint<C> {
    type Output = CurvePoint<C>;
    fn neg(self) -> Self::Output {
        match self {
            CurvePoint::Inf(_) => CurvePoint::Inf(PhantomData),
            CurvePoint::Pt(x, y, _) => CurvePoint::Pt(x.clone(), -y, PhantomData),
        }
    }
}

#[macro_export]
macro_rules! weierstrass_curve {
    ($v:vis $name:ident { a: $a:literal, b: $b:literal, mod: $m:literal }) => {
        $crate::prime_mod!(INNER => $m);
        weienerstrass_curve!($v $name { a: $a, b: $b, mod: INNER });
    };
    ($v:vis $name:ident { a: $a:literal, b: $b:literal, mod: $m:ty }) => {
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
            fn get_b() -> &'static $crate::modulus::ModN<$m> {
                use std::str::FromStr;
                lazy_static::lazy_static! {
                    pub static ref B: $crate::modulus::ModN<$m> =
                        $crate::modulus::ModN::new(
                            $crate::modulus::BigUint::from_str(concat!($b)).unwrap()
                        );
                }
                &*B
            }
        }
        impl $crate::modulus::ElipticCurve for $name {
            type M = $m;
            fn on_curve(pt: &$crate::modulus::CurvePoint<Self>) -> bool {
                if let Some((x, y)) = pt.coords() {
                    y * y == x * x * x + x * Self::get_a() + Self::get_b()
                } else {
                    true
                }
            }

            fn add_pts(
                p: &$crate::modulus::CurvePoint<Self>,
                q: &$crate::modulus::CurvePoint<Self>
            ) -> $crate::modulus::CurvePoint<Self> {
                match (p.coords(), q.coords()) {
                    (Some((px, py)), Some((qx, qy))) => {
                        if px == qx {
                            if py == qy && py != &$crate::modulus::ModN::new(0u64) {
                                let s = ($crate::modulus::ModN::new(3u64) * px * px + Self::get_a())
                                    / ($crate::modulus::ModN::new(2u64) * py);
                                let rx = &s * &s - px - qx;
                                let ry = s * (&rx - px) + py;
                                unsafe {
                                    $crate::modulus::CurvePoint::new_unchecked(rx, -ry)
                                }
                            } else {
                                $crate::modulus::CurvePoint::new_zero()
                            }
                        } else {
                            let s = (qy - py) / (qx - px);
                            let rx = &s * &s - px - qx;
                            let ry = s * (&rx - px) + py;
                            unsafe {
                                $crate::modulus::CurvePoint::new_unchecked(rx, -ry)
                            }
                        }
                    }
                    (None, Some((px, py))) | (Some((px, py)), None) => unsafe {
                        $crate::modulus::CurvePoint::new_unchecked(px.clone(), py.clone())
                    },
                    (None, None) => $crate::modulus::CurvePoint::new_zero(),
                }
            }
        }
    };
}

//weienerstrass_curve!(pub TestCurve<N_101> => "0", "1");

mod derives {
    use super::*;
    use std::fmt::{Display, Debug};

    impl<M: PrimeMod> Clone for ModN<M> {
        fn clone(&self) -> Self {
            Self(self.0.clone(), PhantomData)
        }
    }

    impl<M: PrimeMod> PartialEq for ModN<M> {
        fn eq(&self, rhs: &Self) -> bool {
            self.0 == rhs.0
        }
    }
    impl<M: PrimeMod> Eq for ModN<M> {}

    impl<M: PrimeMod> PartialOrd for ModN<M> {
        fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
            self.0.partial_cmp(&rhs.0)
        }
    }
    impl<M: PrimeMod> Ord for ModN<M> {
        fn cmp(&self, rhs: &Self) -> Ordering {
            self.0.cmp(&rhs.0)
        }
    }

    impl<M: PrimeMod> Debug for ModN<M> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.0)
        }
    }
    impl<M: PrimeMod> Display for ModN<M> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    impl<E: ElipticCurve> Debug for CurvePoint<E> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Pt(x, y, _) => write!(f, "({:?}, {:?})", x, y),
                Self::Inf(_) => write!(f, "(inf)"),
            }
        }
    }
    impl<E: ElipticCurve> Display for CurvePoint<E> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Pt(x, y, _) => write!(f, "({:?}, {:?})", x, y),
                Self::Inf(_) => write!(f, "(inf)"),
            }
        }
    }

    impl<E: ElipticCurve> Clone for CurvePoint<E> {
        fn clone(&self) -> Self {
            match self {
                Self::Pt(x, y, _) => Self::Pt(x.clone(), y.clone(), PhantomData),
                Self::Inf(_) => Self::Inf(PhantomData),
            }
        }
    }

    impl<E: ElipticCurve> PartialEq for CurvePoint<E> {
        fn eq(&self, rhs: &Self) -> bool {
            match (self, rhs) {
                (Self::Inf(_), Self::Inf(_)) => true,
                (Self::Pt(lx, ly, _), Self::Pt(rx, ry, _)) => lx == rx && ly == ry,
                _ => false,
            }
        }
    }
    impl<E: ElipticCurve> Eq for CurvePoint<E> {}
}
