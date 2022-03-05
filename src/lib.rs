

pub mod modulus;
//pub mod eliptic_curve;

pub use modulus::{ModN, ElipticCurve, CurvePoint};


#[cfg(test)]
mod tests {
    use crate::{weierstrass_curve, CurvePoint};

    #[test]
    fn test_curve() {
        weierstrass_curve!(pub TestCurve { a: 0, b: 1, mod: 101 });
        let p = CurvePoint::<TestCurve>::new(38u64.into(), 38u64.into()).unwrap();

        assert_eq!(&p + &p, CurvePoint::new(42u64.into(), 37u64.into()).unwrap(), "Point did not match");
        assert_eq!(&p * 2u8, CurvePoint::new(42u64.into(), 37u64.into()).unwrap(), "Point did not match");
        assert_eq!(&p * 3u8, CurvePoint::new(40u64.into(), 13u64.into()).unwrap(), "Point did not match");
    }
}
