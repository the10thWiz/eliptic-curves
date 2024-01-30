

pub mod modulus;
pub mod eliptic_curve;

pub use modulus::{ModN, ElipticCurve};


#[cfg(test)]
mod tests {
    use crate::{weierstrass_curve, montgomery_curve};

    #[test]
    fn test_curve() {
        use crate::modulus::CurvePoint;
        weierstrass_curve!(pub TestCurve { a: 0, b: 1, mod: 101 });
        let p = CurvePoint::<TestCurve>::new(38u64.into(), 38u64.into()).unwrap();

        assert_eq!(&p + &p, CurvePoint::new(42u64.into(), 37u64.into()).unwrap(), "Point did not match");
        assert_eq!(&p * 2u8, CurvePoint::new(42u64.into(), 37u64.into()).unwrap(), "Point did not match");
        assert_eq!(&p * 3u8, CurvePoint::new(40u64.into(), 13u64.into()).unwrap(), "Point did not match");

        let mut total = p.clone();
        for _ in 0..101 {
            println!("{}", total);
            total = total + &p;
        }
    }

    #[test]
    fn test_mongomery() {
        use crate::eliptic_curve::CurvePoint;
        montgomery_curve!(pub TestCurve { a: 1, base: 9, mod: 101 });
        let base = TestCurve::get_base();
        assert_eq!(base, &CurvePoint::new(9u64), "Wrong base point");
    }

    #[test]
    fn test_curve_25519() {
        use crate::eliptic_curve::CurvePoint;
        montgomery_curve!(pub Curve25519 {
            a: 1,
            base: 9,
            mod: "57896044618658097711785492504343953926634992332820282019728792003956564819949"
        });
        let base = Curve25519::get_base();
        assert_eq!(base, &CurvePoint::new(9u64), "Wrong base point");
        assert_eq!(base * 2u8, CurvePoint::new(9u64), "Doubling point doesn't work");
    }
//lazy_static! {
    //pub static ref CURVE_25519: ElipticCurve = ElipticCurve {
        //base_point: BigUint::from_str("9").unwrap(),
        //prime: BigUint::from_str(
            //"57896044618658097711785492504343953926634992332820282019728792003956564819949"
        //)
        //.unwrap(),
    //};
//}
}
