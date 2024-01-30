//
// montgomery.rs
// Copyright (C) 2022 matthew <matthew@WINDOWS-05HIC4F>
// Distributed under terms of the MIT license.
//


pub struct FixedModN<const LEN: usize>([u64; LEN / 4]);

pub trait GroupMember {
	fn zero() -> Self;
	fn add(&self, other: &Self) -> Self;
	fn double(&self) -> Self;
}

pub fn montgomery_ladder<B: GroupMember>(base: B, n: &BigUint) -> B {
	let r0 = B::zero();
	let r1 = base;
	let len = n.bits();
	for i in len - 1..=0 {
		if n.bit(i) {
			r0 = r0.add(r1);
			r1 = r1.double();
		} else {
			r1 = r0.add(r1);
			r0 = r0.double();
		}
	}
	r0
}

struct MN(BigUint);
impl GroupMember for MN {
	fn zero() -> Self {
		Self(BigUint::from(0u8))
	}
	fn double(&self) -> Self {
		Self(self.0.pow(2))
	}
	fn add(&self, other: &Self) -> Self {
		Self(self.0 * other.0)
	}
}


#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn it_works() {
	}
}
