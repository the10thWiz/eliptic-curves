# eliptic-curves

My implementation of eliptic curves in Rust, primarily for me to learn eliptic curves.

See the tests in lib.rs for an example on how this should be used. One goal of this
repository is to be entirely safe, and easy to use. The library should be written
in, and used with idiomatic Rust, which has lead to a few iteresting design decisions.

Specifically, I've chosen to create a `ModN` struct, which holds a BigUint, mod a
specific modulus. The modulus is a generic parameter, which provides a convient way
to enforce that operations can only be preformed between numbers using the same modulus.
The other advantage to having a `ModN` struct is that they are automatically reduced
as often as possible. The process for declaring a modulus is non-trivial, so I have
written a macro to make it easier. Similarly, points on the eliptic curves use a
generic parameter to specify which curve they are on, and there is a macro to create
the eliptic curve implementation.

## Features

- [x] Weierstrass form of eliptic curve
- [ ] Montgomery form
- [ ] Points with only the X parameter
