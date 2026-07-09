# #466 R360 — reinterpretation: one prime ideal, many short vectors

The ten six-web orbit representatives have equal resultant but are not
associates as polynomials over `ℚ`. The correct algebraic interpretation is
therefore not “ten equivalent templates.” They are distinct short vectors in
the same finite-index cyclotomic kernel/prime ideal modulo `p`.

Concretely, each signed exponent polynomial evaluates to zero at the same
primitive order-64 element in `F_p`, and each norm is `2^3 p`. The bad prime
creates one kernel lattice of index controlled by `p`; the ten affine web types
are short lattice vectors inside that one lattice.

This reconnects R358 directly to R322/R323: the right global theorem is a
short-vector/return-probability bound for a prime ideal, not a union bound over
all six-term resultants. Geometry-of-numbers, successive minima, or a transfer
operator on the ideal’s short-vector graph are the natural tools. A single
ideal can contain many short vectors, so resultant counting alone cannot see
the multiplicity that drives the moment excess.
