/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.CharP.Lemmas

/-!
# R323: the power-of-two cyclotomic polynomial is repeated-root modulo two

The dyadic saturation census points to the prime over two.  This file records its elementary
algebraic source: in characteristic two, `x^(2^k)+1 = (x+1)^(2^k)`.  Thus the reduction of
`x^(2^k)+1` has the sole root `1`, with full multiplicity `2^k`.

R324 shows that this repeated-root quotient has characters of normalized bias `1-2/a`; it
therefore does not itself provide a uniform spectral gap.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R323RepeatedRootCyclotomic

/-- Freshman's dream at every dyadic depth. -/
theorem pow_two_add_one_eq_repeated_root {R : Type*} [CommSemiring R] [CharP R 2]
    (x : R) (k : ℕ) :
    x ^ (2 ^ k) + 1 = (x + 1) ^ (2 ^ k) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [add_pow_char_pow x 1 2 k, one_pow]

#print axioms pow_two_add_one_eq_repeated_root

end ArkLib.ProximityGap.Frontier.R323RepeatedRootCyclotomic
