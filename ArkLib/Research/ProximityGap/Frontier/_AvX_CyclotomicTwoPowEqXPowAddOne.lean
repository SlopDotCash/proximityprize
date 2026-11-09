/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# `_AvX_CyclotomicTwoPowEqXPowAddOne`

The 2-power cyclotomic polynomial in closed binomial form:
`Φ_{2^{k+1}}(X) = X^{2^k} + 1` over any commutative ring `R`.

This supplies the "cyclotomic bridge" flagged (but assumed) in `LamLeungTwoPower.lean`'s
docstring — turning a stated dependency into an in-tree, axiom-clean lemma reusable across
every 2-power cyclotomic argument (`ConverseLamLeung2Power`, `NoExcessBindingRootSum`).

The proof specializes Mathlib's `cyclotomic_prime_pow_eq_geom_sum` at `p = 2`: the geometric
sum `∑ i ∈ range 2, (X^{2^k})^i = 1 + X^{2^k}`.
-/

namespace ProximityGap.Frontier

open Polynomial Finset

/-- **Closed binomial form of the 2-power cyclotomic polynomial.**
For any commutative ring `R` and `k : ℕ`,
`Φ_{2^{k+1}}(X) = X^{2^k} + 1`. -/
theorem CyclotomicTwoPowEqXPowAddOne (R : Type*) [CommRing R] (k : ℕ) :
    Polynomial.cyclotomic (2 ^ (k + 1)) R = X ^ (2 ^ k) + 1 := by
  rw [cyclotomic_prime_pow_eq_geom_sum (R := R) (p := 2) (n := k) Nat.prime_two]
  -- `∑ i ∈ range 2, (X^{2^k})^i = (X^{2^k})^0 + (X^{2^k})^1 = 1 + X^{2^k}`
  rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
  ring

#print axioms CyclotomicTwoPowEqXPowAddOne

end ProximityGap.Frontier
