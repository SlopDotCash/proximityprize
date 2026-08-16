/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
# Primitive 2-power root: the half-period power is `-1`

For a commutative ring `R` with no zero divisors and `ζ : R` with
`IsPrimitiveRoot ζ (2^(k+1))`, we have `ζ^(2^k) = -1`.

(The `NoZeroDivisors` hypothesis is genuinely needed: `mul_self_eq_one_iff` — "a square
root of `1` is `±1`" — fails in rings with nilpotents, and the in-tree consumer always
works over a field/domain `L`.)

This is the precise hinge of the 2-adic antipodal engine ("the only minimal vanishing
relation is `ζ + (-ζ) = 0`" when 2 is the sole ramified prime). It is reproved inline as
`hhalf` in `LamLeungMultisetAntipodal`, and the caller of
`LamLeungTwoPower.antipodal_shift` / `eval_dvd_eq_zero` currently must supply
`hζ : ζ^h = -1` by hand. With this lemma the antipodal engine becomes self-contained
from primitivity alone.

SOURCE: novel (Lean formalization gap; elementary consequence of `ζ^(2^{k+1})=1` and
primitivity). No one-shot `exact?` in Mathlib.

PROOF: let `s = ζ^(2^k)`. Then `s*s = ζ^(2^{k+1}) = 1`, so `mul_self_eq_one_iff` gives
`s = 1 ∨ s = -1`. Rule out `s = 1`: `orderOf ζ = 2^(k+1)` (primitivity), but `s = 1`
would give `orderOf ζ ∣ 2^k`, contradicting `2^k < 2^(k+1)` via `Nat.le_of_dvd`.
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace ArkLib.ProximityGap.Frontier

open scoped Classical

/-- For a primitive `2^(k+1)`-th root of unity `ζ` in a commutative ring, the half-period
power `ζ^(2^k)` equals `-1`. -/
theorem PrimitiveTwoPowRootHalfPowerEqNegOne
    {R : Type*} [CommRing R] [NoZeroDivisors R] {ζ : R} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) :
    ζ ^ (2 ^ k) = -1 := by
  haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
  have hsq : (ζ ^ (2 ^ k)) * (ζ ^ (2 ^ k)) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    exact hζ.pow_eq_one
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · exfalso
    have hdvd : orderOf ζ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    have hord : orderOf ζ = 2 ^ (k + 1) := hζ.eq_orderOf.symm
    rw [hord] at hdvd
    have hle := Nat.le_of_dvd (by positivity) hdvd
    have hlt : (2 : ℕ) ^ k < 2 ^ (k + 1) := by
      rw [pow_succ]; omega
    omega
  · exact h1

#print axioms PrimitiveTwoPowRootHalfPowerEqNegOne

end ArkLib.ProximityGap.Frontier
