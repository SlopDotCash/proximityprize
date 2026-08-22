/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-!
# R317 (#466): constructive algebra for the large `c = 3` relation-web fibers

The R310/R311 histogram for a dangerous `c = 3` relation web has a large
signature `(3n - 3, 3, 1)`.  Its field-theoretic core is much simpler than the
remaining combinatorial classification: if `ζ ^ h = 3` and
`ζ ^ m = -1`, then the complementary exponent `k = m - h` satisfies
`3 * ζ ^ k = -1`.  Consequently, for every translate `t`, the three template
values

```text
-ζ^t,  2ζ^t - ζ^(t+h),  3ζ^(t+k)
```

coalesce exactly.  This file proves that constructive half of the large-fiber
law.  It deliberately does not assert the unproved representation multiplicity
or exhaustivity statements needed for the full R311 histogram.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R317C3LargeFiberConstruction

variable {F : Type*} [Field F]

/-- The exponent complementary to a `c = 3` relation converts `3` into the
half-turn `-1`. -/
theorem three_mul_complementary_pow_eq_neg_one
    {ζ : F} {h k m : ℕ}
    (hhalfTurn : ζ ^ m = -1)
    (hThree : ζ ^ h = 3)
    (hcomplement : k + h = m) :
    (3 : F) * ζ ^ k = -1 := by
  calc
    (3 : F) * ζ ^ k = ζ ^ k * (3 : F) := by ring
    _ = ζ ^ k * ζ ^ h := by rw [hThree]
    _ = ζ ^ (k + h) := (pow_add ζ k h).symm
    _ = ζ ^ m := by rw [hcomplement]
    _ = -1 := hhalfTurn

/-- The three explicit large-fiber templates attached to every translate `t`
of a `c = 3` relation have the same value. -/
theorem c3_large_fiber_coalesces
    {ζ : F} {h k m t : ℕ}
    (hhalfTurn : ζ ^ m = -1)
    (hThree : ζ ^ h = 3)
    (hcomplement : k + h = m) :
    -ζ ^ t = (2 : F) * ζ ^ t - ζ ^ (t + h) ∧
      -ζ ^ t = (3 : F) * ζ ^ (t + k) := by
  constructor
  · calc
      -ζ ^ t = (2 : F) * ζ ^ t - ζ ^ t * (3 : F) := by ring
      _ = (2 : F) * ζ ^ t - ζ ^ t * ζ ^ h := by rw [hThree]
      _ = (2 : F) * ζ ^ t - ζ ^ (t + h) := by rw [pow_add]
  · have hcomplementary : (3 : F) * ζ ^ k = -1 :=
      three_mul_complementary_pow_eq_neg_one hhalfTurn hThree hcomplement
    calc
      -ζ ^ t = ζ ^ t * (-1) := by ring
      _ = ζ ^ t * ((3 : F) * ζ ^ k) := by rw [hcomplementary]
      _ = (3 : F) * ζ ^ (t + k) := by rw [pow_add]; ring

/-- One of the three one-parameter small-fiber families is already forced by
the complementary `c = 3` relation. -/
theorem c3_small_fiber_coalesces
    {ζ : F} {k t : ℕ}
    (hcomplementary : (3 : F) * ζ ^ k = -1) :
    1 + ζ ^ t + ζ ^ k = ζ ^ t - (2 : F) * ζ ^ k := by
  have hone : (1 : F) = -((3 : F) * ζ ^ k) := by
    rw [hcomplementary]
    norm_num
  rw [hone]
  ring

/-- The small-fiber identity follows from the same half-turn and `ζ ^ h = 3`
assumptions as the large-fiber identity. -/
theorem c3_small_fiber_coalesces_of_half_turn
    {ζ : F} {h k m t : ℕ}
    (hhalfTurn : ζ ^ m = -1)
    (hThree : ζ ^ h = 3)
    (hcomplement : k + h = m) :
    1 + ζ ^ t + ζ ^ k = ζ ^ t - (2 : F) * ζ ^ k :=
  c3_small_fiber_coalesces
    (three_mul_complementary_pow_eq_neg_one hhalfTurn hThree hcomplement)

/-- The small-fiber collision persists under every multiplicative translate.
This is the raw two-parameter family whose nondegenerate parameter slice is
observed to account for the complete `(6,3)` stratum. -/
theorem c3_small_fiber_coalesces_translated
    {ζ : F} {k s t : ℕ}
    (hcomplementary : (3 : F) * ζ ^ k = -1) :
    ζ ^ s + ζ ^ (s + t) + ζ ^ (s + k)
      = ζ ^ (s + t) - (2 : F) * ζ ^ (s + k) := by
  calc
    ζ ^ s + ζ ^ (s + t) + ζ ^ (s + k)
        = ζ ^ s * (1 + ζ ^ t + ζ ^ k) := by rw [pow_add, pow_add]; ring
    _ = ζ ^ s * (ζ ^ t - (2 : F) * ζ ^ k) := by
      rw [c3_small_fiber_coalesces hcomplementary]
    _ = ζ ^ (s + t) - (2 : F) * ζ ^ (s + k) := by rw [pow_add, pow_add]; ring

/-- Distinct exponents give distinct large-fiber centers.  Combined with
`c3_large_fiber_coalesces`, this supplies the algebraic distinctness half of
the `n` large collision fibers; the remaining representation multiplicities
are a separate finite-combinatorial task. -/
theorem c3_large_centers_injective {n : ℕ} {ζ : F}
    (hprim : IsPrimitiveRoot ζ n) :
    Function.Injective (fun t : Fin n => -ζ ^ (t : ℕ)) := by
  intro i j hij
  apply Fin.ext
  exact hprim.pow_inj i.isLt j.isLt (neg_injective hij)

end ArkLib.ProximityGap.Frontier.R317C3LargeFiberConstruction

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R317C3LargeFiberConstruction.three_mul_complementary_pow_eq_neg_one
#print axioms ArkLib.ProximityGap.Frontier.R317C3LargeFiberConstruction.c3_large_fiber_coalesces
#print axioms ArkLib.ProximityGap.Frontier.R317C3LargeFiberConstruction.c3_small_fiber_coalesces
#print axioms
  ArkLib.ProximityGap.Frontier.R317C3LargeFiberConstruction.c3_small_fiber_coalesces_of_half_turn
#print axioms
  ArkLib.ProximityGap.Frontier.R317C3LargeFiberConstruction.c3_small_fiber_coalesces_translated
#print axioms ArkLib.ProximityGap.Frontier.R317C3LargeFiberConstruction.c3_large_centers_injective
