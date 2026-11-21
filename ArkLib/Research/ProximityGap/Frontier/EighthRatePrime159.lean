/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuadraticTwoHeadThreshold
import ArkLib.Research.ProximityGap.Support.BinaryPower
import ArkLib.Research.ProximityGap.Support.DyadicPowerDomain
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-! # A smooth rate-one-eighth code with 128-bit MCA cutoff above one half

The prime 139619·2^141+1 supplies enough scalars to cross the two-head
budget at 571879424 errors on every domain of length 2^30.
-/
set_option autoImplicit false
namespace ProximityGap.EighthRatePrime159
open MCAThresholdLedger
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)
open scoped NNReal ENNReal

/-- A prime of the form 139619·2¹⁴¹+1. -/
abbrev p : ℕ := 389200967984205884049759431188611448137934962689

set_option maxRecDepth 100000 in
/-- The Lucas certificate uses generator 3 and the two prime divisors 2 and 139619 of p−1. -/
theorem prime_p : p.Prime := by
  apply lucas_primality p 3 (by rw [← binaryPow_eq_pow]; decide)
  intro v hv hd
  rw [show p - 1 = 2 ^ 141 * 139619 by decide] at hd
  rcases hv.dvd_mul.mp hd with h | h
  · have heq := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp (hv.dvd_of_dvd_pow h)
    subst v
    rw [← binaryPow_eq_pow]
    decide
  · have heq := (Nat.prime_dvd_prime_iff_eq hv (by norm_num : Nat.Prime 139619)).mp h
    subst v
    rw [← binaryPow_eq_pow]
    decide

instance : Fact p.Prime := ⟨prime_p⟩

/-- Fixed nonzero generator of the evaluation subgroup. -/
def generator : (ZMod p)ˣ := Units.mk0 382733111260874176310205324238922864095590508475 (by decide)

set_option maxRecDepth 100000 in
theorem generator_order : orderOf generator = 2 ^ 30 := by
  rw [← orderOf_units]
  apply orderOf_eq_prime_pow (p := 2) (n := 29) <;> rw [← binaryPow_eq_pow] <;> decide

/-- The domain sends i to the i-th power of the specified generator. -/
def domain : Fin (2 ^ 30) ↪ ZMod p := MCADeltaStarLiteralEps.smoothDom p generator generator_order

/-- The explicit power domain satisfies the canonical smoothness predicate. -/
noncomputable instance smooth : ReedSolomon.Smooth domain :=
  DyadicPowerDomain.smooth generator generator_order

/-- Every embedding, including the displayed subgroup and each of its cosets,
has precisely the indicated good real radii at every positive width. -/
theorem classification (x : Fin 1073741824 ↪ ZMod p) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x 134217728 : Set (Fin 1073741824 → ZMod p)) ^⋈ (Fin width)
    let b := (571879424:ℝ≥0)/1073741824
    mcaDeltaStar (F:=ZMod p) C (1/2^128) = b ∧ ∀ δ, epsMCA (F:=ZMod p) C δ≤1/2^128 ↔ δ<b :=
  QuadraticTwoHeadThreshold.production_eighth (B:=1143758848) x (by decide) (by decide) (by decide) width

end ProximityGap.EighthRatePrime159
#print axioms ProximityGap.EighthRatePrime159.prime_p
#print axioms ProximityGap.EighthRatePrime159.smooth
#print axioms ProximityGap.EighthRatePrime159.classification
