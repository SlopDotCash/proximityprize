/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Research.ProximityGap.Frontier.ManyHeadLocatorMass
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonPuncture
import ArkLib.Research.ProximityGap.Frontier.SmoothPowerMcaDescent

/-! # Opposite 128-bit list and MCA verdicts past Johnson at the production length

At 379625061 agreements the punctured intersection estimate gives a uniform
list cap. Three polynomial heads with a common locator attain a strictly higher
MCA numerator. A prime between the associated security cutoffs admits every
dyadic domain size through 2^30.
-/

namespace ProximityGap.ProductionBeyondJohnsonListMca

open scoped NNReal ENNReal
open ArkLib.ProximityGap.Frontier

/-- A common security budget interval for all length-2³⁰ domains in the field. -/
def Window (p : ℕ) : Prop := 1660990722 ≤ p/2^128 ∧ p/2^128 < 2082350292

/-- Numerical strictness against the finite Johnson agreement count. -/
theorem strictly_beyond_johnson : (379625061 : ℕ)^2 < 1073741824*(134217728-1) := by decide

/-- Both predicates use the same field, evaluation domain, dimension and error count. -/
def Separated {p : ℕ} [Fact p.Prime] (D : Fin 1073741824 ↪ ZMod p) : Prop :=
  (∀ m, InterleavedListJohnsonRank.AtErrors D m 134217728 694116763 (p/2^128)) ∧
  1 / (2^128 : ℝ≥0∞) < epsMCA (F := ZMod p)
    (ReedSolomon.code D 134217728 : Set (Fin 1073741824 → ZMod p))
    (694116763/1073741824)

/-- Every prime in the interval has an actual MCA error above tolerance even
though every closed interleaved list lies within tolerance on every domain. -/
theorem all_domains {p : ℕ} [Fact p.Prime] (D : Fin 1073741824 ↪ ZMod p)
    (hw : Window p) : Separated D := by
  have hp : 1660990722 * 2^128 ≤ p :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 2^128)).mp hw.1
  have hm := ManyHeadLocatorMass.mass D (694116763/1073741824)
    (h := 32566678) (d := 2) (r := 347058382) (k := 134217728)
    (by decide) (by decide) (by decide) (by norm_num [tsub_mul, div_mul_cancel₀])
    ((by decide : 2*2+3 ≤ 1660990722*2^128).trans hp)
    ((by rw [Nat.choose_two_right]; decide :
      ((2+1)*2*347058382).choose 2 ≤ 1660990722*2^128).trans hp)
  refine ⟨fun m => (InterleavedListJohnsonPuncture.eighth_below_johnson D m).trans
    (by exact_mod_cast hw.1), lt_of_lt_of_le ?_ hm⟩
  apply lt_of_not_ge
  intro h
  rw [show (2+1)*2*347058382 = 2082350292 by decide] at h
  apply (not_le_of_gt hw.2)
  exact (BoundarySecurityBudget.count_ratio_le_iff (a := 2082350292) (D := 2^128)
    (Fact.out (p := p.Prime)).pos (by decide)).mp
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using h)

/-- The modulus with factorization p−1 = 2¹⁵⁰·3³·17. -/
abbrev P : ℕ := 459*2^150+1

set_option maxRecDepth 10000 in
theorem prime_P : Nat.Prime P := by
  have hmain : (5 : ZMod P)^(P-1) = 1 := by
    rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]; decide
  apply lucas_primality P 5 hmain
  intro v hv hd
  rw [show P-1 = 2^150*(3^3*17) by decide] at hd
  rcases hv.dvd_mul.mp hd with h2 | hr
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp (hv.dvd_of_dvd_pow h2)
    rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]; decide
  rcases hv.dvd_mul.mp hr with h3 | h17
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_three).mp (hv.dvd_of_dvd_pow h3)
    rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]; decide
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 17)).mp h17
    rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]; decide

instance : Fact P.Prime := ⟨prime_P⟩

theorem budget : P/2^128 = 1925185536 := by decide

/-- A concrete smooth production-length prime-field domain with a strict
beyond-Johnson list pass and a simultaneous strict MCA failure. -/
theorem smooth_example : ∃ D : Fin 1073741824 ↪ ZMod P,
    Nonempty (ReedSolomon.Smooth D) ∧ Separated D := by
  obtain ⟨D, hD⟩ := SmoothPowerMcaDescent.exists_prime_domain (p := P) (n := 1073741824)
    (by decide) ⟨30, by decide⟩
  exact ⟨D, hD, all_domains D (by unfold Window; rw [budget]; decide)⟩

/-- On the explicit prime, the two security verdicts differ on 52,388,251
consecutive error counts. The upper end is strictly beyond Johnson. -/
theorem separated_interval (D : Fin 1073741824 ↪ ZMod P) (e m : ℕ)
    (hlo : 641728513 ≤ e) (hhi : e ≤ 694116763) :
    InterleavedListJohnsonRank.AtErrors D m 134217728 e (P/2^128) ∧
    1 / (2^128 : ℝ≥0∞) < epsMCA (F := ZMod P)
      (ReedSolomon.code D 134217728 : Set (Fin 1073741824 → ZMod P)) ((e : ℝ≥0)/1073741824) := by
  have hupper := (all_domains D (by unfold Window; rw [budget]; decide)).1 m
  have he : (e : ℝ) / 1073741824 ≤ 694116763/1073741824 :=
    div_le_div_of_nonneg_right (by exact_mod_cast hhi) (by norm_num)
  refine ⟨(Code.Lambda_mono he).trans hupper, ?_⟩
  have hmass := ManyHeadLocatorMass.mass D (641728513/1073741824)
    (h := 111149053) (d := 2) (r := 320864257) (k := 134217728)
    (by decide) (by decide) (by decide) (by norm_num [tsub_mul, div_mul_cancel₀])
    (by decide) (by rw [Nat.choose_two_right]; decide)
  have hbad : 1 / (2^128 : ℝ≥0∞) < (1925185542 : ℝ≥0∞)/P := by
    apply lt_of_not_ge
    intro h
    exact (by decide : ¬1925185542 ≤ P/2^128)
      ((BoundarySecurityBudget.count_ratio_le_iff (a := 1925185542) (q := P)
        (D := 2^128) (by decide) (by decide)).mp
        (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using h))
  rw [show (2+1)*2*320864257 = 1925185542 by decide] at hmass
  exact (hbad.trans_le hmass).trans_le (epsMCA_mono _
    (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (by norm_num)))

#print axioms separated_interval
#print axioms all_domains
#print axioms prime_P
#print axioms smooth_example

end ProximityGap.ProductionBeyondJohnsonListMca
