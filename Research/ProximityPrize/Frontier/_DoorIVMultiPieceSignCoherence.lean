/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Door IV multi-piece sign coherence: negation-stable refinements still reduce to signs

This file records a small axiom-clean constraint lemma for Shaw's door-(iv) localized coherence
object.  The raw index-2 split was already shown sign-degenerate in
`_DoorIVCosetHalfCoherence`: when the two half-period sums are real and have the same sign, the
coherence is exactly `1`.

The same obstruction is not special to two pieces.  Any refinement whose pieces are individually
negation-stable has real period sums, and if those real pieces all have one sign then the normalized
multi-piece coherence

`|∑ᵢ Aᵢ| / ∑ᵢ |Aᵢ|`

is exactly `1`.  Thus a door-(iv) anti-concentration theorem cannot get a nontrivial upper bound
merely by subdividing into more negation-stable cosets and hoping for automatic phase spread: on
same-sign fibers the statistic again saturates.  The companion probe
`scripts/probes/probe_dooriv_multipiece_sign_coherence.py` checks this for index `4` and `8` coset
refinements in the thin prize regime.  This is only a constraint lemma, not CORE and not a moment or
completion bound.
-/

open scoped BigOperators

namespace ProximityGap.Frontier.DoorIVMultiPieceSignCoherence

/-- Normalized coherence of finitely many real pieces. -/
noncomputable def multiPieceCoherence {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) : ℝ :=
  |∑ i ∈ s, A i| / (∑ i ∈ s, |A i|)

/-- The real multi-piece coherence statistic is always at most `1` when its `L¹` denominator is
positive.  This pins the trivial ceiling for refined door-(iv) splits: any useful statement must
be a strict subunit bound, and the later signed-mass lemmas identify exactly what pays for that strict
slack. -/
theorem multiPieceCoherence_le_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) (hpos : 0 < ∑ i ∈ s, |A i|) :
    multiPieceCoherence s A ≤ 1 := by
  unfold multiPieceCoherence
  exact (div_le_one hpos).mpr (Finset.abs_sum_le_sum_abs _ _)

/-- Nonnegativity of the real multi-piece coherence statistic. -/
theorem multiPieceCoherence_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) :
    0 ≤ multiPieceCoherence s A := by
  unfold multiPieceCoherence
  exact div_nonneg (abs_nonneg _)
    (Finset.sum_nonneg (fun i hi => abs_nonneg (A i)))

/-- The real multi-piece coherence lies in the closed unit interval whenever the denominator is
positive.  This is the exact ceiling/slack interface consumed by the sign-balance obstruction: the
only nontrivial content is moving from `≤ 1` to `≤ 1 - ε`. -/
theorem multiPieceCoherence_mem_Icc {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) (hpos : 0 < ∑ i ∈ s, |A i|) :
    multiPieceCoherence s A ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨multiPieceCoherence_nonneg s A, multiPieceCoherence_le_one s A hpos⟩

/-- If all real pieces are nonnegative and the total is nonzero, multi-piece coherence is exactly
`1`.  This is the positive-sign saturation obstruction for negation-stable door-(iv) refinements. -/
theorem multiPieceCoherence_eq_one_of_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hpos : 0 < ∑ i ∈ s, A i) :
    multiPieceCoherence s A = 1 := by
  unfold multiPieceCoherence
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, A i := Finset.sum_nonneg hA
  have hden : (∑ i ∈ s, |A i|) = ∑ i ∈ s, A i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact abs_of_nonneg (hA i hi)
  rw [abs_of_nonneg hsum_nonneg, hden]
  exact div_self (ne_of_gt hpos)

/-- If all real pieces are nonpositive and the total is nonzero, multi-piece coherence is exactly
`1`.  This is the negative-sign saturation obstruction for negation-stable door-(iv) refinements. -/
theorem multiPieceCoherence_eq_one_of_nonpos {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ)
    (hA : ∀ i ∈ s, A i ≤ 0) (hneg : (∑ i ∈ s, A i) < 0) :
    multiPieceCoherence s A = 1 := by
  unfold multiPieceCoherence
  have hsum_nonpos : (∑ i ∈ s, A i) ≤ 0 := Finset.sum_nonpos hA
  have hden : (∑ i ∈ s, |A i|) = -(∑ i ∈ s, A i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact abs_of_nonpos (hA i hi)
  rw [abs_of_nonpos hsum_nonpos, hden]
  exact div_self (ne_of_gt (neg_pos.mpr hneg))

/-- Compact same-sign formulation: if all real pieces have one sign and the total is nonzero, then
multi-piece coherence is exactly `1`. -/
theorem multiPieceCoherence_eq_one_of_sameSign {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ)
    (hsign : (∀ i ∈ s, 0 ≤ A i) ∨ (∀ i ∈ s, A i ≤ 0))
    (hsum : (∑ i ∈ s, A i) ≠ 0) :
    multiPieceCoherence s A = 1 := by
  rcases hsign with hnonneg | hnonpos
  · exact multiPieceCoherence_eq_one_of_nonneg s A hnonneg
      (lt_of_le_of_ne (Finset.sum_nonneg hnonneg) hsum.symm)
  · exact multiPieceCoherence_eq_one_of_nonpos s A hnonpos
      (lt_of_le_of_ne (Finset.sum_nonpos hnonpos) hsum)

/-! ## Signed-mass compression

For real, negation-stable refinements, subdividing the period into more pieces does not by itself
create a new phase statistic.  Once the pieces are real, the normalized multi-piece coherence is
controlled entirely by the imbalance between the aggregate positive `L¹` mass and the aggregate
negative `L¹` mass.  Thus a nontrivial coherence-slack theorem for a refined split must prove a real
signed-mass balance statement; it cannot come merely from the existence of many pieces.
-/

/-- If the total real sum is `posMass - negMass` and the total `L¹` mass is `posMass + negMass`,
then the multi-piece coherence compresses exactly to the signed-mass ratio
`|posMass - negMass| / (posMass + negMass)`.  This abstracts the door-(iv) obstruction: after a
negation-stable refinement has made every piece real, all phase information has collapsed to the two
numbers `posMass` and `negMass`. -/
theorem multiPieceCoherence_eq_abs_signedMass_ratio {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass) :
    multiPieceCoherence s A = |posMass - negMass| / (posMass + negMass) := by
  unfold multiPieceCoherence
  rw [hsum, hden]

/-- A coherence upper bound below `c` is exactly a signed-mass-balance demand: the absolute
positive/negative imbalance must be at most `c` times the total `L¹` mass.  This is the formal
constraint behind the probe verdict: to get slack from a multi-piece real refinement, one must prove
aggregate sign balance at the worst frequency, not merely refine the coset split. -/
theorem abs_signedMass_le_of_multiPieceCoherence_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass c : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hpos : 0 < posMass + negMass)
    (hle : multiPieceCoherence s A ≤ c) :
    |posMass - negMass| ≤ c * (posMass + negMass) := by
  rw [multiPieceCoherence_eq_abs_signedMass_ratio s A hsum hden] at hle
  exact (div_le_iff₀ hpos).mp hle

/-- Conversely, a signed-mass-balance inequality is precisely a coherence bound for the refined
real pieces.  The door-(iv) multi-piece route is therefore equivalent to proving this balance at the
adversarial `b`; refinement alone supplies no cancellation. -/
theorem multiPieceCoherence_le_of_abs_signedMass_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass c : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hpos : 0 < posMass + negMass)
    (hbal : |posMass - negMass| ≤ c * (posMass + negMass)) :
    multiPieceCoherence s A ≤ c := by
  rw [multiPieceCoherence_eq_abs_signedMass_ratio s A hsum hden]
  exact (div_le_iff₀ hpos).mpr hbal

/-- A strict coherence slack `c < 1` forces genuine positive mass.  If all real pieces were
nonpositive (`posMass = 0`), the signed-mass ratio would be exactly `1`, contradicting a strict
subunit balance bound. -/
theorem posMass_pos_of_strict_signedMass_balance {posMass negMass c : ℝ}
    (hposMass : 0 ≤ posMass) (hnegMass : 0 ≤ negMass)
    (htotal : 0 < posMass + negMass) (hc : c < 1)
    (hbal : |posMass - negMass| ≤ c * (posMass + negMass)) :
    0 < posMass := by
  by_contra hnot
  have hzero : posMass = 0 := le_antisymm (le_of_not_gt hnot) hposMass
  have hnegpos : 0 < negMass := by linarith
  have habs : |posMass - negMass| = negMass := by
    rw [hzero, zero_sub, abs_neg]
    exact abs_of_nonneg hnegMass
  have hle_abs : |negMass| ≤ c * negMass := by
    simpa [hzero, habs] using hbal
  have hle : negMass ≤ c * negMass := by
    rwa [abs_of_nonneg hnegMass] at hle_abs
  have hlt : c * negMass < negMass := by
    simpa using (mul_lt_mul_of_pos_right hc hnegpos)
  linarith

/-- A strict coherence slack `c < 1` also forces genuine negative mass.  A multi-piece real
refinement can beat coherence `1` only when both signs occur with nonzero aggregate mass. -/
theorem negMass_pos_of_strict_signedMass_balance {posMass negMass c : ℝ}
    (hposMass : 0 ≤ posMass) (hnegMass : 0 ≤ negMass)
    (htotal : 0 < posMass + negMass) (hc : c < 1)
    (hbal : |posMass - negMass| ≤ c * (posMass + negMass)) :
    0 < negMass := by
  by_contra hnot
  have hzero : negMass = 0 := le_antisymm (le_of_not_gt hnot) hnegMass
  have hpospos : 0 < posMass := by linarith
  have habs : |posMass - negMass| = posMass := by
    rw [hzero, sub_zero]
    exact abs_of_nonneg hposMass
  have hle_abs : |posMass| ≤ c * posMass := by
    simpa [hzero, habs] using hbal
  have hle : posMass ≤ c * posMass := by
    rwa [abs_of_nonneg hposMass] at hle_abs
  have hlt : c * posMass < posMass := by
    simpa using (mul_lt_mul_of_pos_right hc hpospos)
  linarith

/-- For nonnegative aggregate positive/negative masses with positive total, strict coherence slack is
*exactly* the presence of both signs.  This is the sharp multi-piece signed-mass obstruction:
a real refinement beats coherence `1` iff neither aggregate sign mass vanishes. -/
theorem abs_signedMass_ratio_lt_one_iff_two_sided {posMass negMass : ℝ}
    (hposMass : 0 ≤ posMass) (hnegMass : 0 ≤ negMass)
    (htotal : 0 < posMass + negMass) :
    |posMass - negMass| / (posMass + negMass) < 1 ↔ 0 < posMass ∧ 0 < negMass := by
  constructor
  · intro hlt
    let c := |posMass - negMass| / (posMass + negMass)
    have hmul : c * (posMass + negMass) = |posMass - negMass| := by
      dsimp [c]
      rw [div_mul_cancel₀ _ (ne_of_gt htotal)]
    have hbal : |posMass - negMass| ≤ c * (posMass + negMass) := by
      rw [hmul]
    exact ⟨
      posMass_pos_of_strict_signedMass_balance hposMass hnegMass htotal hlt hbal,
      negMass_pos_of_strict_signedMass_balance hposMass hnegMass htotal hlt hbal⟩
  · rintro ⟨hpos, hneg⟩
    have hlt_abs : |posMass - negMass| < posMass + negMass := by
      rw [abs_lt]
      constructor <;> linarith
    exact (div_lt_one htotal).mpr hlt_abs

/-- The complementary sharp form: with nonnegative masses and positive total, signed-mass coherence
saturates at `1` exactly when one aggregate sign mass is zero. -/
theorem abs_signedMass_ratio_eq_one_iff_one_side_zero {posMass negMass : ℝ}
    (hposMass : 0 ≤ posMass) (hnegMass : 0 ≤ negMass)
    (htotal : 0 < posMass + negMass) :
    |posMass - negMass| / (posMass + negMass) = 1 ↔ posMass = 0 ∨ negMass = 0 := by
  constructor
  · intro h
    by_cases hP : posMass = 0
    · exact Or.inl hP
    by_cases hN : negMass = 0
    · exact Or.inr hN
    have hpos : 0 < posMass := lt_of_le_of_ne hposMass (Ne.symm hP)
    have hneg : 0 < negMass := lt_of_le_of_ne hnegMass (Ne.symm hN)
    have hlt : |posMass - negMass| / (posMass + negMass) < 1 :=
      (abs_signedMass_ratio_lt_one_iff_two_sided hposMass hnegMass htotal).mpr ⟨hpos, hneg⟩
    linarith
  · intro hzero
    rcases hzero with hzero | hzero
    · have hnegpos : negMass ≠ 0 := by linarith
      rw [hzero, zero_sub, abs_neg, abs_of_nonneg hnegMass, zero_add]
      exact div_self hnegpos
    · have hpospos : posMass ≠ 0 := by linarith
      rw [hzero, sub_zero, abs_of_nonneg hposMass, add_zero]
      exact div_self hpospos

/-- Bridged sharp form for the actual multi-piece statistic: after compression to aggregate positive
and negative masses, strict multi-piece coherence slack is exactly two-sided aggregate sign mass. -/
theorem multiPieceCoherence_lt_one_iff_two_sided {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hposMass : 0 ≤ posMass) (hnegMass : 0 ≤ negMass)
    (htotal : 0 < posMass + negMass) :
    multiPieceCoherence s A < 1 ↔ 0 < posMass ∧ 0 < negMass := by
  rw [multiPieceCoherence_eq_abs_signedMass_ratio s A hsum hden]
  exact abs_signedMass_ratio_lt_one_iff_two_sided hposMass hnegMass htotal

/-- Bridged saturation form for the actual multi-piece statistic: after compression, coherence equals
`1` exactly when one aggregate sign mass vanishes. -/
theorem multiPieceCoherence_eq_one_iff_one_side_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hposMass : 0 ≤ posMass) (hnegMass : 0 ≤ negMass)
    (htotal : 0 < posMass + negMass) :
    multiPieceCoherence s A = 1 ↔ posMass = 0 ∨ negMass = 0 := by
  rw [multiPieceCoherence_eq_abs_signedMass_ratio s A hsum hden]
  exact abs_signedMass_ratio_eq_one_iff_one_side_zero hposMass hnegMass htotal

/-- If the positive mass is at least the negative mass, coherence is just the normalized excess
`(posMass - negMass)/(posMass + negMass)`. -/
theorem multiPieceCoherence_eq_posExcess_ratio {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hge : negMass ≤ posMass) :
    multiPieceCoherence s A = (posMass - negMass) / (posMass + negMass) := by
  rw [multiPieceCoherence_eq_abs_signedMass_ratio s A hsum hden]
  rw [abs_of_nonneg (sub_nonneg.mpr hge)]

/-- If the negative mass is at least the positive mass, coherence is the opposite normalized excess
`(negMass - posMass)/(posMass + negMass)`. -/
theorem multiPieceCoherence_eq_negExcess_ratio {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hge : posMass ≤ negMass) :
    multiPieceCoherence s A = (negMass - posMass) / (posMass + negMass) := by
  rw [multiPieceCoherence_eq_abs_signedMass_ratio s A hsum hden]
  have hnonpos : posMass - negMass ≤ 0 := sub_nonpos.mpr hge
  rw [abs_of_nonpos hnonpos]
  ring

/-- Signed-mass coherence is exactly `1` minus twice the minority-sign mass fraction.  This pins the
quantitative obligation of a multi-piece real-refinement attack: slack below `1` is not created by
having many pieces; it is exactly paid for by aggregate mass on the minority sign. -/
theorem abs_signedMass_ratio_eq_one_sub_two_mul_min_ratio {posMass negMass : ℝ}
    (htotal : 0 < posMass + negMass) :
    |posMass - negMass| / (posMass + negMass) =
      1 - (2 * min posMass negMass) / (posMass + negMass) := by
  by_cases hle : posMass ≤ negMass
  · have hnonpos : posMass - negMass ≤ 0 := sub_nonpos.mpr hle
    rw [abs_of_nonpos hnonpos, min_eq_left hle]
    field_simp [ne_of_gt htotal]
    ring
  · have hge : negMass ≤ posMass := le_of_not_ge hle
    have hnonneg : 0 ≤ posMass - negMass := sub_nonneg.mpr hge
    rw [abs_of_nonneg hnonneg, min_eq_right hge]
    field_simp [ne_of_gt htotal]
    ring

/-- Bridged quantitative form for the actual multi-piece statistic: after compression to aggregate
positive/negative masses, the coherence slack is exactly twice the minority-sign mass divided by the
total `L¹` mass. -/
theorem multiPieceCoherence_eq_one_sub_two_mul_min_ratio {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass) :
    multiPieceCoherence s A = 1 - (2 * min posMass negMass) / (posMass + negMass) := by
  rw [multiPieceCoherence_eq_abs_signedMass_ratio s A hsum hden]
  exact abs_signedMass_ratio_eq_one_sub_two_mul_min_ratio htotal

/-- A strict upper bound on real multi-piece coherence forces a quantitative minority-sign mass
floor.  If the compressed statistic is at most `c`, then the minority aggregate must pay at least
`(1-c)/2` of the total `L¹` mass.  This is the probe-facing obligation for any refined door-(iv)
sign-balance attack: the slack must be witnessed by actual two-sided mass, not by subdivision. -/
theorem two_mul_minMass_ge_of_multiPieceCoherence_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass c : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass)
    (hle : multiPieceCoherence s A ≤ c) :
    (1 - c) * (posMass + negMass) ≤ 2 * min posMass negMass := by
  rw [multiPieceCoherence_eq_one_sub_two_mul_min_ratio s A hsum hden htotal] at hle
  have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt htotal)
  rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt htotal)] at hmul
  linarith

/-- Exact budget interface for real multi-piece coherence.  A bound `coherence ≤ c` is equivalent to
paying the denominator-cleared minority-sign budget `(1-c)·total ≤ 2·minority`.  This is the sharp
constraint form a probe can cite: every claimed `1-c` coherence saving must appear as actual
minority-sign mass. -/
theorem multiPieceCoherence_le_iff_two_mul_minMass_ge {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass c : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass) :
    multiPieceCoherence s A ≤ c ↔
      (1 - c) * (posMass + negMass) ≤ 2 * min posMass negMass := by
  rw [multiPieceCoherence_eq_one_sub_two_mul_min_ratio s A hsum hden htotal]
  constructor
  · intro hle
    have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt htotal)
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt htotal)] at hmul
    linarith
  · intro hbudget
    have hmul := mul_le_mul_of_nonneg_right hbudget (inv_nonneg.mpr (le_of_lt htotal))
    field_simp [ne_of_gt htotal] at hmul ⊢
    linarith


/-- Exact saving identity for real multi-piece coherence.  After compression to aggregate sign
masses, the slack below saturation is precisely twice the minority-sign mass divided by the total
`L¹` mass.  This packages the door-(iv) obligation in the form used by probes: every unit of claimed
coherence saving must be paid by actual minority mass, not by the refinement itself. -/
theorem one_sub_multiPieceCoherence_eq_two_mul_min_ratio {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass) :
    1 - multiPieceCoherence s A = (2 * min posMass negMass) / (posMass + negMass) := by
  rw [multiPieceCoherence_eq_one_sub_two_mul_min_ratio s A hsum hden htotal]
  ring

/-- Exact epsilon-budget equality form.  A real refined split has coherence exactly `1 - ε` iff the
advertised saving `ε` is exactly the denominator-normalized minority-sign budget.  This is the sharp
equality companion to the `≤` budget theorem below. -/
theorem multiPieceCoherence_eq_one_sub_iff_eps_mass_budget_eq {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass ε : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass) :
    multiPieceCoherence s A = 1 - ε ↔
      ε * (posMass + negMass) = 2 * min posMass negMass := by
  rw [multiPieceCoherence_eq_one_sub_two_mul_min_ratio s A hsum hden htotal]
  constructor
  · intro h
    have hx : (2 * min posMass negMass) / (posMass + negMass) = ε := by linarith
    calc
      ε * (posMass + negMass)
          = ((2 * min posMass negMass) / (posMass + negMass)) * (posMass + negMass) := by rw [hx]
      _ = 2 * min posMass negMass := div_mul_cancel₀ _ (ne_of_gt htotal)
  · intro h
    have hx : (2 * min posMass negMass) / (posMass + negMass) = ε := by
      calc
        (2 * min posMass negMass) / (posMass + negMass)
            = (ε * (posMass + negMass)) / (posMass + negMass) := by rw [← h]
        _ = ε := mul_div_cancel_right₀ ε (ne_of_gt htotal)
    linarith

/-- Epsilon-budget form of the exact multi-piece obstruction.  A real refined split has coherence
at most `1 - ε` iff the aggregate minority-sign mass pays the full denominator-cleared budget
`ε * (posMass + negMass) ≤ 2 * min posMass negMass`.  This is the sharp consumer-facing form of the
constraint: an advertised `ε` coherence saving is exactly an `ε/2` minority-mass obligation. -/
theorem multiPieceCoherence_le_one_sub_iff_eps_mass_budget {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass ε : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass) :
    multiPieceCoherence s A ≤ 1 - ε ↔
      ε * (posMass + negMass) ≤ 2 * min posMass negMass := by
  rw [multiPieceCoherence_le_iff_two_mul_minMass_ge s A hsum hden htotal]
  ring_nf

/-- Contrapositive epsilon-budget form: if the aggregate minority-sign mass is too small for the
claimed `ε` saving, then the real multi-piece refinement cannot certify coherence `≤ 1 - ε`. -/
theorem not_multiPieceCoherence_le_one_sub_of_eps_mass_budget_lt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass ε : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass)
    (hfail : 2 * min posMass negMass < ε * (posMass + negMass)) :
    ¬ multiPieceCoherence s A ≤ 1 - ε := by
  intro hle
  have hbudget : ε * (posMass + negMass) ≤ 2 * min posMass negMass :=
    (multiPieceCoherence_le_one_sub_iff_eps_mass_budget s A hsum hden htotal).mp hle
  exact not_le_of_gt hfail hbudget

/-- Consumer-facing strict form: any subunit coherence certificate `coherence ≤ c < 1` for a real
multi-piece refinement forces positive aggregate mass on both signs.  This is the exact obstruction
for door-(iv) refinements at the adversarial frequency: a strict cap must first prove two-sided
signed mass, not merely introduce more pieces. -/
theorem two_sided_of_multiPieceCoherence_le_lt_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass c : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hposMass : 0 ≤ posMass) (hnegMass : 0 ≤ negMass)
    (htotal : 0 < posMass + negMass)
    (hle : multiPieceCoherence s A ≤ c) (hc : c < 1) :
    0 < posMass ∧ 0 < negMass := by
  have hlt : multiPieceCoherence s A < 1 := lt_of_le_of_lt hle hc
  exact (multiPieceCoherence_lt_one_iff_two_sided s A hsum hden hposMass hnegMass htotal).mp hlt

/-- Contrapositive interface: if one aggregate sign mass vanishes, no strict subunit bound can hold.
Thus a same-sign or one-sided refined split cannot be used as a door-(iv) anti-concentration witness. -/
theorem not_multiPieceCoherence_le_of_one_side_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass c : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hposMass : 0 ≤ posMass) (hnegMass : 0 ≤ negMass)
    (htotal : 0 < posMass + negMass)
    (hzero : posMass = 0 ∨ negMass = 0) (hc : c < 1) :
    ¬ multiPieceCoherence s A ≤ c := by
  intro hle
  have hone : multiPieceCoherence s A = 1 :=
    (multiPieceCoherence_eq_one_iff_one_side_zero s A hsum hden hposMass hnegMass htotal).mpr hzero
  linarith

/-- Epsilon-slack two-sidedness interface: any advertised positive saving
`coherence ≤ 1 - ε` for a real multi-piece refinement already forces positive aggregate mass on
both signs.  This is the direct consumer form of the sign-obstruction constraint: before a
door-(iv) anti-concentration proof can spend a fixed `ε`, it must exhibit genuine two-sided signed
mass at the worst frequency. -/
theorem two_sided_of_multiPieceCoherence_le_one_sub_eps {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass ε : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hposMass : 0 ≤ posMass) (hnegMass : 0 ≤ negMass)
    (htotal : 0 < posMass + negMass)
    (hε : 0 < ε) (hle : multiPieceCoherence s A ≤ 1 - ε) :
    0 < posMass ∧ 0 < negMass := by
  exact two_sided_of_multiPieceCoherence_le_lt_one s A hsum hden hposMass hnegMass htotal hle
    (by linarith)

/-- Epsilon-slack contrapositive: if one aggregate sign mass vanishes, then no positive `ε`
coherence saving can be certified by a real multi-piece refinement.  Refining into more real pieces
does not create a door-(iv) anti-concentration witness unless the minority sign has nonzero mass. -/
theorem not_multiPieceCoherence_le_one_sub_eps_of_one_side_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass ε : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hposMass : 0 ≤ posMass) (hnegMass : 0 ≤ negMass)
    (htotal : 0 < posMass + negMass)
    (hzero : posMass = 0 ∨ negMass = 0) (hε : 0 < ε) :
    ¬ multiPieceCoherence s A ≤ 1 - ε := by
  exact not_multiPieceCoherence_le_of_one_side_zero s A hsum hden hposMass hnegMass htotal hzero
    (by linarith)

/-- Direct minority-mass floor forced by an advertised epsilon saving.  In the real multi-piece
compression, a certificate `coherence ≤ 1 - ε` must place at least an `ε/2` fraction of the total
`L¹` mass on the minority sign.  This is the denominator-normalized form used by probes: slack is
not generated by refinement count, it is paid linearly by aggregate minority mass. -/
theorem minMass_ge_half_eps_total_of_multiPieceCoherence_le_one_sub_eps {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass ε : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass)
    (hle : multiPieceCoherence s A ≤ 1 - ε) :
    (ε / 2) * (posMass + negMass) ≤ min posMass negMass := by
  have hbudget : ε * (posMass + negMass) ≤ 2 * min posMass negMass :=
    (multiPieceCoherence_le_one_sub_iff_eps_mass_budget s A hsum hden htotal).mp hle
  linarith

/-- Contrapositive of the minority-mass floor: if the observed minority aggregate is below the
required `ε/2` share of the total `L¹` mass, then the real multi-piece refinement cannot certify
coherence `≤ 1 - ε`.  This is the sharp finite-probe obstruction for sign-refinement routes. -/
theorem not_multiPieceCoherence_le_one_sub_eps_of_minMass_lt_half_eps_total {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass ε : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass)
    (hfail : min posMass negMass < (ε / 2) * (posMass + negMass)) :
    ¬ multiPieceCoherence s A ≤ 1 - ε := by
  intro hle
  have hfloor := minMass_ge_half_eps_total_of_multiPieceCoherence_le_one_sub_eps s A hsum hden
    htotal hle
  exact not_le_of_gt hfail hfloor


end ProximityGap.Frontier.DoorIVMultiPieceSignCoherence

open ProximityGap.Frontier.DoorIVMultiPieceSignCoherence

#print axioms multiPieceCoherence_eq_one_of_nonneg
#print axioms multiPieceCoherence_le_one
#print axioms multiPieceCoherence_nonneg
#print axioms multiPieceCoherence_mem_Icc
#print axioms multiPieceCoherence_eq_one_of_nonpos
#print axioms multiPieceCoherence_eq_one_of_sameSign
#print axioms multiPieceCoherence_eq_abs_signedMass_ratio
#print axioms abs_signedMass_le_of_multiPieceCoherence_le
#print axioms multiPieceCoherence_le_of_abs_signedMass_le
#print axioms posMass_pos_of_strict_signedMass_balance
#print axioms negMass_pos_of_strict_signedMass_balance
#print axioms abs_signedMass_ratio_lt_one_iff_two_sided
#print axioms abs_signedMass_ratio_eq_one_iff_one_side_zero
#print axioms multiPieceCoherence_lt_one_iff_two_sided
#print axioms multiPieceCoherence_eq_one_iff_one_side_zero
#print axioms multiPieceCoherence_eq_posExcess_ratio
#print axioms multiPieceCoherence_eq_negExcess_ratio
#print axioms abs_signedMass_ratio_eq_one_sub_two_mul_min_ratio
#print axioms multiPieceCoherence_eq_one_sub_two_mul_min_ratio
#print axioms two_mul_minMass_ge_of_multiPieceCoherence_le
#print axioms multiPieceCoherence_le_iff_two_mul_minMass_ge
#print axioms one_sub_multiPieceCoherence_eq_two_mul_min_ratio
#print axioms multiPieceCoherence_eq_one_sub_iff_eps_mass_budget_eq
#print axioms multiPieceCoherence_le_one_sub_iff_eps_mass_budget
#print axioms not_multiPieceCoherence_le_one_sub_of_eps_mass_budget_lt
#print axioms two_sided_of_multiPieceCoherence_le_one_sub_eps
#print axioms not_multiPieceCoherence_le_one_sub_eps_of_one_side_zero
#print axioms minMass_ge_half_eps_total_of_multiPieceCoherence_le_one_sub_eps
#print axioms not_multiPieceCoherence_le_one_sub_eps_of_minMass_lt_half_eps_total
#print axioms two_sided_of_multiPieceCoherence_le_lt_one
#print axioms not_multiPieceCoherence_le_of_one_side_zero
