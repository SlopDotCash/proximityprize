/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothDeepMcaThreshold
import ArkLib.Research.ProximityGap.Frontier.FourRateListPrime246
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA
import ArkLib.Data.CodingTheory.ProximityGap.MCAExactPin

/-! # Four exact MCA radii on every smooth length-128 domain in a field-size interval

At dimension 64, 67 agreements suffice at the specified budget and a DEEP
quotient violates it at 66 agreements. At dimensions 32, 16 and 8 the total
number of detecting interpolation circuits suffices on the full radius range.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace ProximityGap.FourRateSmoothMca128
open GrandChallenges
open scoped NNReal ENNReal
variable {I F : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F] [DecidableEq F] [DecidableEq I]

/-- Least integer budget for the circuit upper bound at 67 agreements. -/
abbrev lowerBudget : ℕ := 10994250290001056506599803605439163

/-- Largest integer budget exceeded by the common-product pigeonhole at 66 agreements. -/
abbrev upperBudget : ℕ := 175865058349821587478617952204192862

/-- Field orders for which the fixed length-128 counts straddle the prize threshold. -/
def BudgetWindow (q : ℕ) : Prop := lowerBudget ≤ q / 2^128 ∧ q / 2^128 ≤ upperBudget

/-- The exact probability tolerance lies between the two adjacent grid numerators. -/
theorem prize_band (q : ℕ) (hq : 0 < q) :
    (((q/2^128 : ℕ) : ℝ≥0∞) / q ≤ ((prizeThreshold : ℝ≥0) : ℝ≥0∞)) ∧
    (((prizeThreshold : ℝ≥0) : ℝ≥0∞) < ((q/2^128+1 : ℕ) : ℝ≥0∞) / q) := by
  have hp : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hq.ne'
  constructor
  · rw [ENNReal.div_le_iff hp (ENNReal.natCast_ne_top _)]
    exact (FourRateList128.budget_cast q (q/2^128 : ℕ)).2 le_rfl
  · rw [ENNReal.lt_div_iff_mul_lt (Or.inl hp) (Or.inl (ENNReal.natCast_ne_top _))]
    apply lt_of_not_ge
    intro h
    have hle := (FourRateList128.budget_cast q (q/2^128+1 : ℕ)).1 h
    exact (Nat.not_succ_le_self _) (by exact_mod_cast hle)

variable (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 128)
    (window : BudgetWindow (Fintype.card F))
include hn window

/-- The exact 128-bit bad-scalar crossing at rate one half. -/
theorem half_good_iff (δ : ℝ≥0) :
    epsMCA (F := F) (ReedSolomon.code D 64 : Set (I → F)) δ ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ↔ δ < 62/128 := by
  let q := Fintype.card F
  let B := q/2^128
  have hB : lowerBudget ≤ B ∧ B ≤ upperBudget := window
  have hq := (Nat.mul_le_mul_right (2^128) hB.1).trans (Nat.div_mul_le_self q (2^128))
  have hroom : 64*(B+1).choose 2 < (q-128)*(B+1-B) := by
    rw [show B+1-B = 1 by omega, Nat.mul_one]
    calc 64*(B+1).choose 2 ≤ 64*(upperBudget+1).choose 2 :=
          Nat.mul_le_mul_left _ (Nat.choose_le_choose 2 (by omega))
      _ < lowerBudget * 2^128-128 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
      _ ≤ q-128 := Nat.sub_le_sub_right hq _
  have hε := prize_band q Fintype.card_pos
  have hu : Nat.choose 128 65 / Nat.choose 66 64 ≤ B := by
    calc Nat.choose 128 65 / Nat.choose 66 64 = lowerBudget := by
            simp only [Nat.choose_eq_descFactorial_div_factorial]
            decide
      _ ≤ B := hB.1
  have hl : 128 * B < Nat.choose 128 66 := by
    calc 128 * B ≤ 128 * upperBudget := Nat.mul_le_mul_left _ hB.2
      _ < Nat.choose 128 66 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h := SmoothDeepMcaThreshold.epsMCA_le_iff D (k := 64) (a := 0) (t := 66)
    (B := B) (L := B) (by decide) (by decide) (by rw [hn]; decide)
    (hn ▸ hu) (by simpa only [hn, pow_zero, Nat.mul_one] using hl)
    (by simpa only [hn] using hroom) _ hε.1 hε.2 δ
  simpa only [hn, Nat.reduceSub, Nat.cast_ofNat] using h

omit [ReedSolomon.Smooth D] in
/-- At the other three sponsor dimensions the entire interval is safe. -/
theorem lower_rates_good {k : ℕ} (hk : k = 32 ∨ k = 16 ∨ k = 8) (δ : ℝ≥0) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) δ ≤ ((prizeThreshold : ℝ≥0) : ℝ≥0∞) := by
  classical
  apply le_trans ?_ (prize_band (Fintype.card F) Fintype.card_pos).1
  apply epsMCA_le_of_badCount_le
  intro u
  apply (CircuitDensity.mca_count_le_choose D k δ (u 0) (u 1)).trans
  rw [hn]
  apply le_trans ?_ window.1
  rcases hk with rfl | rfl | rfl <;> rw [Nat.choose_eq_descFactorial_div_factorial] <;> decide

/-- The real-radius classification at positive interleaving width. -/
theorem interleaved_good_iff (j : Fin 4) (m : ℕ) [NeZero m] (δ : ℝ≥0) :
    epsMCA (F := F) (A := Fin m → F)
      ((ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → F)) ^⋈ (Fin m)) δ ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ↔ j ≠ 0 ∨ δ < 62/128 := by
  rw [epsMCA_interleaved_eq]
  fin_cases j
  · simpa [prizeDimension, prizeDenominator, hn] using half_good_iff D hn window δ
  all_goals
    constructor
    · intro _
      exact Or.inl (by decide)
    · intro _
      apply lower_rates_good D hn window
      norm_num [prizeDimension, prizeDenominator, hn]

/-- The operational supremum in [0,1] at every prize rate and positive width. -/
theorem threshold (j : Fin 4) (m : ℕ) [NeZero m] :
    MCAThresholdLedger.mcaDeltaStar (F := F)
      ((ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → F)) ^⋈ (Fin m))
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) = if j = 0 then 62/128 else 1 := by
  split_ifs with hj
  · apply MCAThresholdLedger.mcaDeltaStar_eq_of_good_below_of_bad_above _ _ (by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 128)]
      norm_num)
    · intro δ hδ
      exact (interleaved_good_iff D hn window j m δ).2 (.inr hδ)
    · intro δ hδ
      exact lt_of_not_ge fun h => ((interleaved_good_iff D hn window j m δ).1 h).elim
        (fun h => h hj) (not_lt_of_ge hδ)
  · unfold MCAThresholdLedger.mcaDeltaStar
    apply le_antisymm
    · apply csSup_le
      · exact ⟨0, by simp, (interleaved_good_iff D hn window j m 0).2 (.inl hj)⟩
      · intro x hx
        exact hx.1
    · exact MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ le_rfl
        ((interleaved_good_iff D hn window j m 1).2 (.inl hj))

/-- All four canonical affine-line MCA prize instances, with the half-rate crossing at
62 errors and the other three dimensions safe through the radius-one grid point. -/
theorem mcaPrize_all_rates [SampleableType F] : mcaPrize D := by
  refine ⟨PrizeDomainAdmissible.of_smooth D (hn ▸ by decide), ?_⟩
  intro j
  fin_cases j
  · left
    refine ⟨61, hn ▸ by decide, ?_, ?_⟩
    · rw [← epsMCA_eq_mcaError]
      simpa [prizeDimension, prizeDenominator, hn] using
        (half_good_iff D hn window (gridPt (ι := I) 61)).2 (by norm_num [gridPt, hn])
    · rw [← epsMCA_eq_mcaError]
      apply lt_of_not_ge
      intro h
      apply lt_irrefl (62/128 : ℝ≥0)
      simpa [gridPt, hn] using (half_good_iff D hn window (gridPt (ι := I) 62)).1 (by
        simpa [prizeDimension, prizeDenominator, hn] using h)
  all_goals
    right
    intro e _
    rw [← epsMCA_eq_mcaError]
    apply lower_rates_good D hn window
    norm_num [prizeDimension, prizeDenominator, hn]

omit hn window

/-- The certified prime 65·2²³⁹+1 is in the interval. -/
theorem prime246_window : BudgetWindow (Fintype.card FourRateListPrime246.K) := by
  rw [FourRateListPrime246.card_K]
  unfold BudgetWindow
  decide

/-- A concrete smooth-domain inhabitant, with its prime and domain supplied by the
kernel-verified order-128 generator. -/
theorem prime246_mcaPrize : mcaPrize FourRateListPrime246.domain :=
  mcaPrize_all_rates FourRateListPrime246.domain FourRateListPrime246.card_H prime246_window

/-- The list and MCA classifications coexist at this prime and domain for every positive width. -/
theorem prime246_both_prizes (m : ℕ) (hm : 0 < m) :
    mcaPrize FourRateListPrime246.domain ∧ listDecodingPrize FourRateListPrime246.domain m :=
  ⟨prime246_mcaPrize, FourRateListPrime246.listDecodingPrize_all_rates m hm⟩

#print axioms threshold
#print axioms prime246_both_prizes
#print axioms half_good_iff
#print axioms interleaved_good_iff
#print axioms mcaPrize_all_rates
#print axioms prime246_mcaPrize
end ProximityGap.FourRateSmoothMca128
