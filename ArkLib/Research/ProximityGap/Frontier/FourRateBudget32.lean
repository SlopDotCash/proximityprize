/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FourRateSmoothMca128
import ArkLib.Research.ProximityGap.Frontier.ListInterpolationBoundary
import ArkLib.Research.ProximityGap.Frontier.InterleavedListProjection

/-! # Four sharp MCA and list thresholds throughout a field-size interval at length 32 -/

set_option autoImplicit false

namespace ProximityGap.FourRateBudget32

open Finset Code GrandChallenges
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F] [DecidableEq F]

/-- The range of 128-bit security budgets with the stated eight thresholds. -/
def BudgetWindow (q : ℕ) : Prop := 3928630 ≤ q / 2^128 ∧ q / 2^128 ≤ 10518299

variable (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 32)
    (win : BudgetWindow (Fintype.card F))

private theorem room {k q : ℕ} (hk : k ≤ 16) (hw : BudgetWindow q) :
    k * (q / 2^128 + 1).choose 2 < (q - 32) * (q / 2^128 + 1 - q / 2^128) := by
  have hq := (Nat.le_div_iff_mul_le (by decide : 0 < 2^128)).mp hw.1
  rw [show q / 2^128 + 1 - q / 2^128 = 1 by omega, Nat.mul_one]
  calc k * (q/2^128 + 1).choose 2 ≤ 16 * (10518299+1).choose 2 :=
        Nat.mul_le_mul hk (Nat.choose_le_choose 2 (Nat.succ_le_succ hw.2))
    _ < 3928630*2^128 - 32 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
    _ ≤ q - 32 := Nat.sub_le_sub_right hq _

include hn win in
private theorem half_mca (δ : ℝ≥0) :
    epsMCA (F := F) (ReedSolomon.code D 16 : Set (I → F)) δ ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ↔ δ < 14/32 := by
  classical
  have band := FourRateSmoothMca128.prize_band (Fintype.card F) Fintype.card_pos
  have h := SmoothDeepMcaThreshold.epsMCA_le_iff D (k := 16) (a := 0) (t := 18)
    (B := Fintype.card F/2^128) (L := Fintype.card F/2^128)
    (by decide) (by decide) (by rw [hn]; decide)
    ((by rw [hn]; simp only [Nat.choose_eq_descFactorial_div_factorial]; decide :
      (Fintype.card I).choose (16+1)/Nat.choose 18 16 ≤ 3928630).trans win.1)
    (by
      rw [hn, pow_zero, Nat.mul_one]
      apply (Nat.mul_le_mul_left 32 win.2).trans_lt
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide)
    (by simpa only [hn] using room (by decide : 16 ≤ 16) win) _ band.1 band.2 δ
  simpa only [hn, Nat.reduceSub, Nat.cast_ofNat] using h

include hn win in
omit [ReedSolomon.Smooth D] [DecidableEq F] in
private theorem quarter_mca (δ : ℝ≥0) :
    epsMCA (F := F) (ReedSolomon.code D 8 : Set (I → F)) δ ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ↔ δ < 23/32 := by
  classical
  let q := Fintype.card F
  let B := q/2^128
  have hstep : (1-δ)*(Fintype.card I : ℝ≥0) ≤ 9 ↔ 23/32 ≤ δ := by
    rw [hn, Nat.cast_ofNat, tsub_mul, one_mul, tsub_le_iff_right, div_le_iff₀ (by norm_num)]
    constructor <;> intro h <;> linarith
  have band := FourRateSmoothMca128.prize_band q Fintype.card_pos
  constructor
  · contrapose!
    intro hδ
    have hq : Nat.card F < 2^256 := by
      rw [Nat.card_eq_fintype_card]
      exact ((Nat.div_lt_iff_lt_mul (by decide : 0 < 2^128)).mp (Nat.lt_succ_of_le win.2)).trans_le
        (by decide)
    have hl : (B : ℕ∞) < Lambda (ReedSolomon.code D (8+1) : Set (I → F))
        (((Fintype.card I - 9 : ℕ) : ℝ) / Fintype.card I) := by
      by_contra! h
      have hh := (InterleavedListProjection.prize_list_budget_iff (κ := Fin 1)
        (ReedSolomon.code D 9) _ hq).mpr (by simpa only [Nat.card_eq_fintype_card] using h)
      change Lambda (ListInterpolationBoundary.words D 9 1) _ ≤ _ at hh
      rw [ListInterpolationBoundary.at_dimension_agreement D (by decide) (by rw [hn]; decide)
        (by decide), Nat.card_eq_fintype_card, hn] at hh
      have h' : Nat.choose 32 9 ≤ B := by exact_mod_cast hh
      exact (not_le_of_gt (win.2.trans_lt
        (show 10518299 < Nat.choose 32 9 by
          rw [Nat.choose_eq_descFactorial_div_factorial]
          decide))) h'
    obtain ⟨u,v,hcount⟩ := DeepListMcaTransfer.exists_bad_count_of_list D δ (k := 8) (t := 9)
      (B := B) (L := B) (by decide) (by decide) (by rw [hn]; decide) (hstep.mpr hδ)
      hl (by simpa only [hn] using room (by decide : 8 ≤ 16) win)
    let G := univ.filter (mcaEvent (F := F) (ReedSolomon.code D 8 : Set (I → F)) δ u v)
    have hbig := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
      (ReedSolomon.code D 8 : Set (I → F)) δ ![u,v] G (fun γ hγ => (mem_filter.mp hγ).2)
    apply band.2.trans_le (le_trans ?_ hbig)
    exact ENNReal.div_le_div_right (by exact_mod_cast (show B+1 ≤ G.card from hcount)) q
  · intro hδ
    apply le_trans ?_ band.1
    apply epsMCA_le_of_badCount_le
    intro u
    have h := CircuitDensity.mca_count_mul_le D 8 10 δ (u 0) (u 1) (by decide) (by
      intro S hS
      by_contra! hc
      exact hδ.not_ge (hstep.mp (hS.trans (by exact_mod_cast (show S.card ≤ 9 by omega)))))
    have hb := (Nat.le_div_iff_mul_le (Nat.choose_pos (by decide : 8 ≤ 10-1))).mpr h
    apply hb.trans
    rw [hn]
    exact (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide :
      Nat.choose 32 (8+1)/Nat.choose (10-1) 8 ≤ 3928630).trans win.1

include hn win in
omit [ReedSolomon.Smooth D] [DecidableEq F] in
private theorem low_mca {k : ℕ} (hk : k = 4 ∨ k = 2) (δ : ℝ≥0) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) δ ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) := by
  classical
  apply le_trans ?_ (FourRateSmoothMca128.prize_band (Fintype.card F) Fintype.card_pos).1
  apply epsMCA_le_of_badCount_le
  intro u
  apply (CircuitDensity.mca_count_le_choose D k δ (u 0) (u 1)).trans
  rw [hn]
  apply le_trans ?_ win.1
  rcases hk with rfl | rfl <;> rw [Nat.choose_eq_descFactorial_div_factorial] <;> decide

include hn win in
/-- At dimensions 16 and 8 the MCA first failure is at 14 and 23 errors respectively.
At dimensions 4 and 2 every radius passes. This holds at every positive interleaving width. -/
theorem mca_threshold (j : Fin 4) (m : ℕ) [NeZero m] (δ : ℝ≥0) :
    epsMCA (F := F) (A := Fin m → F)
        ((ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → F)) ^⋈ (Fin m)) δ ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ↔
      (j = 0 → δ < 14/32) ∧ (j = 1 → δ < 23/32) := by
  classical
  rw [epsMCA_interleaved_eq]
  fin_cases j
  · simpa [prizeDimension, prizeDenominator, hn] using half_mca D hn win δ
  · simpa [prizeDimension, prizeDenominator, hn] using quarter_mca D hn win δ
  · simpa [prizeDimension, prizeDenominator, hn] using low_mca D hn win (k := 4) (Or.inl rfl) δ
  · simpa [prizeDimension, prizeDenominator, hn] using low_mca D hn win (k := 2) (Or.inr rfl) δ

/-- The list first failing counts at dimensions 16, 8, 4, and 2. -/
def listFirstBad : Fin 4 → ℕ := ![15,24,29,31]

include hn win in
private theorem half_list (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (ListInterpolationBoundary.words D 16 m) δ : ℝ≥0∞) ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F ↔ δ < 15/32 := by
  let B := Fintype.card F / 2^128
  rw [FourRateList128.budget_cast]
  constructor
  · contrapose!
    intro hδ
    have hs := SmoothDeepMcaThreshold.smooth_list_lower D (k := 16) (a := 0) (L := B)
      (by decide) (by
        rw [hn, pow_zero, Nat.mul_one]
        apply (Nat.mul_le_mul_left 32 win.2).trans_lt
        rw [Nat.choose_eq_descFactorial_div_factorial]
        decide)
    have hd := Lambda_le_of_injective_comp (C := (ReedSolomon.code D 16 : Set (I → F)))
      (D := ListInterpolationBoundary.words D 16 m) (e := fun (a : F) (_ : Fin m) => a)
      (fun _ _ h => congrFun h ⟨0, hm⟩) (fun _ h _ => h) (15/32)
    rw [hn] at hs
    exact (show (B : ℕ∞) < _ from hs).trans_le (hd.trans (Lambda_mono hδ))
  · intro hδ
    have hu := AgreementSubsetListPacking.interleaved_lambda_le_choose_div D 16 18 m δ
      (by decide) (by rw [hn]; norm_num; linarith)
    rw [hn] at hu
    apply hu.trans
    exact_mod_cast (show Nat.choose 32 16 / Nat.choose 18 16 ≤ B from
      (by simp only [Nat.choose_eq_descFactorial_div_factorial]; decide :
        Nat.choose 32 16 / Nat.choose 18 16 ≤ 3928630).trans win.1)

include hn win in
/-- The simultaneous list threshold on all smooth length-32 domains throughout the
budget window, for every positive interleaving width. -/
theorem list_threshold (j : Fin 4) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (ListInterpolationBoundary.words D (prizeDimension (ι := I) j) m) δ : ℝ≥0∞) ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F ↔ δ < (listFirstBad j : ℝ)/32 := by
  let B := Fintype.card F / 2^128
  have low (k : ℕ) (hk : k = 8 ∨ k = 4 ∨ k = 2) :=
    ListInterpolationBoundary.prize_good_iff D (k := k) (m := m) (by omega)
      (by rw [hn]; omega) hm (by
        rw [hn]
        apply le_trans ?_ win.1
        rcases hk with rfl | rfl | rfl <;>
          rw [Nat.choose_eq_descFactorial_div_factorial] <;> decide) δ
  have h₈ : ¬ Nat.choose 32 8 ≤ B := not_le_of_gt (win.2.trans_lt
    (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide))
  have h₄ : Nat.choose 32 4 ≤ B := (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide :
    Nat.choose 32 4 ≤ 3928630).trans win.1
  have h₂ : Nat.choose 32 2 ≤ B := (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide :
    Nat.choose 32 2 ≤ 3928630).trans win.1
  fin_cases j
  · simpa [prizeDimension, prizeDenominator, hn, listFirstBad] using half_list D hn win m hm δ
  · have h := low 8 (Or.inl rfl)
    rw [hn, ite_eq_right h₈] at h
    simpa [prizeDimension, prizeDenominator, hn, listFirstBad] using h
  · have h := low 4 (Or.inr (Or.inl rfl))
    rw [hn, ite_eq_left h₄] at h
    simpa [prizeDimension, prizeDenominator, hn, listFirstBad] using h
  · have h := low 2 (Or.inr (Or.inr rfl))
    rw [hn, ite_eq_left h₂] at h
    simpa [prizeDimension, prizeDenominator, hn, listFirstBad] using h

end ProximityGap.FourRateBudget32
