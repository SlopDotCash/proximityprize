/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothPowerMcaDescent

/-! # Explicit below-capacity MCA failures at all four rates on large smooth domains -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace ProximityGap.FourRateSmoothMcaLift
open Finset Polynomial FourRateSmoothMca128
open scoped NNReal ENNReal
variable {I F : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Field F] [Fintype F] [DecidableEq F]

private theorem power_bad (D : I ↪ F) [ReedSolomon.Smooth D] {m h k : ℕ} (hm : 0 < m)
    (hk : 0 < k) (hk64 : k ≤ 64) (hh512 : h ≤ 512) (ht : k+2 ≤ h)
    (hn : Fintype.card I = m*h) (hp : ∃ b : ℕ, h = 2^b)
    (window : BudgetWindow (Fintype.card F)) (hnum : h*upperBudget < h.choose (k+2))
    {δ : ℝ≥0} (hδ : ((h-(k+2) : ℕ) : ℝ≥0) / (h : ℝ≥0) ≤ δ) :
    ((prizeThreshold : ℝ≥0) : ℝ≥0∞) <
      epsMCA (F := F) (ReedSolomon.code D (k*m) : Set (I → F)) δ := by
  classical
  obtain ⟨V,hV,_,_,⟨sm⟩,hlift⟩ := SmoothPowerMcaDescent.exists_smooth_base D hm hn hp
  let := sm
  have hpos : 0 < h := by omega
  let : Nonempty V := Fintype.card_pos_iff.mp (by simpa [hV] using hpos)
  let E := Function.Embedding.subtype (· ∈ V)
  let q := Fintype.card F
  let B := q/2^128
  have hB : lowerBudget ≤ B ∧ B ≤ upperBudget := window
  have hq := (Nat.mul_le_mul_right (2^128) hB.1).trans (Nat.div_mul_le_self q (2^128))
  have hroom : k*(B+1).choose 2 < (q-h)*(B+1-B) := by
    rw [show B+1-B = 1 by omega, Nat.mul_one]
    calc k*(B+1).choose 2 ≤ 64*(upperBudget+1).choose 2 :=
          Nat.mul_le_mul hk64 (Nat.choose_le_choose 2 (by omega))
      _ < lowerBudget*2^128-512 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
      _ ≤ q-h := by omega
  have hr : (1-δ)*(h : ℝ≥0) ≤ k+2 := by
    have hn' : (0 : ℝ≥0) < h := by exact_mod_cast hpos
    rw [div_le_iff₀ hn', Nat.cast_tsub, tsub_le_iff_right] at hδ
    rw [tsub_mul, one_mul, tsub_le_iff_right]
    simpa [add_comm] using hδ
  have hc : Fintype.card V = h := by simpa using hV
  apply lt_of_lt_of_le _ (hlift k hk δ)
  apply SmoothDeepMcaThreshold.lt_epsMCA_of_product E (k := k) (a := 0) (t := k+2)
    (B := B) (L := B) hk rfl (hc ▸ ht) ?_ (hc ▸ hroom) _ (prize_band q Fintype.card_pos).2 δ
  · simpa only [hc, Nat.cast_add, Nat.cast_ofNat] using hr
  · simpa [hc] using (Nat.mul_le_mul_left h hB.2).trans_lt hnum

/-- Sufficient bad radii at the sponsor rates in order. -/
noncomputable def failureRadius : Fin 4 → ℝ≥0 := ![31/64, 95/128, 111/128, 239/256]

/-- Every smooth domain of size a multiple of 512 in the field budget interval violates
the 128-bit threshold, at all four sponsor rates, at the displayed respective radii. -/
theorem all_rates_bad (D : I ↪ F) [ReedSolomon.Smooth D] {r : ℕ}
    (hr : 0 < r) (hn : Fintype.card I = r*512) (window : BudgetWindow (Fintype.card F))
    (j : Fin 4) (δ : ℝ≥0) (hδ : failureRadius j ≤ δ) :
    ((prizeThreshold : ℝ≥0) : ℝ≥0∞) <
      epsMCA (F := F) (ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → F)) δ := by
  let h : Fin 4 → ℕ := ![128,256,256,512]
  let d : Fin 4 → ℕ := ![64,64,32,32]
  let s : Fin 4 → ℕ := ![4*r,2*r,2*r,r]
  have hdim : prizeDimension (ι := I) j = d j * s j := by
    fin_cases j <;> simp [prizeDimension,prizeDenominator,hn,d,s] <;> omega
  rw [hdim]
  apply power_bad D (h := h j)
  · fin_cases j <;> simp [s] <;> omega
  · fin_cases j <;> decide
  · fin_cases j <;> decide
  · fin_cases j <;> decide
  · fin_cases j <;> decide
  · rw [hn]; fin_cases j <;> simp [s,h] <;> omega
  · fin_cases j
    · exact ⟨7,rfl⟩
    · exact ⟨8,rfl⟩
    · exact ⟨8,rfl⟩
    · exact ⟨9,rfl⟩
  · exact window
  · fin_cases j <;> simp only [d,h,Nat.choose_eq_descFactorial_div_factorial] <;> decide
  · fin_cases j <;> norm_num [h,d,failureRadius] at hδ ⊢ <;> exact hδ

/-- Every positive interleaving width has the same four upper bounds on its operational radius. -/
theorem threshold_le_failureRadius (D : I ↪ F) [ReedSolomon.Smooth D] {r : ℕ}
    (hr : 0 < r) (hn : Fintype.card I = r*512) (window : BudgetWindow (Fintype.card F))
    (j : Fin 4) (width : ℕ) [NeZero width] :
    MCAThresholdLedger.mcaDeltaStar (F := F)
      ((ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → F)) ^⋈ (Fin width))
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ≤ failureRadius j := by
  apply MCAThresholdLedger.mcaDeltaStar_le_of_bad
  rw [epsMCA_interleaved_eq]
  exact all_rates_bad D hr hn window j _ le_rfl

/-- The actual length-128 power image is within budget at each of the three lower
rates even when arbitrary received stacks upstairs strictly violate the same tolerance. -/
theorem reverse_budget_failure (D : I ↪ F) [ReedSolomon.Smooth D] {r : ℕ}
    (hr : 0 < r) (hn : Fintype.card I = r*512) (window : BudgetWindow (Fintype.card F)) :
    ∃ V : Finset F, V.card = 128 ∧ (∀ i, D i ^ (4*r) ∈ V) ∧
      (∀ v ∈ V, (univ.filter (fun i => D i ^ (4*r) = v)).card = 4*r) ∧
      ∀ j : Fin 4, j ≠ 0 → ∀ δ : ℝ≥0, failureRadius j ≤ δ →
      epsMCA (F := F) (ReedSolomon.code (Function.Embedding.subtype (· ∈ V))
        (prizeDimension (ι := V) j) : Set (V → F)) δ ≤ ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ∧
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) <
        epsMCA (F := F) (ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → F)) δ := by
  classical
  obtain ⟨V,hV,hm,hf,_,_⟩ := SmoothPowerMcaDescent.exists_smooth_base D
    (m := 4*r) (h := 128) (by omega) (by omega) ⟨7,rfl⟩
  let : Nonempty V := Fintype.card_pos_iff.mp (by simp [hV])
  refine ⟨V,hV,hm,hf,fun j hj δ hδ => ⟨?_, all_rates_bad D hr hn window j δ hδ⟩⟩
  apply lower_rates_good _ (by simpa using hV) window
  fin_cases j <;> norm_num [prizeDimension,prizeDenominator,hV] at *

/-- At the certified 246-bit prime these bounds apply on every smooth domain of size 2³⁰. -/
theorem prime246_thresholds (D : I ↪ FourRateListPrime246.K) [ReedSolomon.Smooth D]
    (hn : Fintype.card I = 2^30) (j : Fin 4) (width : ℕ) [NeZero width] :
    MCAThresholdLedger.mcaDeltaStar (F := FourRateListPrime246.K)
      ((ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → FourRateListPrime246.K))
        ^⋈ (Fin width)) ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ≤ failureRadius j :=
  threshold_le_failureRadius D (r := 2097152) (by decide) (hn.trans (by decide)) prime246_window j width

#print axioms reverse_budget_failure
#print axioms all_rates_bad
#print axioms threshold_le_failureRadius
#print axioms prime246_thresholds
end ProximityGap.FourRateSmoothMcaLift
