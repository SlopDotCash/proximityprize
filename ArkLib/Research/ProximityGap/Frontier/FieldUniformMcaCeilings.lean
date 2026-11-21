/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FourRateSmoothMcaLift

/-!
# Power-map MCA failures without a field-size window

`FourRateSmoothMcaLift.all_rates_bad` proves four below-capacity MCA failures on long smooth
domains when the 128-bit budget `⌊q/2^128⌋` lies in a window. The window has a lower end
only because the DEEP collision count was stated for lists of the budget's own size. Here
the lower end is removed, and a second version with lists of size `2 B + 1` removes the
upper end as well.

## Main statements

* `all_rates_bad_of_budget_le`: for every finite field whose budget is at most
  `FourRateSmoothMca128.upperBudget`, every smooth domain of length divisible by 512 fails
  the 128-bit test at radii `31/64`, `95/128`, `111/128` and `239/256`.
* `all_rates_bad_below_256`: for every finite field with fewer than `2^256` elements, the
  same domains fail at radii `63/128`, `95/128`, `111/128` and `239/256`.

Both need more than 2048 field elements, which the domain already forces at lengths
above 2048.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace ProximityGap.FieldUniformMcaCeilings

open Finset Polynomial FourRateSmoothMca128 FourRateSmoothMcaLift
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Field F] [Fintype F]
  [DecidableEq F]

/-- A power-map failure with lists of the budget's own size. It needs the budget below
`2^118` and no lower bound on the field beyond `1024 + 2 h` elements. -/
private theorem power_bad_small (D : I ↪ F) [ReedSolomon.Smooth D] {m h k : ℕ} (hm : 0 < m)
    (hk : 0 < k) (hk512 : k ≤ 512) (ht : k+2 ≤ h)
    (hn : Fintype.card I = m*h) (hp : ∃ b : ℕ, h = 2^b)
    (hq : 1024 + 2*h < Fintype.card F) (hB118 : Fintype.card F / 2^128 ≤ 2^118)
    (hnum : h*(Fintype.card F / 2^128) < h.choose (k+2))
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
  have hB : B*2^128 ≤ q := Nat.div_mul_le_self q (2^128)
  have hroom : k*(B+1).choose 2 < (q-h)*(B+1-B) := by
    rw [show B+1-B = 1 by omega, Nat.mul_one, Nat.choose_two_right, Nat.add_sub_cancel]
    have h₁ : k*((B+1)*B/2) ≤ 512*((B+1)*B/2) := Nat.mul_le_mul_right _ hk512
    have h₂ : (B+1)*B ≤ (2^118+1)*B := Nat.mul_le_mul_right B (by omega)
    omega
  have hr : (1-δ)*(h : ℝ≥0) ≤ k+2 := by
    have hn' : (0 : ℝ≥0) < h := by exact_mod_cast hpos
    rw [div_le_iff₀ hn', Nat.cast_tsub, tsub_le_iff_right] at hδ
    rw [tsub_mul, one_mul, tsub_le_iff_right]
    simpa [add_comm] using hδ
  have hc : Fintype.card V = h := by simpa using hV
  have hlower : h*B < h.choose (k+2) := hnum
  apply lt_of_lt_of_le _ (hlift k hk δ)
  apply SmoothDeepMcaThreshold.lt_epsMCA_of_product E (k := k) (a := 0) (t := k+2)
    (B := B) (L := B) hk rfl (hc ▸ ht) ?_ (hc ▸ hroom) _ (prize_band q Fintype.card_pos).2 δ
  · simpa only [hc, Nat.cast_add, Nat.cast_ofNat] using hr
  · simpa [hc] using hlower

/-- A power-map failure with lists of size `2 B + 1`. It needs no bound on the budget
beyond the count `h (2 U + 1) < C(h, k + 2)` for a cap `U` on it. -/
private theorem power_bad_any (D : I ↪ F) [ReedSolomon.Smooth D] {m h k U : ℕ} (hm : 0 < m)
    (hk : 0 < k) (hk512 : k ≤ 512) (ht : k+2 ≤ h)
    (hn : Fintype.card I = m*h) (hp : ∃ b : ℕ, h = 2^b)
    (hq : 1024 + 2*h < Fintype.card F) (hU : Fintype.card F / 2^128 ≤ U)
    (hnum : h*(2*U+1) < h.choose (k+2))
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
  have hB : B*2^128 ≤ q := Nat.div_mul_le_self q (2^128)
  have hlin : k*(2*B+1) < q-h := by
    have h₁ : k*(2*B+1) ≤ 512*(2*B+1) := Nat.mul_le_mul_right _ hk512
    omega
  have hroom : k*(2*B+1+1).choose 2 < (q-h)*(2*B+1+1-B) := by
    have e : (2*B+1+1).choose 2 = (B+1)*(2*B+1) := by
      rw [Nat.choose_two_right, Nat.add_sub_cancel]
      apply Nat.div_eq_of_eq_mul_left (by decide)
      ring
    rw [e, show 2*B+1+1-B = B+2 by omega]
    calc k*((B+1)*(2*B+1)) = k*(2*B+1)*(B+1) := by ring
      _ ≤ (q-h)*(B+1) := Nat.mul_le_mul_right _ hlin.le
      _ < (q-h)*(B+2) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hr : (1-δ)*(h : ℝ≥0) ≤ k+2 := by
    have hn' : (0 : ℝ≥0) < h := by exact_mod_cast hpos
    rw [div_le_iff₀ hn', Nat.cast_tsub, tsub_le_iff_right] at hδ
    rw [tsub_mul, one_mul, tsub_le_iff_right]
    simpa [add_comm] using hδ
  have hc : Fintype.card V = h := by simpa using hV
  have hlower : h*(2*B+1) < h.choose (k+2) :=
    (Nat.mul_le_mul_left h (by omega : 2*B+1 ≤ 2*U+1)).trans_lt hnum
  apply lt_of_lt_of_le _ (hlift k hk δ)
  apply SmoothDeepMcaThreshold.lt_epsMCA_of_product E (k := k) (a := 0) (t := k+2)
    (B := B) (L := 2*B+1) hk rfl (hc ▸ ht) ?_ (hc ▸ hroom) _
    (prize_band q Fintype.card_pos).2 δ
  · simpa only [hc, Nat.cast_add, Nat.cast_ofNat] using hr
  · simpa [hc] using hlower

/-- Below the upper budget of `FourRateSmoothMca128.BudgetWindow`, with no lower bound on the
field, every smooth domain of size a multiple of 512 violates the 128-bit threshold at all
four sponsor rates at the radii of `FourRateSmoothMcaLift.failureRadius`. -/
theorem all_rates_bad_of_budget_le (D : I ↪ F) [ReedSolomon.Smooth D] {r : ℕ}
    (hr : 0 < r) (hn : Fintype.card I = r*512) (hq : 2048 < Fintype.card F)
    (hbudget : Fintype.card F / 2^128 ≤ upperBudget)
    (j : Fin 4) (δ : ℝ≥0) (hδ : failureRadius j ≤ δ) :
    ((prizeThreshold : ℝ≥0) : ℝ≥0∞) <
      epsMCA (F := F) (ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → F)) δ := by
  let h : Fin 4 → ℕ := ![128,256,256,512]
  let d : Fin 4 → ℕ := ![64,64,32,32]
  let s : Fin 4 → ℕ := ![4*r,2*r,2*r,r]
  have hdim : prizeDimension (ι := I) j = d j * s j := by
    fin_cases j <;> simp [prizeDimension,prizeDenominator,hn,d,s] <;> omega
  have hcap : upperBudget ≤ 2^118 := by decide
  rw [hdim]
  apply power_bad_small D (h := h j)
  · fin_cases j <;> simp [s] <;> omega
  · fin_cases j <;> decide
  · fin_cases j <;> decide
  · fin_cases j <;> decide
  · rw [hn]; fin_cases j <;> simp [s,h] <;> omega
  · fin_cases j
    · exact ⟨7,rfl⟩
    · exact ⟨8,rfl⟩
    · exact ⟨8,rfl⟩
    · exact ⟨9,rfl⟩
  · fin_cases j <;> simp [h] <;> omega
  · exact hbudget.trans hcap
  · refine (Nat.mul_le_mul_left _ hbudget).trans_lt ?_
    fin_cases j <;> simp only [d,h,Nat.choose_eq_descFactorial_div_factorial] <;> decide
  · fin_cases j <;> norm_num [h,d,failureRadius] at hδ ⊢ <;> exact hδ

/-- Failing radii for every field with fewer than `2^256` elements, in prize-rate order. -/
noncomputable def universalFailureRadius : Fin 4 → ℝ≥0 := ![63/128, 95/128, 111/128, 239/256]

/-- Over every finite field with fewer than `2^256` elements, every smooth domain of size a
multiple of 512 violates the 128-bit threshold at all four sponsor rates at the radii of
`universalFailureRadius`. -/
theorem all_rates_bad_below_256 (D : I ↪ F) [ReedSolomon.Smooth D] {r : ℕ}
    (hr : 0 < r) (hn : Fintype.card I = r*512) (hq : 2048 < Fintype.card F)
    (hq256 : Fintype.card F < 2^256)
    (j : Fin 4) (δ : ℝ≥0) (hδ : universalFailureRadius j ≤ δ) :
    ((prizeThreshold : ℝ≥0) : ℝ≥0∞) <
      epsMCA (F := F) (ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → F)) δ := by
  let h : Fin 4 → ℕ := ![256,256,256,512]
  let d : Fin 4 → ℕ := ![128,64,32,32]
  let s : Fin 4 → ℕ := ![2*r,2*r,2*r,r]
  have hdim : prizeDimension (ι := I) j = d j * s j := by
    fin_cases j <;> simp [prizeDimension,prizeDenominator,hn,d,s] <;> omega
  have hU : Fintype.card F / 2^128 ≤ 2^128-1 := by
    have := Nat.div_lt_of_lt_mul (show Fintype.card F < 2^128 * 2^128 by
      rw [← pow_add]; exact hq256)
    omega
  rw [hdim]
  apply power_bad_any D (h := h j) (U := 2^128-1)
  · fin_cases j <;> simp [s] <;> omega
  · fin_cases j <;> decide
  · fin_cases j <;> decide
  · fin_cases j <;> decide
  · rw [hn]; fin_cases j <;> simp [s,h] <;> omega
  · fin_cases j
    · exact ⟨8,rfl⟩
    · exact ⟨8,rfl⟩
    · exact ⟨8,rfl⟩
    · exact ⟨9,rfl⟩
  · fin_cases j <;> simp [h] <;> omega
  · exact hU
  · fin_cases j <;> simp only [d,h,Nat.choose_eq_descFactorial_div_factorial] <;> decide
  · fin_cases j <;> norm_num [h,d,universalFailureRadius] at hδ ⊢ <;> exact hδ

/-- The operational radius of every positive interleaving width is at most the universal
failing radius, over every field with fewer than `2^256` elements. -/
theorem threshold_le_universalFailureRadius (D : I ↪ F) [ReedSolomon.Smooth D] {r : ℕ}
    (hr : 0 < r) (hn : Fintype.card I = r*512) (hq : 2048 < Fintype.card F)
    (hq256 : Fintype.card F < 2^256) (j : Fin 4) (width : ℕ) [NeZero width] :
    MCAThresholdLedger.mcaDeltaStar (F := F)
      ((ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → F)) ^⋈ (Fin width))
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ≤ universalFailureRadius j := by
  apply MCAThresholdLedger.mcaDeltaStar_le_of_bad
  rw [epsMCA_interleaved_eq]
  exact all_rates_bad_below_256 D hr hn hq hq256 j _ le_rfl

/-- The operational radius is at most `FourRateSmoothMcaLift.failureRadius` whenever the
budget is at most the upper end of the window. -/
theorem threshold_le_failureRadius_of_budget_le (D : I ↪ F) [ReedSolomon.Smooth D] {r : ℕ}
    (hr : 0 < r) (hn : Fintype.card I = r*512) (hq : 2048 < Fintype.card F)
    (hbudget : Fintype.card F / 2^128 ≤ upperBudget) (j : Fin 4) (width : ℕ)
    [NeZero width] :
    MCAThresholdLedger.mcaDeltaStar (F := F)
      ((ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → F)) ^⋈ (Fin width))
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ≤ failureRadius j := by
  apply MCAThresholdLedger.mcaDeltaStar_le_of_bad
  rw [epsMCA_interleaved_eq]
  exact all_rates_bad_of_budget_le D hr hn hq hbudget j _ le_rfl

end ProximityGap.FieldUniformMcaCeilings

#print axioms ProximityGap.FieldUniformMcaCeilings.all_rates_bad_of_budget_le
#print axioms ProximityGap.FieldUniformMcaCeilings.all_rates_bad_below_256
#print axioms ProximityGap.FieldUniformMcaCeilings.threshold_le_universalFailureRadius
