/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarAllFieldPlateau
import ArkLib.Research.ProximityGap.Frontier.QuarterRateTwoRichFloor
import ArkLib.Research.ProximityGap.Frontier.SmoothCubicCharacteristic
import ArkLib.Research.ProximityGap.SecondPrimeRankReview

/-! # The exact two-head threshold over smooth finite-field domains at quarter rate -/
namespace ArkLib.ProximityGap.Frontier.SmoothQuarterTwoHeadWindow

open Code _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger ProximityPrize
open scoped NNReal ENNReal

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I]

omit [Nonempty I] [DecidableEq I] in
/-- The subgroup order bounds the extension degree by five, making the characteristic
large enough throughout the two-head field-size interval. -/
theorem characteristic (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 2^30)
    (hl : 2505397586^5 < Fintype.card F) (hu : Fintype.card F < 2^160) :
    2505397586 < ringChar F := by
  classical
  obtain ⟨equiv,_⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  let H := ReedSolomon.Smooth.H D
  let _ : Fintype H := Fintype.ofEquiv I equiv
  have hd : 2^30 ∣ Fintype.card F-1 := by
    rw [← hn,Fintype.card_congr equiv]
    simpa only [Nat.card_eq_fintype_card,Fintype.card_units] using Subgroup.card_subgroup_dvd_card H
  obtain ⟨e,hp,hq⟩ := FiniteField.card F (ringChar F)
  rw [hq] at hd hl hu
  have deg := SmoothCubicCharacteristic.degree_le_five hp e.pos hd hu
  by_contra! small
  exact hl.not_ge ((Nat.pow_le_pow_right hp.pos deg).trans (Nat.pow_le_pow_left small 5))

/-- The full grid-point probability curve through the saturated predecessor in
every smooth prize-size field, with no lower bound on the scalar budget. -/
theorem full_grid_mass (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 1073741824)
    (hq : Fintype.card F < 2^256) {e : ℕ} (he : e ≤ 447392427) (m : ℕ) [NeZero m] :
    epsMCA (F := F) ((ReedSolomon.code D 268435456 : Set (I → F)) ^⋈ (Fin m)) ((e : ℝ≥0)/1073741824) =
      ((if e<402653184 then e+1 else 2*(e+1) : ℕ) : ℝ≥0∞)/Fintype.card F := by
  have hnR : (Fintype.card I : ℝ≥0)=1073741824 := by exact_mod_cast hn
  rw [epsMCA_interleaved_eq,← hnR]
  by_cases low : e<402653184
  · rw [ite_eq_left low]
    exact ApolarAllFieldPlateau.preunique_mass D (a:=402653184) (by decide) (by omega) (by omega) low
  · rw [ite_eq_right low]
    have hp := SmoothCubicCharacteristic.characteristic D hn hq
    apply QuarterRateTwoRichFloor.exact_through_saturation D hn (by omega) he
    intro i hi hj hz
    exact (by omega : ¬ringChar F ≤ i) (Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff F (ringChar F) i).mp hz))

/-- The exact budget criterion for safety at the last computed quarter-rate grid point. -/
theorem predecessor_good_iff (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 1073741824)
    (hq : Fintype.card F < 2^256) (m : ℕ) [NeZero m] :
    epsMCA (F := F) ((ReedSolomon.code D 268435456 : Set (I → F)) ^⋈ (Fin m)) (447392427/1073741824) ≤
      (epsStar : ℝ≥0∞) ↔ 894784856 ≤ Fintype.card F/2^128 := by
  have h := full_grid_mass D hn hq (e:=447392427) (by decide) m
  change epsMCA (F:=F) _ (447392427/1073741824) = ((894784856:ℕ):ℝ≥0∞)/Fintype.card F at h
  rw [h,PrizeShapeRateHalfBracket.epsStar_coe_eq_natCast_inv,← one_div]
  exact BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide)

/-- Closed-ball security at every positive interleaving width is equivalent to a
strict real-radius inequality for each budget in the window. -/
theorem classification (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 1073741824)
    {B : ℕ} (hB : Fintype.card F / 2^128 = B)
    (hl : 805306370 ≤ B) (hu : B ≤ 894784857) (m : ℕ) [NeZero m] :
    let r : ℝ≥0 := ((B/2 : ℕ) : ℝ≥0)/1073741824
    mcaDeltaStar (F := F) ((ReedSolomon.code D 268435456 : Set (I → F)) ^⋈ (Fin m))
      (epsStar : ℝ≥0∞) = r ∧
    ∀ δ : ℝ≥0, epsMCA (F := F) ((ReedSolomon.code D 268435456 : Set (I → F)) ^⋈ (Fin m))
      δ ≤ (epsStar : ℝ≥0∞) ↔ δ < r := by
  apply QuarterRateQuadraticSafety.budget_window_of_mass D hn hB hl (by omega) _ m
  have h := full_grid_mass D hn (by omega) (e:=B/2-1) (by omega) 1
  have hnR : (Fintype.card I : ℝ≥0)=1073741824 := by exact_mod_cast hn
  rw [epsMCA_interleaved_eq,ite_eq_right (by omega : ¬B/2-1<402653184),← hnR] at h
  exact h

/-- The spike regime, the plateau, and the budget-dependent two-head regime
give one formula on every smooth production-length field through the last budget. -/
theorem complete_curve (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 1073741824)
    {B : ℕ} (hB : Fintype.card F / 2^128 = B) (hu : B ≤ 894784857) (m : ℕ) [NeZero m] :
    let r : ℝ≥0 := ((min B (max 402653184 (B/2)) : ℕ) : ℝ≥0)/1073741824
    mcaDeltaStar (F := F) ((ReedSolomon.code D 268435456 : Set (I → F)) ^⋈ (Fin m))
      (epsStar : ℝ≥0∞) = r ∧
    ∀ δ : ℝ≥0, epsMCA (F := F) ((ReedSolomon.code D 268435456 : Set (I → F)) ^⋈ (Fin m))
      δ ≤ (epsStar : ℝ≥0∞) ↔ δ < r := by
  dsimp only
  by_cases below : B ≤ 805306369
  · rw [max_eq_left (by omega : B/2 ≤ 402653184)]
    have h := ApolarAllFieldPlateau.classification D (k:=268435456) (a:=402653184)
      (by decide) (by omega) (by omega) (by decide : 0<2^128) hB (by omega) m
    dsimp only at h
    rw [hn] at h
    simpa only [PrizeShapeRateHalfBracket.epsStar_coe_eq_natCast_inv,one_div,Nat.cast_ofNat] using h
  · rw [max_eq_right (by omega : 402653184 ≤ B/2),min_eq_right (by omega : B/2≤B)]
    exact classification D hn hB (by omega) hu m

/-- The rank calculation gives the same three-regime answer, including budget zero. -/
theorem complete_rank_answer (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 1073741824)
    {B : ℕ} (hB : Fintype.card F / 2^128 = B) (hu : B ≤ 894784857) :
    (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) 268435456).map Fin.val =
      some (min B (max 402653184 (B/2))) := by
  let j := min B (max 402653184 (B/2))
  have inside : j < Fintype.card I := by dsimp [j]; omega
  let ix : Fin (Fintype.card I + 1) := ⟨j,by omega⟩
  have hs := (complete_curve D hn hB hu 1).1
  rw [mcaDeltaStar_interleaved_eq] at hs
  have ht : ((prizeThreshold : ℝ≥0) : ℝ≥0∞) = (epsStar : ℝ≥0∞) := by
    norm_num [prizeThreshold,epsStar]
  have h := SecondPrimeRankReview.rankAnswer_of_interior_supremum D (prizeThreshold : ℝ≥0) 268435456 ix
    inside (by change _ = (j : ℝ≥0)/Fintype.card I; rw [ht,hn]; exact hs)
  exact congrArg (Option.map Fin.val) h

/-- The finite support-rank search returns this same first failing error count. -/
theorem rank_answer (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 1073741824)
    {B : ℕ} (hB : Fintype.card F / 2^128 = B) (hl : 805306370 ≤ B) (hu : B ≤ 894784857) :
    (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) 268435456).map Fin.val = some (B/2) := by
  simpa only [max_eq_right (by omega : 402653184 ≤ B/2),min_eq_right (by omega : B/2≤B)] using
    complete_rank_answer D hn hB hu

#print axioms full_grid_mass
#print axioms predecessor_good_iff
#print axioms complete_curve
#print axioms complete_rank_answer
#print axioms classification
#print axioms rank_answer
end ArkLib.ProximityGap.Frontier.SmoothQuarterTwoHeadWindow
