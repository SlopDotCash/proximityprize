/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothCubicCharacteristic
import ArkLib.Research.ProximityGap.Frontier.ThreeHeadThresholdCurve
import ArkLib.Research.ProximityGap.SecondPrimeRankReview

/-! # The three-head threshold on smooth domains over finite fields

The order of the domain discharges the characteristic assumption for the
entire five-eighths plateau and the following budget-dependent crossing. -/

namespace ArkLib.ProximityGap.Frontier.SmoothCubicBudgetWindow

open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger TerminalDomainSecurity
open ProximityPrize
open scoped NNReal ENNReal

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]

/-- For every smooth domain and positive interleaving width, the first failing
error count throughout this whole budget interval is `max 671088640 (B / 3)`. -/
theorem classification (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = n)
    {B : ℕ} (hB : Fintype.card F / 2 ^ 128 = B) (hl : 1565873494 ≤ B)
    (hu : B ≤ 2147483648) (m : ℕ) [NeZero m] :
    let b : ℝ≥0 := ((max 671088640 (B / 3) : ℕ) : ℝ≥0) / n
    mcaDeltaStar (F := F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin m)) tolerance = b ∧
      ∀ δ : ℝ≥0, epsMCA (F := F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin m)) δ ≤
        tolerance ↔ δ < b := by
  classical
  have hchar := SmoothCubicCharacteristic.characteristic D hn (by omega)
  have hp : 1744830589 < ringChar F := by omega
  dsimp only
  by_cases h : B ≤ 2013265922
  · rw [max_eq_left (by omega : B / 3 ≤ 671088640)]
    rw [show ((671088640 : ℕ) : ℝ≥0) / n = 5 / 8 by norm_num [n]]
    exact FiveEighthsPlateauThreshold.classification D hn hp (by omega) (by omega) m
  · rw [max_eq_right (by omega : 671088640 ≤ B / 3)]
    exact UniversalCubicBudgetWindow.classification D hn hp hB (by omega) hu m

/-- At each of 44,739,242 consecutive Hamming counts, the exact error
probability is determined by the field order and the error count. -/
theorem exact_eps (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = n)
    (hl : 2305843008139952128 ≤ Fintype.card F) (hu : Fintype.card F < 2 ^ 256)
    {e : ℕ} (he₁ : 671088640 ≤ e) (he₂ : e ≤ 715827881) (m : ℕ) [NeZero m] :
    epsMCA (F := F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin m)) ((e : ℝ≥0) / n) =
      ((3 * (e + 1) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  have hchar := SmoothCubicCharacteristic.characteristic D hn hu
  apply ThreeHeadThresholdCurve.exact_eps D hn (p := ringChar F) (by omega) he₁ he₂ _ m
  apply (Nat.choose_le_choose 2 (by omega : 3 * (e + 1) ≤ 2147483648)).trans
  rw [Nat.choose_two_right]
  omega

/-- The universal support-rank procedure returns the same first bad count for
every code in the smooth-field interval. -/
theorem rank_answer (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = n)
    {B : ℕ} (hB : Fintype.card F / 2 ^ 128 = B) (hl : 1565873494 ≤ B)
    (hu : B ≤ 2147483648) : (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k).map Fin.val =
      some (max 671088640 (B / 3)) := by
  classical
  let e := max 671088640 (B / 3)
  have he : e < Fintype.card I := by rw [hn]; dsimp [e, n]; omega
  let ix : Fin (Fintype.card I + 1) := ⟨e, by omega⟩
  have hv : ix.val = e := rfl
  have hs := (classification D hn hB hl hu 1).1
  rw [mcaDeltaStar_interleaved_eq] at hs
  have ht : ((prizeThreshold : ℝ≥0) : ℝ≥0∞) = tolerance := by norm_num [prizeThreshold, tolerance]
  have h := SecondPrimeRankReview.rankAnswer_of_interior_supremum D
    (prizeThreshold : ℝ≥0) k ix he (by rw [hv, ht, hn]; exact hs)
  exact congrArg (Option.map Fin.val) h

end ArkLib.ProximityGap.Frontier.SmoothCubicBudgetWindow
