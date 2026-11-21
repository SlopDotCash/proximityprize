/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondBudgetCharacteristic
import ArkLib.Research.ProximityGap.Frontier.UniversalCubicThreshold
import ArkLib.Research.ProximityGap.SecondPrimeRankReview

/-! # Exact MCA on every smooth domain at budget twice the length -/

namespace ProximityPrize.SecondBudgetSmoothReview
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.Frontier ArkLib.ProximityGap.Frontier.TerminalDomainSecurity
open Code
open scoped NNReal ENNReal

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]

/-- All positive widths have the same exact cutoff throughout this field band.
The field order and the smooth domain imply the characteristic condition. -/
theorem classification (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = n)
    (hB : Fintype.card F / 2 ^ 128 = 2147483648) (m : ℕ) [NeZero m] :
    mcaDeltaStar (F := F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin m)) tolerance = boundary ∧
      ∀ δ : ℝ≥0, epsMCA (F := F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin m)) δ ≤
        tolerance ↔ δ < boundary := by
  classical
  exact UniversalCubicThreshold.classification D hn (p := ringChar F)
    (SecondBudgetCharacteristic.smooth D (hn ▸ by decide) hB) hB m

/-- The universal supplied-domain rank answer returns the first failing integer explicitly. -/
theorem rank_answer (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = n)
    (hB : Fintype.card F / 2 ^ 128 = 2147483648) :
    (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k).map Fin.val = some 715827882 := by
  classical
  let index : Fin (Fintype.card I + 1) := ⟨715827882, by rw [hn]; decide⟩
  have hv : index.val = 715827882 := rfl
  have he : index.val < Fintype.card I := by rw [hv, hn]; decide
  have hs := (classification D hn hB 1).1
  rw [mcaDeltaStar_interleaved_eq] at hs
  have ht : ((prizeThreshold : ℝ≥0) : ℝ≥0∞) = tolerance := by
    norm_num [prizeThreshold, tolerance]
  have h := SecondPrimeRankReview.rankAnswer_of_interior_supremum D
    (prizeThreshold : ℝ≥0) k index he (by rw [hv, hn, ht]; exact hs)
  exact congrArg (Option.map Fin.val) h

#print axioms classification
#print axioms rank_answer
end ProximityPrize.SecondBudgetSmoothReview
