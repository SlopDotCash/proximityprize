/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondBudgetCharacteristic
import ArkLib.Research.ProximityGap.Frontier.UniversalCubicThreshold
import ArkLib.Research.ProximityGap.RankProductionDomain

/-! # A field-order interval with the same exact rate-sixteenth MCA threshold

The safe neighbor comes from the cubic population bound. At the next error count,
three heads give a strict failure on any injective domain in the stated field band.
-/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeFieldWindow
open _root_.ProximityGap CoreDefinitions Code ProximityPrize
open HalfPredecessorBadEventRichPointBridge
open scoped NNReal ENNReal

variable {F : Type} [Field F] [Fintype F] {p : ℕ} [CharP F p]

/-- The exact scalar test on every injective domain in the twice-length budget band
over an arbitrary finite field of odd characteristic. -/
theorem good_iff (dom : Fin 1073741824 ↪ F) (hp : p ≠ 2)
    (hB : Fintype.card F / 2^128 = 2147483648) (δ : ℝ≥0) :
    epsMCA (F := F) (ReedSolomon.code dom 67108864 : Set (Fin 1073741824 → F)) δ ≤
      1/(2:ℝ≥0∞)^128 ↔ δ < 715827882/1073741824 := by
  classical
  obtain ⟨m,hprime,hm⟩ := FiniteField.card F p
  have hpow := hB
  rw [hm] at hpow
  have hchar := (SecondBudgetCharacteristic.odd_power hprime hp hpow).2
  have h := (UniversalCubicThreshold.classification dom (Fintype.card_fin _) hchar hB 1).2 δ
  rwa [epsMCA_interleaved_eq] at h

/-- The last safe grid point and the first failure for any odd characteristic. -/
theorem adjacent (dom : Fin 1073741824 ↪ F) (hp : p ≠ 2)
    (hB : Fintype.card F / 2^128 = 2147483648) :
    let C := (ReedSolomon.code dom 67108864 : Set (Fin 1073741824 → F))
    epsMCA (F := F) C (715827881/1073741824) ≤ 1/(2:ℝ≥0∞)^128 ∧
      1/(2:ℝ≥0∞)^128 < epsMCA (F := F) C (715827882/1073741824) := by
  refine ⟨(good_iff dom hp hB _).2 ?_, lt_of_not_ge (fun h => (lt_irrefl _)
    ((good_iff dom hp hB _).1 h))⟩
  exact (div_lt_div_iff_of_pos_right (by norm_num)).2 (by norm_num)

/-- The supplied-domain matrix rank formula returns the same numerical first failure
on every smooth domain in the field-order band. -/
theorem rank_answer [SampleableType F] [DecidableEq F] (dom : Fin 1073741824 ↪ F)
    [ReedSolomon.Smooth dom]
    (hB : Fintype.card F / 2^128 = 2147483648) :
    (RankReview.mcaAnswer dom (_root_.ProximityGap.prizeThreshold : ℝ≥0) 67108864).map Fin.val =
      some 715827882 := by
  let i : Fin (Fintype.card (Fin 1073741824) + 1) := ⟨715827882, by rw [Fintype.card_fin] <;> decide⟩
  obtain ⟨hM, _⟩ := RankReview.correctForEveryDomain dom (_root_.ProximityGap.prizeThreshold : ℝ≥0)
    67108864 (Or.inr (Or.inr (Or.inr (by rw [Fintype.card_fin] <;> decide))))
  have hbound : FullPrizeReview.correctBoundary (Fintype.card (Fin 1073741824)) (some i)
      (fun δ => mcaError (AffineLineGenerator F) (ReedSolomon.code dom 67108864) (δ : ℝ) ≤
        ((_root_.ProximityGap.prizeThreshold : ℝ≥0) : ℝ≥0∞)) := by
    intro δ _
    dsimp only
    rw [← epsMCA_eq_mcaError]
    have ht : ((_root_.ProximityGap.prizeThreshold : ℝ≥0) : ℝ≥0∞) = 1/(2:ℝ≥0∞)^128 := by
      norm_num [_root_.ProximityGap.prizeThreshold]
    rw [ht]
    simpa only [Fintype.card_fin, i, Nat.cast_ofNat] using good_iff (p := ringChar F) dom
      (SecondBudgetCharacteristic.ne_two_of_even_smooth dom (by rw [Fintype.card_fin] <;> decide)) hB δ
  exact congrArg (Option.map Fin.val)
    (_root_.FullPrizeReview.correctBoundary_unique Fintype.card_pos hM hbound)

#print axioms good_iff
#print axioms rank_answer
end ArkLib.ProximityGap.Frontier.SecondPrimeFieldWindow
