/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R160PuncturedUniqueBudgetConsumer

/-!
# LANE HLOW (#466 round 161): scanner for failure of the punctured unique slice

R159/R160 prove the positive direction: the punctured unique-decoding inequality gives
`PuncturedListBudget dom k a 1`, hence a safe large-zero budget `n`.

This file records the matching failure localization.  Any counterexample to the `B = 1`
punctured-list socket must exhibit a safe non-support-eligible line on which the punctured
unique-decoding inequality itself fails.  This is a small but useful scanner: future countermodels
cannot live in the unique-decoding slice.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Finset

namespace ProximityGap.LargeZeroWitnessSplit.Frontier.R161PuncturedUniqueFailureScanner

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.LowProfileCoupled
open ProximityGap.LargeZeroWitnessSplit
open ProximityGap.LargeZeroWitnessSplit.Frontier.R159PuncturedUniqueDecodingSlice

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- A line with at least two appearing codewords cannot lie in the punctured unique-decoding
slice. -/
theorem not_punctured_unique_of_lineAppearingCodewords_card_gt_one
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (u₀ u₁ : Fin n → F)
    (hgt : 1 < (lineAppearingCodewords dom k a u₀ u₁).card) :
    ¬ (directionZeroSet u₁).card + k ≤ 2 * (a - (directionSupportSet u₁).card) := by
  intro hunique
  have hle := lineAppearingCodewords_card_le_one_of_punctured_unique dom hk a u₀ u₁ hunique
  exact not_lt_of_ge hle hgt

open Classical in
/-- Failure of the `B = 1` punctured-list budget localizes to a concrete safe line where the
punctured unique-decoding inequality fails. -/
theorem exists_not_punctured_unique_of_not_puncturedListBudget_one
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (hnot : ¬ PuncturedListBudget dom k a 1) :
    ∃ u₀ u₁ : Fin n → F,
      ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
      1 < (lineAppearingCodewords dom k a u₀ u₁).card ∧
      ¬ (directionZeroSet u₁).card + k ≤ 2 * (a - (directionSupportSet u₁).card) := by
  classical
  simp only [PuncturedListBudget, not_forall] at hnot
  rcases hnot with ⟨u₀, hnot⟩
  rcases hnot with ⟨u₁, hnot⟩
  push Not at hnot
  rcases hnot with ⟨hne, hsafe, hgt⟩
  exact ⟨u₀, u₁, hne, hsafe, hgt,
    not_punctured_unique_of_lineAppearingCodewords_card_gt_one dom hk a u₀ u₁ hgt⟩

end ProximityGap.LargeZeroWitnessSplit.Frontier.R161PuncturedUniqueFailureScanner

/-! ## Axiom audit -/
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R161PuncturedUniqueFailureScanner.not_punctured_unique_of_lineAppearingCodewords_card_gt_one
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R161PuncturedUniqueFailureScanner.exists_not_punctured_unique_of_not_puncturedListBudget_one
