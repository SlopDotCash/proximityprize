/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R161PuncturedUniqueFailureScanner

/-!
# LANE HLOW (#466 round 162): safe-branch failure leaves the unique slice

R161 localizes failure of the `B = 1` punctured-list socket.  The weld-facing safe branch is the
corresponding bad-scalar budget with the support factor `n`.  This file composes the two:

if the large-zero-safe branch cannot be bounded by `n`, then the counterexample line must fail the
punctured unique-decoding inequality.  Thus future attacks on the safe branch can ignore the
unique-decoding region completely.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Finset

namespace ProximityGap.LargeZeroWitnessSplit.Frontier.R162LargeZeroSafeUniqueFailureScanner

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.LowProfileCoupled
open ProximityGap.LargeZeroWitnessSplit
open ProximityGap.LargeZeroWitnessSplit.Frontier.R161PuncturedUniqueFailureScanner

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Failure of the weld-facing safe large-zero budget `n` localizes to a concrete safe line
outside the punctured unique-decoding slice. -/
theorem exists_not_punctured_unique_of_not_largeZeroSafe_budget_n
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (hnot : ¬ LargeZeroSafeLineBadScalarsBudgeted dom k a n) :
    ∃ u₀ u₁ : Fin n → F,
      ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
      1 < (lineAppearingCodewords dom k a u₀ u₁).card ∧
      ¬ (directionZeroSet u₁).card + k ≤ 2 * (a - (directionSupportSet u₁).card) := by
  have hpunctured :
      ¬ PuncturedListBudget dom k a 1 :=
    not_puncturedListBudget_of_not_largeZeroSafeLineBadScalarsBudgeted dom k a 1
      (by
        simpa using hnot)
  exact exists_not_punctured_unique_of_not_puncturedListBudget_one dom hk a hpunctured

end ProximityGap.LargeZeroWitnessSplit.Frontier.R162LargeZeroSafeUniqueFailureScanner

/-! ## Axiom audit -/
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R162LargeZeroSafeUniqueFailureScanner.exists_not_punctured_unique_of_not_largeZeroSafe_budget_n
