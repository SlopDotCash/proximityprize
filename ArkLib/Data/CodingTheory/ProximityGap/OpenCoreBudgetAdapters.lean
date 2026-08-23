/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdBudgetMono

/-!
# Budget adapters for the open-core incidence pin

The prize-facing open core is `WorstCaseIncidenceBounded C δ B`: every stack has at most `B`
bad scalars.  Many production routes naturally prove a sharper internal budget and then need to
publish the result at the prize budget `E ≈ q·ε*`.  This file records the monotone adapters once,
so downstream certificates can keep their sharp count while consuming a larger public budget.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal
open ProximityGap
open ProximityGap.OpenCoreConditionalPin

namespace ProximityGap.OpenCoreBudgetAdapters

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- `WorstCaseIncidenceBounded` is monotone in the natural-number budget. -/
theorem worstCaseIncidenceBounded_mono_budget
    (C : Set (ι → A)) (δ : ℝ≥0) {B B' : ℕ}
    (hBB : B ≤ B')
    (hI : WorstCaseIncidenceBounded (F := F) (A := A) C δ B) :
    WorstCaseIncidenceBounded (F := F) (A := A) C δ B' := by
  intro u
  exact le_trans (hI u) hBB

/-- A sharp incidence certificate at budget `B` pins `δ*` at any larger normalized budget
`B'/q`, provided `B ≤ B'`. -/
theorem worstCaseIncidence_pin_budget_of_le
    (C : Set (ι → A)) {δ : ℝ≥0} {B B' : ℕ}
    (hδ : δ ≤ 1)
    (hBB : B ≤ B')
    (hI : WorstCaseIncidenceBounded (F := F) (A := A) C δ B) :
    δ ≤ MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C
      ((B' : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  worstCaseIncidence_pin_budget (F := F) (A := A) C hδ
    (worstCaseIncidenceBounded_mono_budget (F := F) (A := A) C δ hBB hI)

/-- A sharp incidence certificate at budget `B` also pins `δ*` at any error budget above
`B'/q`, provided `B ≤ B'`. -/
theorem worstCaseIncidence_pin_of_le_budget
    (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B B' : ℕ}
    (hδ : δ ≤ 1)
    (hBB : B ≤ B')
    (hI : WorstCaseIncidenceBounded (F := F) (A := A) C δ B)
    (hbudget : (B' : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  worstCaseIncidence_pin (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_mono_budget (F := F) (A := A) C δ hBB hI)
    hbudget

/-- If a threshold is already pinned at a sharper error budget `ε₀`, it remains pinned at any
larger error budget `ε₁`.  This is the open-core-facing wrapper around the ledger monotonicity. -/
theorem deltaStar_pin_mono_error
    (C : Set (ι → A)) {δ : ℝ≥0} {ε₀ ε₁ : ℝ≥0∞}
    (hpin : δ ≤ MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C ε₀)
    (hε : ε₀ ≤ ε₁) :
    δ ≤ MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C ε₁ :=
  le_trans hpin (MCAThresholdLedger.mcaDeltaStar_mono (F := F) (A := A) C hε)

end ProximityGap.OpenCoreBudgetAdapters

/-! ## Axiom audit -/
#print axioms ProximityGap.OpenCoreBudgetAdapters.worstCaseIncidenceBounded_mono_budget
#print axioms ProximityGap.OpenCoreBudgetAdapters.worstCaseIncidence_pin_budget_of_le
#print axioms ProximityGap.OpenCoreBudgetAdapters.worstCaseIncidence_pin_of_le_budget
#print axioms ProximityGap.OpenCoreBudgetAdapters.deltaStar_pin_mono_error
