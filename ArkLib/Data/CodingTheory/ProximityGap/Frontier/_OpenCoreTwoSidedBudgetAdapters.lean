/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreBudgetAdapters
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TwoSidedCapstone

/-!
# LANE I (#466): two-sided open-core budget adapters

The round-14 two-sided capstone identifies `ε_mca(C, δ) <= B/q` with the stackwise incidence
budget `WorstCaseIncidenceBounded C δ B`.  This file records the public-budget wrappers used by
downstream certificates: a sharp internal budget may be consumed at any larger published budget,
both on the pointwise-good side and on the strict-interior `δ*` side.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open scoped NNReal ENNReal
open ProximityGap
open ProximityGap.OpenCoreConditionalPin
open ProximityGap.OpenCoreBudgetAdapters

namespace ArkLib.ProximityGap.Frontier.OpenCoreTwoSidedBudgetAdapters

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Pointwise-goodness at a sharp natural budget gives the incidence Prop at any larger public
budget. -/
theorem incidence_of_epsMCA_le_budget_of_le
    (C : Set (ι → A)) (δ : ℝ≥0) {B B' : ℕ}
    (hBB : B ≤ B')
    (hGood : epsMCA (F := F) (A := A) C δ
      ≤ ((B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))) :
    WorstCaseIncidenceBounded (F := F) (A := A) C δ B' :=
  worstCaseIncidenceBounded_mono_budget (F := F) (A := A) C δ hBB
    (TwoSidedCapstone.worstCaseIncidenceBounded_of_epsMCA_le (F := F) (A := A) C δ hGood)

/-- A sharp pointwise-goodness certificate pins `δ*` at any larger normalized public budget. -/
theorem deltaStar_pin_of_epsMCA_le_budget_of_le
    (C : Set (ι → A)) {δ : ℝ≥0} {B B' : ℕ}
    (hδ : δ ≤ 1)
    (hBB : B ≤ B')
    (hGood : epsMCA (F := F) (A := A) C δ
      ≤ ((B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))) :
    δ ≤ MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C
      ((B' : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  worstCaseIncidence_pin_budget (F := F) (A := A) C hδ
    (incidence_of_epsMCA_le_budget_of_le (F := F) (A := A) C δ hBB hGood)

/-- The two-sided capstone's exact `iff`, relaxed to a larger public incidence budget in the
forward direction.  The reverse remains at the public budget `B'`, so this is a one-way adapter
from sharp analytic error to coarser public incidence. -/
theorem epsMCA_le_budget_implies_public_incidence_iff
    (C : Set (ι → A)) (δ : ℝ≥0) {B B' : ℕ} (hBB : B ≤ B') :
    epsMCA (F := F) (A := A) C δ ≤ ((B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) →
      WorstCaseIncidenceBounded (F := F) (A := A) C δ B' :=
  incidence_of_epsMCA_le_budget_of_le (F := F) (A := A) C δ hBB

/-- Strict-interior `δ*` transport at a sharp budget, followed by publication at any larger
incidence budget. -/
theorem incidence_of_lt_deltaStar_budget_of_le
    (C : Set (ι → A)) {δ : ℝ≥0} {B B' : ℕ}
    (hBB : B ≤ B')
    (hδ : δ < MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C
      ((B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))) :
    WorstCaseIncidenceBounded (F := F) (A := A) C δ B' :=
  worstCaseIncidenceBounded_mono_budget (F := F) (A := A) C δ hBB
    (OpenCoreConverse.worstCaseIncidence_of_lt_mcaDeltaStar (F := F) (A := A) C hδ)

/-- The budget-relaxed strict-interior capstone: strictly below the sharp `δ*` floor gives the
public incidence budget, while public incidence at `B'` pins `δ*` at the public error `B'/q`. -/
theorem deltaStar_strictInterior_public_budget_pair
    (C : Set (ι → A)) {δ : ℝ≥0} {B B' : ℕ} (hδ1 : δ ≤ 1) (hBB : B ≤ B') :
    (δ < MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C
        ((B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) →
        WorstCaseIncidenceBounded (F := F) (A := A) C δ B')
    ∧ (WorstCaseIncidenceBounded (F := F) (A := A) C δ B' →
        δ ≤ MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C
          ((B' : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))) :=
  ⟨incidence_of_lt_deltaStar_budget_of_le (F := F) (A := A) C hBB,
    fun hI => worstCaseIncidence_pin_budget (F := F) (A := A) C hδ1 hI⟩

end ArkLib.ProximityGap.Frontier.OpenCoreTwoSidedBudgetAdapters

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.OpenCoreTwoSidedBudgetAdapters.incidence_of_epsMCA_le_budget_of_le
#print axioms
  ArkLib.ProximityGap.Frontier.OpenCoreTwoSidedBudgetAdapters.deltaStar_pin_of_epsMCA_le_budget_of_le
#print axioms
  ArkLib.ProximityGap.Frontier.OpenCoreTwoSidedBudgetAdapters.incidence_of_lt_deltaStar_budget_of_le
#print axioms
  ArkLib.ProximityGap.Frontier.OpenCoreTwoSidedBudgetAdapters.deltaStar_strictInterior_public_budget_pair
