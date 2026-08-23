/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreBudgetAdapters
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._StackProfileDominationInterface
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.StackMaximizerDomination

/-!
# Budget-relaxed consumers for profile and maximizer certificates

The profile/maximizer APIs reduce the prize floor to a finite or one-stack certificate for the
actual MCA bad-scalar count.  Those certificates often prove a sharper internal budget `B`; the
public prize consumer may reserve a larger budget `B'`.  This file wires the root
`OpenCoreBudgetAdapters` monotonicity into those two proof surfaces.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.OpenCoreProfileBudgetAdapters

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

namespace Profile

open ArkLib.ProximityGap.Frontier.StackProfileDominationInterface

/-- One-stack profile-interface budgets are monotone in the natural-number budget. -/
theorem stackBounded_mono_budget
    (C : Set (ι -> A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) {B B' : ℕ}
    (hBB : B ≤ B')
    (h : StackBounded F C δ u B) :
    StackBounded F C δ u B' :=
  le_trans h hBB

/-- Finite-family profile-interface budgets are monotone in the natural-number budget. -/
theorem familyBounded_mono_budget
    (C : Set (ι -> A)) (δ : ℝ≥0) (R : Finset (WordStack A (Fin 2) ι)) {B B' : ℕ}
    (hBB : B ≤ B')
    (h : FamilyBounded F C δ R B) :
    FamilyBounded F C δ R B' := by
  intro r hr
  exact stackBounded_mono_budget C δ r hBB (h r hr)

/-- Profile caps budgeted at `B` are also budgeted at any larger `B'`. -/
theorem profileBudgeted_mono_budget {P : Type} {cap : P -> ℕ} {B B' : ℕ}
    (hBB : B ≤ B')
    (h : ProfileBudgeted cap B) :
    ProfileBudgeted cap B' :=
  fun p => le_trans (h p) hBB

/-- Direct profile-cap certificates can be consumed at a larger public budget `B'`. -/
theorem deltaStar_pin_of_profileCaps_budget_of_le
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B B' : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P} {cap : P -> ℕ}
    (hcap : ProfileCaps F C δ profile cap)
    (hprofileBudget : ProfileBudgeted cap B)
    (hBB : B ≤ B')
    (hbudget : (B' : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreBudgetAdapters.worstCaseIncidence_pin_of_le_budget
    (F := F) (A := A) C εstar hδ hBB
    (worstCaseIncidenceBounded_of_profileCaps_budget C δ hcap hprofileBudget)
    hbudget

/-- Profile-representative certificates can be consumed at a larger public budget `B'`. -/
theorem deltaStar_pin_of_profileReps_familyBounded_of_le
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B B' : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} [Fintype P] [DecidableEq P]
    {profile : WordStack A (Fin 2) ι -> P} {cap : P -> ℕ}
    {rep : P -> WordStack A (Fin 2) ι}
    (hcap : ProfileCaps F C δ profile cap)
    (hrep : ProfileRealizedByReps F C δ profile cap rep)
    (hbounded : FamilyBounded F C δ ((Finset.univ : Finset P).image rep) B)
    (hBB : B ≤ B')
    (hbudget : (B' : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreBudgetAdapters.worstCaseIncidence_pin_of_le_budget
    (F := F) (A := A) C εstar hδ hBB
    (worstCaseIncidenceBounded_of_profileReps_familyBounded C δ hcap hrep hbounded)
    hbudget

end Profile

namespace Maximizer

open ArkLib.ProximityGap.Frontier.StackMaximizerDomination

/-- One-stack maximizer-interface budgets are monotone in the natural-number budget. -/
theorem stackBounded_mono_budget
    (C : Set (ι -> A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) {B B' : ℕ}
    (hBB : B ≤ B')
    (h : StackBounded F C δ u B) :
    StackBounded F C δ u B' :=
  le_trans h hBB

/-- A true maximizer bounded at a sharper budget `B` pins `δ*` at any larger public budget `B'`. -/
theorem deltaStar_pin_of_stackMaximizer_of_le
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B B' : ℕ}
    (hδ : δ ≤ 1)
    {uMax : WordStack A (Fin 2) ι}
    (hmax : StackDominates F C δ uMax)
    (hbounded : StackBounded F C δ uMax B)
    (hBB : B ≤ B')
    (hbudget : (B' : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreBudgetAdapters.worstCaseIncidence_pin_of_le_budget
    (F := F) (A := A) C εstar hδ hBB
    (worstCaseIncidenceBounded_of_stackDominates C δ hmax hbounded)
    hbudget

end Maximizer

end ArkLib.ProximityGap.Frontier.OpenCoreProfileBudgetAdapters

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.OpenCoreProfileBudgetAdapters.Profile.stackBounded_mono_budget
#print axioms ArkLib.ProximityGap.Frontier.OpenCoreProfileBudgetAdapters.Profile.familyBounded_mono_budget
#print axioms ArkLib.ProximityGap.Frontier.OpenCoreProfileBudgetAdapters.Profile.profileBudgeted_mono_budget
#print axioms ArkLib.ProximityGap.Frontier.OpenCoreProfileBudgetAdapters.Profile.deltaStar_pin_of_profileCaps_budget_of_le
#print axioms ArkLib.ProximityGap.Frontier.OpenCoreProfileBudgetAdapters.Profile.deltaStar_pin_of_profileReps_familyBounded_of_le
#print axioms ArkLib.ProximityGap.Frontier.OpenCoreProfileBudgetAdapters.Maximizer.stackBounded_mono_budget
#print axioms ArkLib.ProximityGap.Frontier.OpenCoreProfileBudgetAdapters.Maximizer.deltaStar_pin_of_stackMaximizer_of_le
