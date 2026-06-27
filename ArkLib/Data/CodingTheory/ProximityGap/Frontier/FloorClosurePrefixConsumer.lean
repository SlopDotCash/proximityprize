/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.FloorClosureSuccessorScanner

/-!
# Prefix-plus-successor floor closure consumers

`FloorClosureSuccessorScanner` turns verified prefix evidence plus a concrete successor theorem into
uniform singleton exactness for the floor-bad candidate list.  The main floor-closure contract then
feeds that uniform exactness into the Linnik and Thorner-Zaman consumer theorems.

This file records the direct composition.  It does not prove the successor theorem, the least-prime
supply, or the budgeted global-max incidence certificate; it removes only the bookkeeping gap
between finite-rung scanners and the prize-facing consumers.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.FloorFiniteRungUniformityBarrier
open ArkLib.ProximityGap.Frontier.FloorLocalization
open ArkLib.ProximityGap.Frontier.FloorLinnikTZClosure

namespace ArkLib.ProximityGap.Frontier.FloorClosureContract

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Prefix evidence plus the concrete successor theorem can be fed directly into the sharp Linnik
budgeted-global-max incidence consumer. -/
theorem worstCaseIncidenceBounded_of_linnik_prefix_successor_budgetedMax
    (FloorBad : ℕ -> ℕ -> Prop) {cutoff : ℕ}
    (hcutoff : 4 ≤ cutoff)
    (hprefix : VerifiedPrefix 4 cutoff (CandidateListExactAt FloorBad))
    (hstep : CandidateListExactSuccessor FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax : FamilyContainsBudgetedGlobalMax F C δ R B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_linnik_candidateListExactSmallestBudgetedMaxContract
    (F := F) (A := A) FloorBad
    (candidateListExactSmallestFamily_of_verifiedPrefix_and_successorStep
      FloorBad hcutoff hprefix hstep)
    hLeast a ha hcardPrime hcardMod hcardPrize C δ hmax

/-- Delta-star consumer for the prefix-plus-successor Linnik route in the sharp
budgeted-global-max form. -/
theorem deltaStar_pin_of_linnik_prefix_successor_budgetedMax
    (FloorBad : ℕ -> ℕ -> Prop) {cutoff : ℕ}
    (hcutoff : 4 ≤ cutoff)
    (hprefix : VerifiedPrefix 4 cutoff (CandidateListExactAt FloorBad))
    (hstep : CandidateListExactSuccessor FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax : FamilyContainsBudgetedGlobalMax F C δ R B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_linnik_candidateListExactSmallestBudgetedMaxContract
    (F := F) (A := A) FloorBad
    (candidateListExactSmallestFamily_of_verifiedPrefix_and_successorStep
      FloorBad hcutoff hprefix hstep)
    hLeast a ha hcardPrime hcardMod hcardPrize C εstar hδ hmax hbudget

/-- Prefix evidence plus the concrete successor theorem can be fed directly into the sharp
Thorner-Zaman budgeted-global-max incidence consumer. -/
theorem worstCaseIncidenceBounded_of_tz_prefix_successor_budgetedMax
    (FloorBad : ℕ -> ℕ -> Prop) {cutoff : ℕ}
    (hcutoff : 4 ≤ cutoff)
    (hprefix : VerifiedPrefix 4 cutoff (CandidateListExactAt FloorBad))
    (hstep : CandidateListExactSuccessor FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax : FamilyContainsBudgetedGlobalMax F C δ R B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_tz_candidateListExactSmallestBudgetedMaxContract
    (F := F) (A := A) FloorBad
    (candidateListExactSmallestFamily_of_verifiedPrefix_and_successorStep
      FloorBad hcutoff hprefix hstep)
    hβ hTZfam a ha hcardPrime hcardMod hcardPrize C δ hmax

/-- Delta-star consumer for the prefix-plus-successor Thorner-Zaman route in the sharp
budgeted-global-max form. -/
theorem deltaStar_pin_of_tz_prefix_successor_budgetedMax
    (FloorBad : ℕ -> ℕ -> Prop) {cutoff : ℕ}
    (hcutoff : 4 ≤ cutoff)
    (hprefix : VerifiedPrefix 4 cutoff (CandidateListExactAt FloorBad))
    (hstep : CandidateListExactSuccessor FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax : FamilyContainsBudgetedGlobalMax F C δ R B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_tz_candidateListExactSmallestBudgetedMaxContract
    (F := F) (A := A) FloorBad
    (candidateListExactSmallestFamily_of_verifiedPrefix_and_successorStep
      FloorBad hcutoff hprefix hstep)
    hβ hTZfam a ha hcardPrime hcardMod hcardPrize C εstar hδ hmax hbudget

#print axioms worstCaseIncidenceBounded_of_linnik_prefix_successor_budgetedMax
#print axioms deltaStar_pin_of_linnik_prefix_successor_budgetedMax
#print axioms worstCaseIncidenceBounded_of_tz_prefix_successor_budgetedMax
#print axioms deltaStar_pin_of_tz_prefix_successor_budgetedMax

end ArkLib.ProximityGap.Frontier.FloorClosureContract
