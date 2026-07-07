/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorClosureContract
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._StackOrbitRepresentativeReduction

/-!
# Stack-orbit representatives and floor-closure certificates are the same order

`_StackOrbitRepresentativeReduction` was developed as the stack-side quotient interface:
prove invariance, prove a representative cover, and bound the representatives.  Separately,
`_FloorClosureContract` records the off-BGK floor lane's prize-facing contract:
a finite family must contain a budgeted global maximizer for the actual MCA bad-scalar count.

Both files intentionally keep local copies of `StackBadCount` so they can be checked independently.
This bridge proves that the local representative predicates are exactly the floor-closure
predicates after unfolding those copies.  It prevents future work from treating the two interfaces
as different mathematical obligations.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ArkLib.ProximityGap.Frontier.FloorClosureContract
  (CandidateListExactSmallestFamily FloorClosureBudgetedMaxAtField
   deltaStar_pin_of_containsBudgetedGlobalMax
   floorClosureBudgetedMaxAtField_of_linnik_candidateListExactSmallestBudgetedMax
   worstCaseIncidenceBounded_of_linnik_candidateListExactSmallestBudgetedMaxContract
   deltaStar_pin_of_linnik_candidateListExactSmallestBudgetedMaxContract
   floorClosureBudgetedMaxAtField_of_tz_candidateListExactSmallestBudgetedMax
   worstCaseIncidenceBounded_of_tz_candidateListExactSmallestBudgetedMaxContract
   deltaStar_pin_of_tz_candidateListExactSmallestBudgetedMaxContract)
open ArkLib.ProximityGap.Frontier.FloorLocalization (LinnikLeastPrimeBelowPrize)
open ArkLib.ProximityGap.KKH26 (TZPrimeSupply)

namespace ArkLib.ProximityGap.Frontier.StackOrbitFloorClosureBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The stack-orbit and floor-closure local copies of the actual MCA bad-scalar count coincide. -/
theorem stackBadCount_eq_floorClosureStackBadCount
    (C : Set (ι -> A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) :
    StackOrbitRepresentativeReduction.StackBadCount F C δ u =
      FloorClosureContract.StackBadCount F C δ u := by
  rfl

/-- Representative boundedness is exactly the floor-closure family budget predicate. -/
theorem representativeStacksBounded_iff_familyBounded
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) :
    StackOrbitRepresentativeReduction.RepresentativeStacksBounded
        (F := F) (A := A) C δ R B ↔
      FloorClosureContract.FamilyBounded F C δ R B := by
  rfl

/-- Direct stack-orbit domination is exactly floor-closure family domination. -/
theorem stackDominatingRepresentativeCover_iff_familyDominates
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) :
    StackOrbitRepresentativeReduction.StackDominatingRepresentativeCover
        (F := F) (A := A) C δ R ↔
      FloorClosureContract.FamilyDominates F C δ R := by
  rfl

/-- Stack-orbit representative max containment is exactly floor-closure global-max containment. -/
theorem representativeContainsGlobalMax_iff_familyContainsGlobalMax
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) :
    StackOrbitRepresentativeReduction.RepresentativeContainsGlobalMax
        (F := F) (A := A) C δ R ↔
      FloorClosureContract.FamilyContainsGlobalMax F C δ R := by
  rfl

/-- Stack-orbit budgeted representative max containment is exactly the floor-closure sharp
budgeted-global-max certificate. -/
theorem representativeContainsBudgetedGlobalMax_iff_familyContainsBudgetedGlobalMax
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) :
    StackOrbitRepresentativeReduction.RepresentativeContainsBudgetedGlobalMax
        (F := F) (A := A) C δ R B ↔
      FloorClosureContract.FamilyContainsBudgetedGlobalMax F C δ R B := by
  rfl

/-- The stack-orbit sharp representative certificate feeds the floor-closure delta-star consumer
without changing the mathematical obligation. -/
theorem deltaStar_pin_of_stackOrbitRepresentativeBudgetedMax
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax :
      StackOrbitRepresentativeReduction.RepresentativeContainsBudgetedGlobalMax
        (F := F) (A := A) C δ R B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_containsBudgetedGlobalMax C εstar hδ
    ((representativeContainsBudgetedGlobalMax_iff_familyContainsBudgetedGlobalMax C δ R B).mp
      hmax)
    hbudget

/-! ## Arithmetic floor-closure consumers in stack-orbit form -/

/-- Under the Linnik least-prime input, a stack-orbit budgeted global representative is exactly the
sharp floor-closure field certificate. -/
theorem floorClosureBudgetedMaxAtField_of_linnik_stackOrbitRepresentativeBudgetedMax
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : ArkLib.ProximityGap.Frontier.FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (hLeast : ArkLib.ProximityGap.Frontier.FloorLocalization.LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax : ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.RepresentativeContainsBudgetedGlobalMax
      (F := F) (A := A) C δ R B) :
    ArkLib.ProximityGap.Frontier.FloorClosureContract.FloorClosureBudgetedMaxAtField
        (F := F) (A := A) FloorBad a C δ R B :=
  ArkLib.ProximityGap.Frontier.FloorClosureContract.floorClosureBudgetedMaxAtField_of_linnik_candidateListExactSmallestBudgetedMax
    (F := F) (A := A) FloorBad hexact hLeast a ha
    hcardPrime hcardMod hcardPrize C δ
    ((representativeContainsBudgetedGlobalMax_iff_familyContainsBudgetedGlobalMax C δ R B).mp
      hmax)

/-- Linnik floor closure, stated directly in the stack-orbit representative certificate language,
gives the prize-facing worst-case incidence bound. -/
theorem worstCaseIncidenceBounded_of_linnik_stackOrbitRepresentativeBudgetedMaxContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : ArkLib.ProximityGap.Frontier.FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (hLeast : ArkLib.ProximityGap.Frontier.FloorLocalization.LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax : ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.RepresentativeContainsBudgetedGlobalMax
      (F := F) (A := A) C δ R B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  ArkLib.ProximityGap.Frontier.FloorClosureContract.worstCaseIncidenceBounded_of_linnik_candidateListExactSmallestBudgetedMaxContract
    (F := F) (A := A) FloorBad hexact hLeast a ha
    hcardPrime hcardMod hcardPrize C δ
    ((representativeContainsBudgetedGlobalMax_iff_familyContainsBudgetedGlobalMax C δ R B).mp
      hmax)

/-- Linnik floor closure, stated directly in stack-orbit representative form, feeds the direct
delta-star lower-bound consumer. -/
theorem deltaStar_pin_of_linnik_stackOrbitRepresentativeBudgetedMaxContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : ArkLib.ProximityGap.Frontier.FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (hLeast : ArkLib.ProximityGap.Frontier.FloorLocalization.LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax : ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.RepresentativeContainsBudgetedGlobalMax
      (F := F) (A := A) C δ R B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ArkLib.ProximityGap.Frontier.FloorClosureContract.deltaStar_pin_of_linnik_candidateListExactSmallestBudgetedMaxContract
    (F := F) (A := A) FloorBad hexact hLeast a ha
    hcardPrime hcardMod hcardPrize C εstar hδ
    ((representativeContainsBudgetedGlobalMax_iff_familyContainsBudgetedGlobalMax C δ R B).mp
      hmax)
    hbudget

/-- Under TZ prime supply, a stack-orbit budgeted global representative is exactly the sharp
floor-closure field certificate. -/
theorem floorClosureBudgetedMaxAtField_of_tz_stackOrbitRepresentativeBudgetedMax
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : ArkLib.ProximityGap.Frontier.FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> ArkLib.ProximityGap.KKH26.TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax : ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.RepresentativeContainsBudgetedGlobalMax
      (F := F) (A := A) C δ R B) :
    ArkLib.ProximityGap.Frontier.FloorClosureContract.FloorClosureBudgetedMaxAtField
        (F := F) (A := A) FloorBad a C δ R B :=
  ArkLib.ProximityGap.Frontier.FloorClosureContract.floorClosureBudgetedMaxAtField_of_tz_candidateListExactSmallestBudgetedMax
    (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
    hcardPrime hcardMod hcardPrize C δ
    ((representativeContainsBudgetedGlobalMax_iff_familyContainsBudgetedGlobalMax C δ R B).mp
      hmax)

/-- TZ floor closure, stated directly in the stack-orbit representative certificate language, gives
the prize-facing worst-case incidence bound. -/
theorem worstCaseIncidenceBounded_of_tz_stackOrbitRepresentativeBudgetedMaxContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : ArkLib.ProximityGap.Frontier.FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> ArkLib.ProximityGap.KKH26.TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax : ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.RepresentativeContainsBudgetedGlobalMax
      (F := F) (A := A) C δ R B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  ArkLib.ProximityGap.Frontier.FloorClosureContract.worstCaseIncidenceBounded_of_tz_candidateListExactSmallestBudgetedMaxContract
    (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
    hcardPrime hcardMod hcardPrize C δ
    ((representativeContainsBudgetedGlobalMax_iff_familyContainsBudgetedGlobalMax C δ R B).mp
      hmax)

/-- TZ floor closure, stated directly in stack-orbit representative form, feeds the direct
delta-star lower-bound consumer. -/
theorem deltaStar_pin_of_tz_stackOrbitRepresentativeBudgetedMaxContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : ArkLib.ProximityGap.Frontier.FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> ArkLib.ProximityGap.KKH26.TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax : ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.RepresentativeContainsBudgetedGlobalMax
      (F := F) (A := A) C δ R B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ArkLib.ProximityGap.Frontier.FloorClosureContract.deltaStar_pin_of_tz_candidateListExactSmallestBudgetedMaxContract
    (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
    hcardPrime hcardMod hcardPrize C εstar hδ
    ((representativeContainsBudgetedGlobalMax_iff_familyContainsBudgetedGlobalMax C δ R B).mp
      hmax)
    hbudget

/-! ## Axiom audit -/
#print axioms stackBadCount_eq_floorClosureStackBadCount
#print axioms representativeStacksBounded_iff_familyBounded
#print axioms stackDominatingRepresentativeCover_iff_familyDominates
#print axioms representativeContainsGlobalMax_iff_familyContainsGlobalMax
#print axioms representativeContainsBudgetedGlobalMax_iff_familyContainsBudgetedGlobalMax
#print axioms deltaStar_pin_of_stackOrbitRepresentativeBudgetedMax
#print axioms floorClosureBudgetedMaxAtField_of_linnik_stackOrbitRepresentativeBudgetedMax
#print axioms worstCaseIncidenceBounded_of_linnik_stackOrbitRepresentativeBudgetedMaxContract
#print axioms deltaStar_pin_of_linnik_stackOrbitRepresentativeBudgetedMaxContract
#print axioms floorClosureBudgetedMaxAtField_of_tz_stackOrbitRepresentativeBudgetedMax
#print axioms worstCaseIncidenceBounded_of_tz_stackOrbitRepresentativeBudgetedMaxContract
#print axioms deltaStar_pin_of_tz_stackOrbitRepresentativeBudgetedMaxContract

end ArkLib.ProximityGap.Frontier.StackOrbitFloorClosureBridge
