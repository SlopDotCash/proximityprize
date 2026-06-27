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

namespace ArkLib.ProximityGap.Frontier.StackOrbitFloorClosureBridge

namespace SO := ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction
namespace FC := ArkLib.ProximityGap.Frontier.FloorClosureContract

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The stack-orbit and floor-closure local copies of the actual MCA bad-scalar count coincide. -/
theorem stackBadCount_eq_floorClosureStackBadCount
    (C : Set (ι -> A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) :
    SO.StackBadCount F C δ u = FC.StackBadCount F C δ u := by
  rfl

/-- Representative boundedness is exactly the floor-closure family budget predicate. -/
theorem representativeStacksBounded_iff_familyBounded
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) :
    SO.RepresentativeStacksBounded (F := F) (A := A) C δ R B ↔
      FC.FamilyBounded F C δ R B := by
  rfl

/-- Direct stack-orbit domination is exactly floor-closure family domination. -/
theorem stackDominatingRepresentativeCover_iff_familyDominates
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) :
    SO.StackDominatingRepresentativeCover (F := F) (A := A) C δ R ↔
      FC.FamilyDominates F C δ R := by
  rfl

/-- Stack-orbit representative max containment is exactly floor-closure global-max containment. -/
theorem representativeContainsGlobalMax_iff_familyContainsGlobalMax
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) :
    SO.RepresentativeContainsGlobalMax (F := F) (A := A) C δ R ↔
      FC.FamilyContainsGlobalMax F C δ R := by
  rfl

/-- Stack-orbit budgeted representative max containment is exactly the floor-closure sharp
budgeted-global-max certificate. -/
theorem representativeContainsBudgetedGlobalMax_iff_familyContainsBudgetedGlobalMax
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) :
    SO.RepresentativeContainsBudgetedGlobalMax (F := F) (A := A) C δ R B ↔
      FC.FamilyContainsBudgetedGlobalMax F C δ R B := by
  rfl

/-- The stack-orbit sharp representative certificate feeds the floor-closure delta-star consumer
without changing the mathematical obligation. -/
theorem deltaStar_pin_of_stackOrbitRepresentativeBudgetedMax
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax : SO.RepresentativeContainsBudgetedGlobalMax (F := F) (A := A) C δ R B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  FC.deltaStar_pin_of_containsBudgetedGlobalMax C εstar hδ
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

end ArkLib.ProximityGap.Frontier.StackOrbitFloorClosureBridge
