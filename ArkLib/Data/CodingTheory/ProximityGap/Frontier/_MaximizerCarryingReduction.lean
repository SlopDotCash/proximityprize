/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorClosureContract

/-!
# Maximizer-carrying reductions

The floor-closure contract shows that a finite family proves the delta-star incidence bound exactly
when it contains a budgeted global maximizer for the actual MCA bad-scalar count.  A direct sparse
domination theorem can be too strong to prove head-on: it asks every stack to reduce to the finite
family.

This file isolates the weaker, prize-relevant route.  It suffices to prove that an actual global
maximizer can be moved, through count-nondecreasing improvement steps, into the finite family.  The
steps may be algebraic normalizations, profile compressions, orbit moves plus refinements, or any
other local operation; the only semantic requirement is monotonicity for `StackBadCount`.

Thus an outright attack can target the maximizer locus instead of classifying every stack.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ArkLib.ProximityGap.Frontier.FloorClosureContract

namespace ArkLib.ProximityGap.Frontier.MaximizerCarryingReduction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- A finite sequence of proposed improvement steps.  It is kept local instead of using a generic
transitive-closure API so the proof socket remains lightweight and independently checkable. -/
inductive ImprovementChain
    (Step : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop) :
    WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop
  | refl (u : WordStack A (Fin 2) ι) : ImprovementChain Step u u
  | tail {u v w : WordStack A (Fin 2) ι} :
      ImprovementChain Step u v -> Step v w -> ImprovementChain Step u w

/-- One improvement step never decreases the actual MCA bad-scalar count. -/
def StepNondecreasing (C : Set (ι -> A)) (δ : ℝ≥0)
    (Step : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop) : Prop :=
  ∀ {u v : WordStack A (Fin 2) ι}, Step u v ->
    StackBadCount F C δ u ≤ StackBadCount F C δ v

/-- Monotonicity propagates along an improvement chain. -/
theorem stackBadCount_le_of_improvementChain
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Step : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    (hmono : StepNondecreasing (F := F) C δ Step)
    {u v : WordStack A (Fin 2) ι}
    (hchain : ImprovementChain Step u v) :
    StackBadCount F C δ u ≤ StackBadCount F C δ v := by
  induction hchain with
  | refl =>
      exact le_rfl
  | tail hchain hstep ih =>
      exact le_trans ih (hmono hstep)

/-- A stack is a true global maximizer for the MCA bad-scalar count. -/
def IsStackMax (C : Set (ι -> A)) (δ : ℝ≥0)
    (uMax : WordStack A (Fin 2) ι) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    StackBadCount F C δ u ≤ StackBadCount F C δ uMax

/-- The finite stack universe always has a global maximizer. -/
theorem exists_isStackMax (C : Set (ι -> A)) (δ : ℝ≥0) :
    ∃ uMax : WordStack A (Fin 2) ι, IsStackMax (F := F) C δ uMax := by
  classical
  let U : Finset (WordStack A (Fin 2) ι) := Finset.univ
  have hU : U.Nonempty := ⟨(0 : WordStack A (Fin 2) ι), by simp [U]⟩
  obtain ⟨uMax, _huMax, hmax⟩ :=
    U.exists_max_image (fun u : WordStack A (Fin 2) ι => StackBadCount F C δ u) hU
  refine ⟨uMax, ?_⟩
  intro u
  exact hmax u (by simp [U])

/-- Every stack can be improved into the finite family.  This is the strong, all-stack version. -/
def StacksReachFamilyByImprovement
    (Step : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop)
    (R : Finset (WordStack A (Fin 2) ι)) : Prop :=
  ∀ u : WordStack A (Fin 2) ι, ∃ r ∈ R, ImprovementChain Step u r

/-- Every true maximizer can be improved into the finite family.  This is the weaker target that
still suffices for the sharp budgeted-max consumer. -/
def MaximizersReachFamilyByImprovement (C : Set (ι -> A)) (δ : ℝ≥0)
    (Step : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop)
    (R : Finset (WordStack A (Fin 2) ι)) : Prop :=
  ∀ uMax : WordStack A (Fin 2) ι, IsStackMax (F := F) C δ uMax ->
    ∃ r ∈ R, ImprovementChain Step uMax r

/-- If every stack reaches the family by nondecreasing improvements, the family dominates. -/
theorem familyDominates_of_reachesFamilyByImprovement
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Step : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmono : StepNondecreasing (F := F) C δ Step)
    (hreach : StacksReachFamilyByImprovement Step R) :
    FamilyDominates F C δ R := by
  intro u
  rcases hreach u with ⟨r, hr, hchain⟩
  exact ⟨r, hr, stackBadCount_le_of_improvementChain C δ hmono hchain⟩

/-- It is enough to move an actual global maximizer into the family by nondecreasing improvements.
The reached representative is itself a global maximizer. -/
theorem familyContainsGlobalMax_of_maximizersReachFamily
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Step : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmono : StepNondecreasing (F := F) C δ Step)
    (hreach : MaximizersReachFamilyByImprovement (F := F) C δ Step R) :
    FamilyContainsGlobalMax F C δ R := by
  rcases exists_isStackMax (F := F) C δ with ⟨uMax, huMax⟩
  rcases hreach uMax huMax with ⟨r, hr, hchain⟩
  have hur : StackBadCount F C δ uMax ≤ StackBadCount F C δ r :=
    stackBadCount_le_of_improvementChain C δ hmono hchain
  refine ⟨r, hr, ?_⟩
  intro u
  exact le_trans (huMax u) hur

/-- A bounded family reached from a true maximizer contains a budgeted global maximizer. -/
theorem familyContainsBudgetedGlobalMax_of_maximizersReachFamily
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {Step : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmono : StepNondecreasing (F := F) C δ Step)
    (hreach : MaximizersReachFamilyByImprovement (F := F) C δ Step R)
    (hbounded : FamilyBounded F C δ R B) :
    FamilyContainsBudgetedGlobalMax F C δ R B :=
  familyContainsBudgetedGlobalMax_of_familyBounded_containsGlobalMax C δ hbounded
    (familyContainsGlobalMax_of_maximizersReachFamily C δ hmono hreach)

/-- Maximizer-carrying improvement plus a representative budget proves the open-core incidence
hypothesis. -/
theorem worstCaseIncidenceBounded_of_maximizersReachFamily
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {Step : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmono : StepNondecreasing (F := F) C δ Step)
    (hreach : MaximizersReachFamilyByImprovement (F := F) C δ Step R)
    (hbounded : FamilyBounded F C δ R B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_containsBudgetedGlobalMax C δ
    (familyContainsBudgetedGlobalMax_of_maximizersReachFamily C δ hmono hreach hbounded)

/-- Delta-star consumer for the maximizer-carrying route. -/
theorem deltaStar_pin_of_maximizersReachFamily
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {Step : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmono : StepNondecreasing (F := F) C δ Step)
    (hreach : MaximizersReachFamilyByImprovement (F := F) C δ Step R)
    (hbounded : FamilyBounded F C δ R B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_containsBudgetedGlobalMax C εstar hδ
    (familyContainsBudgetedGlobalMax_of_maximizersReachFamily C δ hmono hreach hbounded)
    hbudget

#print axioms deltaStar_pin_of_maximizersReachFamily

end ArkLib.ProximityGap.Frontier.MaximizerCarryingReduction
