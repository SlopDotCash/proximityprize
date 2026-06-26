/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Stack domination is exactly global maximization

The floor-localization route needs a theorem saying that a proposed binder/floor stack dominates all
other stacks for the actual MCA bad-scalar count.  This file records the exact meaning of that
obligation.

Because the stack space is finite, a global maximizer of `StackBadCount` always exists.  For such a
maximizer `uMax`, the open-core hypothesis

`OpenCoreConditionalPin.WorstCaseIncidenceBounded C δ B`

is equivalent to the single bound `StackBadCount C δ uMax <= B`.

The result is intentionally double-edged:

* it explains why a one-stack proof is logically possible;
* it also shows that a binder/floor stack proof must identify a true global maximizer, not merely a
  symmetric or arithmetically convenient obstruction.

The last lemmas record the falsification API: one counter-stack with a strictly larger bad-scalar
count refutes a proposed dominator, and one counter-stack above budget refutes the universal
`WorstCaseIncidenceBounded` hypothesis.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.StackMaximizerDomination

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The actual bad-scalar count appearing in `WorstCaseIncidenceBounded`. -/
noncomputable def StackBadCount (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) : ℕ := by
  classical
  exact (Finset.univ.filter (fun γ : K => mcaEvent (F := K) C δ (u 0) (u 1) γ)).card

/-- A one-stack incidence budget for the actual MCA bad-scalar count. -/
def StackBounded (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (u : WordStack A (Fin 2) ι) (B : ℕ) : Prop :=
  StackBadCount K C δ u ≤ B

/-- Failure of a one-stack budget is exactly that the stack's bad-scalar count is above budget. -/
theorem not_stackBounded_iff_budget_lt_stackBadCount
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (u : WordStack A (Fin 2) ι) (B : ℕ) :
    (¬ StackBounded F C δ u B) ↔ B < StackBadCount F C δ u := by
  constructor
  · intro hnot
    exact lt_of_not_ge hnot
  · intro hgt hbounded
    exact (not_lt_of_ge hbounded) hgt

/-- A stack dominates if it attains the global maximum of the bad-scalar count. -/
def StackDominates (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (uMax : WordStack A (Fin 2) ι) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    StackBadCount K C δ u ≤ StackBadCount K C δ uMax

/-- The finite stack space has a stack whose bad-scalar count dominates every other stack. -/
theorem exists_stackDominates (C : Set (ι -> A)) (δ : ℝ≥0) :
    ∃ uMax : WordStack A (Fin 2) ι,
      StackDominates F C δ uMax := by
  classical
  obtain ⟨uMax, hmax⟩ :=
    Finite.exists_max (fun u : WordStack A (Fin 2) ι => StackBadCount F C δ u)
  exact ⟨uMax, hmax⟩

/-- A dominating stack within budget gives the full worst-case incidence hypothesis. -/
theorem worstCaseIncidenceBounded_of_stackDominates
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {uMax : WordStack A (Fin 2) ι}
    (hmax : StackDominates F C δ uMax)
    (hbounded : StackBounded F C δ uMax B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro u
  exact le_trans (hmax u) hbounded

/-- Any full worst-case incidence bound bounds every chosen stack, in particular a maximizer. -/
theorem stackBounded_of_worstCaseIncidenceBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    (hI : ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B)
    (u : WordStack A (Fin 2) ι) :
    StackBounded F C δ u B :=
  hI u

/-- For a dominating stack, the universal open-core bound is equivalent to a one-stack bound. -/
theorem worstCaseIncidenceBounded_iff_stackBounded_of_stackDominates
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {uMax : WordStack A (Fin 2) ι}
    (hmax : StackDominates F C δ uMax) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B
      ↔ StackBounded F C δ uMax B :=
  ⟨fun hI => stackBounded_of_worstCaseIncidenceBounded C δ hI uMax,
    fun hbounded => worstCaseIncidenceBounded_of_stackDominates C δ hmax hbounded⟩

/-- There exists a stack for which the full worst-case incidence hypothesis is equivalent to
bounding that one stack.  This is nonconstructive: it chooses a true global maximizer. -/
theorem exists_stackDominates_and_worstCaseIncidenceBounded_iff_stackBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) (B : ℕ) :
    ∃ uMax : WordStack A (Fin 2) ι,
      StackDominates F C δ uMax
        ∧ (ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
              (F := F) (A := A) C δ B
            ↔ StackBounded F C δ uMax B) := by
  rcases exists_stackDominates (F := F) (A := A) C δ with ⟨uMax, hmax⟩
  exact ⟨uMax, hmax,
    worstCaseIncidenceBounded_iff_stackBounded_of_stackDominates C δ hmax⟩

/-- Delta-star consumer in maximizer form: if the chosen stack is a true maximizer and is within
budget, it feeds the existing conditional pin. -/
theorem deltaStar_pin_of_stackMaximizer
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {uMax : WordStack A (Fin 2) ι}
    (hmax : StackDominates F C δ uMax)
    (hbounded : StackBounded F C δ uMax B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_stackDominates C δ hmax hbounded)
    hbudget

/-! ## Candidate-refutation API -/

/-- If some stack has strictly larger bad-scalar count than a proposed candidate, the candidate is
not a global maximizer and therefore cannot supply a one-stack domination proof. -/
theorem not_stackDominates_of_exists_strictly_larger
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {uCand uWitness : WordStack A (Fin 2) ι}
    (hgt : StackBadCount F C δ uCand < StackBadCount F C δ uWitness) :
    ¬ StackDominates F C δ uCand := by
  intro hdom
  exact (not_lt_of_ge (hdom uWitness)) hgt

/-- A single stack whose bad-scalar count exceeds the budget refutes the full worst-case incidence
hypothesis at that budget. -/
theorem not_worstCaseIncidenceBounded_of_budget_lt_stackBadCount
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {uWitness : WordStack A (Fin 2) ι}
    (hgt : B < StackBadCount F C δ uWitness) :
    ¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro hI
  exact (not_lt_of_ge (hI uWitness)) hgt

/-- Exact negative form of the open-core incidence budget: it fails precisely when some stack is
above budget. -/
theorem not_worstCaseIncidenceBounded_iff_exists_budget_lt_stackBadCount
    (C : Set (ι -> A)) (δ : ℝ≥0) (B : ℕ) :
    (¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B)
      ↔ ∃ u : WordStack A (Fin 2) ι, B < StackBadCount F C δ u := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u
    have hle : StackBadCount F C δ u ≤ B :=
      le_of_not_gt (fun hgt => hnone ⟨u, hgt⟩)
    simpa [StackBadCount] using hle
  · rintro ⟨u, hgt⟩
    exact not_worstCaseIncidenceBounded_of_budget_lt_stackBadCount C δ hgt

/-- Bounding a convenient candidate stack is compatible with failure of the universal incidence
bound if another stack exceeds the same budget.  This is the exact formal warning against treating
candidate/binder boundedness as `WorstCaseIncidenceBounded` without a domination theorem. -/
theorem candidateBounded_and_counterStack_not_worstCaseIncidenceBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {uCand uWitness : WordStack A (Fin 2) ι}
    (hcand : StackBounded F C δ uCand B)
    (hgt : B < StackBadCount F C δ uWitness) :
    StackBounded F C δ uCand B
      ∧ ¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
          (F := F) (A := A) C δ B :=
  ⟨hcand, not_worstCaseIncidenceBounded_of_budget_lt_stackBadCount C δ hgt⟩

/-- If a candidate is beaten by another stack, then any proof using that candidate as the one-stack
consumer must be a domination proof failure, not merely an unfinished bound. -/
theorem candidateBounded_not_dominationProof_of_strictly_larger
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {uCand uWitness : WordStack A (Fin 2) ι}
    (hcand : StackBounded F C δ uCand B)
    (hgt : StackBadCount F C δ uCand < StackBadCount F C δ uWitness) :
    StackBounded F C δ uCand B ∧ ¬ StackDominates F C δ uCand :=
  ⟨hcand, not_stackDominates_of_exists_strictly_larger C δ hgt⟩

end ArkLib.ProximityGap.Frontier.StackMaximizerDomination

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.StackMaximizerDomination.not_stackBounded_iff_budget_lt_stackBadCount
#print axioms ArkLib.ProximityGap.Frontier.StackMaximizerDomination.exists_stackDominates
#print axioms ArkLib.ProximityGap.Frontier.StackMaximizerDomination.worstCaseIncidenceBounded_of_stackDominates
#print axioms ArkLib.ProximityGap.Frontier.StackMaximizerDomination.stackBounded_of_worstCaseIncidenceBounded
#print axioms ArkLib.ProximityGap.Frontier.StackMaximizerDomination.worstCaseIncidenceBounded_iff_stackBounded_of_stackDominates
#print axioms ArkLib.ProximityGap.Frontier.StackMaximizerDomination.exists_stackDominates_and_worstCaseIncidenceBounded_iff_stackBounded
#print axioms ArkLib.ProximityGap.Frontier.StackMaximizerDomination.deltaStar_pin_of_stackMaximizer
#print axioms ArkLib.ProximityGap.Frontier.StackMaximizerDomination.not_stackDominates_of_exists_strictly_larger
#print axioms ArkLib.ProximityGap.Frontier.StackMaximizerDomination.not_worstCaseIncidenceBounded_of_budget_lt_stackBadCount
#print axioms ArkLib.ProximityGap.Frontier.StackMaximizerDomination.not_worstCaseIncidenceBounded_iff_exists_budget_lt_stackBadCount
#print axioms ArkLib.ProximityGap.Frontier.StackMaximizerDomination.candidateBounded_and_counterStack_not_worstCaseIncidenceBounded
#print axioms ArkLib.ProximityGap.Frontier.StackMaximizerDomination.candidateBounded_not_dominationProof_of_strictly_larger
