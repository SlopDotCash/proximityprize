/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Finite candidate families reduce to their own maximum

The floor/binder route may propose a finite family `R` of stack shapes rather than a single stack.
This file records the exact obligation such a family must satisfy before it can replace the
universal stack quantifier in
`OpenCoreConditionalPin.WorstCaseIncidenceBounded C δ B`.

If `R` dominates all stacks for the actual MCA bad-scalar count, then bounding every representative
in `R` is enough for the universal incidence bound.  Since `R` is finite, that is equivalent to
bounding the representative in `R` with maximal bad-scalar count.  Conversely, one outside stack
whose bad-scalar count is strictly larger than every member of `R` refutes family domination.

Thus a finite catalogue of floor/binder obstructions is only useful after proving that its internal
maximum dominates the whole stack universe.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax

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

/-- Every representative in a finite family satisfies the one-stack budget. -/
def FamilyBounded (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) : Prop :=
  ∀ r ∈ R, StackBounded K C δ r B

/-- Failure of a finite candidate-family budget is exactly an above-budget representative. -/
theorem not_familyBounded_iff_exists_member_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) :
    (¬ FamilyBounded F C δ R B) ↔
      ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧ B < StackBadCount F C δ r := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro r hr
    exact le_of_not_gt (fun hgt => hnone ⟨r, hr, hgt⟩)
  · rintro ⟨r, hr, hgt⟩ hbounded
    exact (not_lt_of_ge (hbounded r hr)) hgt

/-- A finite family dominates if every stack is bounded by some representative's bad-scalar count. -/
def FamilyDominates (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    ∃ r ∈ R, StackBadCount K C δ u ≤ StackBadCount K C δ r

/-- `rMax` is a representative in `R` with maximal bad-scalar count inside `R`. -/
def IsFamilyMax (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι))
    (rMax : WordStack A (Fin 2) ι) : Prop :=
  rMax ∈ R ∧ ∀ r ∈ R, StackBadCount K C δ r ≤ StackBadCount K C δ rMax

/-- Every nonempty finite candidate family has an internal maximum. -/
theorem exists_familyMax_of_nonempty
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hR : R.Nonempty) :
    ∃ rMax : WordStack A (Fin 2) ι, IsFamilyMax F C δ R rMax := by
  classical
  obtain ⟨rMax, hrMax, hmax⟩ :=
    R.exists_max_image (fun r : WordStack A (Fin 2) ι => StackBadCount F C δ r) hR
  exact ⟨rMax, hrMax, hmax⟩

/-- If an internal family maximum dominates all stacks, then the family dominates all stacks. -/
theorem familyDominates_of_familyMax_dominates
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {R : Finset (WordStack A (Fin 2) ι)}
    {rMax : WordStack A (Fin 2) ι}
    (hmax : IsFamilyMax F C δ R rMax)
    (hdom : ∀ u : WordStack A (Fin 2) ι,
      StackBadCount F C δ u ≤ StackBadCount F C δ rMax) :
    FamilyDominates F C δ R := by
  intro u
  exact ⟨rMax, hmax.1, hdom u⟩

/-- A dominating family makes its internal maximum dominate all stacks. -/
theorem familyMax_dominates_of_familyDominates
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {R : Finset (WordStack A (Fin 2) ι)}
    {rMax : WordStack A (Fin 2) ι}
    (hmax : IsFamilyMax F C δ R rMax)
    (hdom : FamilyDominates F C δ R) :
    ∀ u : WordStack A (Fin 2) ι,
      StackBadCount F C δ u ≤ StackBadCount F C δ rMax := by
  intro u
  rcases hdom u with ⟨r, hr, hur⟩
  exact le_trans hur (hmax.2 r hr)

/-- For a chosen internal maximum, family domination is equivalent to domination by that maximum. -/
theorem familyDominates_iff_familyMax_dominates
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {R : Finset (WordStack A (Fin 2) ι)}
    {rMax : WordStack A (Fin 2) ι}
    (hmax : IsFamilyMax F C δ R rMax) :
    FamilyDominates F C δ R
      ↔ ∀ u : WordStack A (Fin 2) ι,
        StackBadCount F C δ u ≤ StackBadCount F C δ rMax :=
  ⟨familyMax_dominates_of_familyDominates C δ hmax,
    familyDominates_of_familyMax_dominates C δ hmax⟩

/-- A stack that beats every candidate refutes finite-family domination. -/
theorem not_familyDominates_of_counterexample
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hcounter :
      ∃ u : WordStack A (Fin 2) ι,
        ∀ r ∈ R, StackBadCount F C δ r < StackBadCount F C δ u) :
    ¬ FamilyDominates F C δ R := by
  intro hdom
  rcases hcounter with ⟨u, hu⟩
  rcases hdom u with ⟨r, hr, hur⟩
  exact (not_lt_of_ge hur) (hu r hr)

/-- Explicit-witness form of `not_familyDominates_of_counterexample`. -/
theorem not_familyDominates_of_exists_strictly_larger_than_all
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {R : Finset (WordStack A (Fin 2) ι)}
    {uWitness : WordStack A (Fin 2) ι}
    (hgt : ∀ r ∈ R, StackBadCount F C δ r < StackBadCount F C δ uWitness) :
    ¬ FamilyDominates F C δ R :=
  not_familyDominates_of_counterexample C δ ⟨uWitness, hgt⟩

/-- Bounding a dominating finite family gives the full worst-case incidence hypothesis. -/
theorem worstCaseIncidenceBounded_of_familyDominates
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hdom : FamilyDominates F C δ R)
    (hR : FamilyBounded F C δ R B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro u
  rcases hdom u with ⟨r, hr, hur⟩
  exact le_trans hur (hR r hr)

/-- The universal incidence hypothesis bounds every member of any candidate family. -/
theorem familyBounded_of_worstCaseIncidenceBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hI : ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B) :
    FamilyBounded F C δ R B := by
  intro r _hr
  exact hI r

/-- For a dominating finite family, the universal incidence hypothesis is equivalent to bounding
every representative in the family. -/
theorem worstCaseIncidenceBounded_iff_familyBounded_of_familyDominates
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hdom : FamilyDominates F C δ R) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B
      ↔ FamilyBounded F C δ R B :=
  ⟨fun hI => familyBounded_of_worstCaseIncidenceBounded C δ hI,
    fun hR => worstCaseIncidenceBounded_of_familyDominates C δ hdom hR⟩

/-- Bounding a convenient finite family is compatible with failure of the universal incidence
bound if some stack exceeds the same budget. -/
theorem familyBounded_and_counterStack_not_worstCaseIncidenceBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    {uWitness : WordStack A (Fin 2) ι}
    (hR : FamilyBounded F C δ R B)
    (hgt : B < StackBadCount F C δ uWitness) :
    FamilyBounded F C δ R B
      ∧ ¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
          (F := F) (A := A) C δ B := by
  refine ⟨hR, ?_⟩
  intro hI
  exact (not_lt_of_ge (hI uWitness)) hgt

/-- If one stack beats every member of a bounded candidate family, then the family-bound proof is
not a domination proof. -/
theorem familyBounded_not_dominationProof_of_exists_strictly_larger_than_all
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    {uWitness : WordStack A (Fin 2) ι}
    (hR : FamilyBounded F C δ R B)
    (hgt : ∀ r ∈ R, StackBadCount F C δ r < StackBadCount F C δ uWitness) :
    FamilyBounded F C δ R B ∧ ¬ FamilyDominates F C δ R :=
  ⟨hR, not_familyDominates_of_exists_strictly_larger_than_all C δ hgt⟩

/-- Bounding every representative is equivalent to bounding the internal maximum. -/
theorem familyBounded_iff_familyMaxBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    {rMax : WordStack A (Fin 2) ι}
    (hmax : IsFamilyMax F C δ R rMax) :
    FamilyBounded F C δ R B ↔ StackBounded F C δ rMax B :=
  ⟨fun hR => hR rMax hmax.1,
    fun hbounded r hr => le_trans (hmax.2 r hr) hbounded⟩

/-- Under family domination, the full worst-case incidence hypothesis is equivalent to bounding the
family's internal maximum. -/
theorem worstCaseIncidenceBounded_iff_familyMaxBounded_of_familyDominates
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    {rMax : WordStack A (Fin 2) ι}
    (hfamilyMax : IsFamilyMax F C δ R rMax)
    (hdom : FamilyDominates F C δ R) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B
      ↔ StackBounded F C δ rMax B :=
  ⟨fun hI => hI rMax,
    fun hbounded =>
      worstCaseIncidenceBounded_of_familyDominates C δ hdom
        ((familyBounded_iff_familyMaxBounded C δ hfamilyMax).mpr hbounded)⟩

/-- A nonempty dominating finite family has one representative whose one-stack budget is equivalent
to the full universal incidence budget. -/
theorem exists_familyMax_and_worstCaseIncidenceBounded_iff_stackBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) (B : ℕ)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hR : R.Nonempty)
    (hdom : FamilyDominates F C δ R) :
    ∃ rMax : WordStack A (Fin 2) ι,
      IsFamilyMax F C δ R rMax
        ∧ (ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
              (F := F) (A := A) C δ B
            ↔ StackBounded F C δ rMax B) := by
  rcases exists_familyMax_of_nonempty (F := F) (A := A) C δ hR with ⟨rMax, hmax⟩
  exact ⟨rMax, hmax,
    worstCaseIncidenceBounded_iff_familyMaxBounded_of_familyDominates C δ hmax hdom⟩

/-- Delta-star consumer in finite-family form: a dominating family plus a budget on every
representative feeds the existing open-core conditional pin. -/
theorem deltaStar_pin_of_familyDominates
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hdom : FamilyDominates F C δ R)
    (hbounded : FamilyBounded F C δ R B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_familyDominates C δ hdom hbounded)
    hbudget

end ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.not_familyBounded_iff_exists_member_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.exists_familyMax_of_nonempty
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.familyDominates_of_familyMax_dominates
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.familyMax_dominates_of_familyDominates
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.familyDominates_iff_familyMax_dominates
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.not_familyDominates_of_counterexample
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.not_familyDominates_of_exists_strictly_larger_than_all
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.worstCaseIncidenceBounded_of_familyDominates
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.familyBounded_of_worstCaseIncidenceBounded
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.worstCaseIncidenceBounded_iff_familyBounded_of_familyDominates
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.familyBounded_and_counterStack_not_worstCaseIncidenceBounded
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.familyBounded_not_dominationProof_of_exists_strictly_larger_than_all
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.familyBounded_iff_familyMaxBounded
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.worstCaseIncidenceBounded_iff_familyMaxBounded_of_familyDominates
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.exists_familyMax_and_worstCaseIncidenceBounded_iff_stackBounded
#print axioms ArkLib.ProximityGap.Frontier.StackCandidateFamilyMax.deltaStar_pin_of_familyDominates
