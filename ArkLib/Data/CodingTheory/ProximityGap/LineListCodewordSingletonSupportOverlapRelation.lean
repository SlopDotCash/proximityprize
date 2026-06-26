/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListCodewordSingletonSupportRatio

/-!
# Coordinate-overlap relation for singleton support-ratio fibers

This file records a negative graph-route certificate: the relation that connects two scalar
witnesses when their support-ratio fibers overlap is edgeless on distinct scalars.  Therefore it
cannot improve the singleton scalar cap through the relation-independence interface; its
witness-local independence budget is exactly the original per-codeword singleton budget.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- The naive coordinate-overlap relation for a fixed codeword: two scalars are adjacent when
their support-ratio fibers share a moving coordinate. -/
noncomputable def supportRatioFiberOverlapRelation
    (c u₀ u₁ : Fin n → F) (γ γ' : F) : Prop :=
  ((supportRatioFiber c u₀ u₁ γ) ∩ (supportRatioFiber c u₀ u₁ γ')).Nonempty

/-- Distinct scalars have no support-ratio coordinate-overlap edge for one fixed codeword. -/
theorem not_supportRatioFiberOverlapRelation_of_ne
    (c u₀ u₁ : Fin n → F) {γ γ' : F} (hne : γ ≠ γ') :
    ¬ supportRatioFiberOverlapRelation c u₀ u₁ γ γ' := by
  intro h
  rcases h with ⟨i, hi⟩
  rw [Finset.mem_inter] at hi
  have hγ := (mem_supportRatioFiber c u₀ u₁ γ i).mp hi.1 |>.2
  have hγ' := (mem_supportRatioFiber c u₀ u₁ γ' i).mp hi.2 |>.2
  exact hne (hγ.symm.trans hγ')

/-- The coordinate-overlap graph is edgeless on every scalar set.  Thus it cannot provide a
nontrivial independence saving for singleton scalars. -/
theorem scalarRelationIndependent_supportRatioFiberOverlapRelation
    (c u₀ u₁ : Fin n → F) (Γ : Finset F) :
    scalarRelationIndependent (supportRatioFiberOverlapRelation c u₀ u₁) Γ := by
  intro γ _hγ γ' _hγ' hne
  exact not_supportRatioFiberOverlapRelation_of_ne c u₀ u₁ hne

variable [Fintype F]

open Classical in
/-- The forbidden-edge half holds automatically for the coordinate-overlap relation, because that
relation has no distinct-scalar edges at all. -/
theorem
    uniformLargeZeroSafeCodewordSingletonRelationForbidden_supportRatioFiberOverlap
    (dom : Fin n ↪ F) (k a : ℕ) :
    UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a
      (fun u₀ u₁ c γ γ' => supportRatioFiberOverlapRelation c u₀ u₁ γ γ') := by
  intro u₀ u₁ _hnotEligible _hsafe c _hc
  exact scalarRelationIndependent_supportRatioFiberOverlapRelation c u₀ u₁
    (codewordSingletonWitnessScalars dom k a u₀ u₁ c)

open Classical in
/-- For the coordinate-overlap relation, the witness-local independence budget is exactly the
original per-codeword singleton cap.  This formally refutes coordinate overlap as a new graph
saving: every subset is independent, so bounding independent singleton subsets is just bounding
the singleton fiber itself. -/
theorem
    uniformRelationWitnessIndependenceBudgeted_supportRatioFiberOverlap_iff_singletonBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ) :
    UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted dom k a
        (fun u₀ u₁ c γ γ' => supportRatioFiberOverlapRelation c u₀ u₁ γ γ') S ↔
      UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
  constructor
  · intro hind
    exact
      uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationWitnessIndependence
        dom k a S
        (fun u₀ u₁ c γ γ' => supportRatioFiberOverlapRelation c u₀ u₁ γ γ')
        (uniformLargeZeroSafeCodewordSingletonRelationForbidden_supportRatioFiberOverlap
          dom k a)
        hind
  · intro hsingle u₀ u₁ hnotEligible hsafe c hc Γ hsubset _hindΓ
    exact le_trans (Finset.card_le_card hsubset)
      (hsingle u₀ u₁ hnotEligible hsafe c hc)

section SourceAudit

#print axioms supportRatioFiberOverlapRelation
#print axioms not_supportRatioFiberOverlapRelation_of_ne
#print axioms scalarRelationIndependent_supportRatioFiberOverlapRelation
#print axioms
  uniformLargeZeroSafeCodewordSingletonRelationForbidden_supportRatioFiberOverlap
#print axioms
  uniformRelationWitnessIndependenceBudgeted_supportRatioFiberOverlap_iff_singletonBudgeted

end SourceAudit

end ProximityGap.Ownership
