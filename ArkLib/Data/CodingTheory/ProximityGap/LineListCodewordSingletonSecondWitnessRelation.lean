/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListCodewordSingletonSupportRatio

/-!
# Endpoint second-witness relation for singleton scalars

This file tests the most direct graph idea for codeword-singleton scalars: connect two scalars
when one endpoint already has a distinct second codeword witness.  The relation is admissible in
the forbidden-edge interface, but exactly because singleton witnesses rule out such endpoint
second witnesses, its witness-local independence budget is equivalent to the original
per-codeword singleton cap.
-/

set_option autoImplicit false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- Endpoint relation for a fixed appearing codeword: a pair is related when at least one endpoint
has a distinct second codeword witness.  Singleton-witness scalars have no such endpoint. -/
def codewordEndpointSecondWitnessRelation
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) (γ γ' : F) : Prop :=
  (∃ c' : Fin n → F, c' ≠ c ∧
    c' ∈ badScalarWitnessCodewords dom k a u₀ u₁ γ) ∨
  (∃ c' : Fin n → F, c' ≠ c ∧
    c' ∈ badScalarWitnessCodewords dom k a u₀ u₁ γ')

/-- A singleton witness at the left endpoint rules out a distinct second witness there. -/
theorem not_exists_endpointSecondWitness_left_of_mem_codewordSingletonWitnessScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) (γ : F)
    (hγ : γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c) :
    ¬ ∃ c' : Fin n → F, c' ≠ c ∧
      c' ∈ badScalarWitnessCodewords dom k a u₀ u₁ γ := by
  rintro ⟨c', hne, hc'⟩
  have hcUnique :=
    ((mem_codewordSingletonWitnessScalars dom k a u₀ u₁ c γ).mp hγ).2
  exact hne (hcUnique.2 c' hc')

/-- Two singleton-witness scalars for the same codeword cannot be related by endpoint second
witnesses. -/
theorem not_codewordEndpointSecondWitnessRelation_of_mem_codewordSingletonWitnessScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) {γ γ' : F}
    (hγ : γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c)
    (hγ' : γ' ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c) :
    ¬ codewordEndpointSecondWitnessRelation dom k a u₀ u₁ c γ γ' := by
  intro hrel
  rcases hrel with hleft | hright
  · exact
      not_exists_endpointSecondWitness_left_of_mem_codewordSingletonWitnessScalars
        dom k a u₀ u₁ c γ hγ hleft
  · exact
      not_exists_endpointSecondWitness_left_of_mem_codewordSingletonWitnessScalars
        dom k a u₀ u₁ c γ' hγ' hright

/-- The endpoint second-witness relation satisfies the forbidden-edge half of the graph
interface.  This is immediate from the definition of a singleton witness. -/
theorem
    uniformLargeZeroSafeCodewordSingletonRelationForbidden_endpointSecondWitnessRelation
    (dom : Fin n ↪ F) (k a : ℕ) :
    UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a
      (codewordEndpointSecondWitnessRelation dom k a) := by
  intro u₀ u₁ _hnotEligible _hsafe c _hc γ hγ γ' hγ' _hne hrel
  exact
    not_codewordEndpointSecondWitnessRelation_of_mem_codewordSingletonWitnessScalars
      dom k a u₀ u₁ c hγ hγ' hrel

/-- For the endpoint second-witness relation, the witness-local graph budget is exactly the
original per-codeword singleton cap.  The relation has no edges on singleton-witness scalars, so
the graph route adds no compression by itself. -/
theorem endpointSecondWitnessRelationWitnessBudgeted_iff_codewordSingletonBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ) :
    UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted dom k a
        (codewordEndpointSecondWitnessRelation dom k a) S ↔
      UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
  constructor
  · intro hind
    exact uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationWitnessIndependence
      dom k a S (codewordEndpointSecondWitnessRelation dom k a)
      (uniformLargeZeroSafeCodewordSingletonRelationForbidden_endpointSecondWitnessRelation
        dom k a)
      hind
  · intro hbudget
    exact
      uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_codewordSingletonBudgeted
        dom k a S (codewordEndpointSecondWitnessRelation dom k a) hbudget

#print axioms codewordEndpointSecondWitnessRelation
#print axioms not_exists_endpointSecondWitness_left_of_mem_codewordSingletonWitnessScalars
#print axioms not_codewordEndpointSecondWitnessRelation_of_mem_codewordSingletonWitnessScalars
#print axioms uniformLargeZeroSafeCodewordSingletonRelationForbidden_endpointSecondWitnessRelation
#print axioms endpointSecondWitnessRelationWitnessBudgeted_iff_codewordSingletonBudgeted
#print axioms
  uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_codewordSingletonBudgeted

end ProximityGap.Ownership
