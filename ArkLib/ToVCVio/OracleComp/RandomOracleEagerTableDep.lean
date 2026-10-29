/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio.OracleComp.QueryTracking.RandomOracle.DependentTable
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Compatibility names for dependent eager random-oracle tables

VCVio now proves dependent-table marginalization and lazy/eager equivalence canonically in
`EvalDist.Monad.DependentTable` and `RandomOracle.DependentTable`. This historical import path
retains the downstream theorem names and delegates to those proofs. Native measure statements
make the output measurable space explicit; no former PMF interpreter is restored.
-/

open OracleComp OracleSpec MeasureTheory

namespace OracleComp

section Marginalization

variable {ι : Type} {R : ι → Type} [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (R i)] [∀ i, Nonempty (R i)] [∀ i, SampleableType (R i)]
  [SampleableType (∀ i, R i)] [∀ i, MeasurableSpace (R i)]
  [∀ i, MeasurableSingletonClass (R i)]

/-- Replacing one cell by a fresh independent uniform sample preserves the dependent table law. -/
lemma evalDist_uniformSample_bind_update_dep (t : ι) :
    𝒟[do let u ← $ᵗ (R t); let g ← $ᵗ (∀ i, R i); pure (Function.update g t u)] =
      𝒟[$ᵗ (∀ i, R i)] := by
  simpa only [id_eq, bind_pure] using
    (evalDist_bind_bind_update_map_dependent t ($ᵗ (R t)) ($ᵗ (∀ i, R i))
      SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample id)

/-- Post-composed dependent-table marginalization, supplied by the canonical native semantics. -/
lemma evalDist_uniformSample_bind_update_map_dep {α : Type} [MeasurableSpace α]
    (t : ι) (ψ : (∀ i, R i) → α) :
    𝒟[do let u ← $ᵗ (R t); let g ← $ᵗ (∀ i, R i); pure (ψ (Function.update g t u))] =
      𝒟[do let g ← $ᵗ (∀ i, R i); pure (ψ g)] :=
  evalDist_bind_bind_update_map_dependent t ($ᵗ (R t)) ($ᵗ (∀ i, R i))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample ψ

/-- A uniform dependent table cell has the same law as an independent uniform value. -/
lemma evalDist_uniformTable_read_eq_uniform {α : Type} [MeasurableSpace α]
    (t : ι) (F : R t → α) :
    𝒟[do let g ← $ᵗ (∀ i, R i); pure (F (g t))] =
      𝒟[do let u ← $ᵗ (R t); pure (F u)] := by
  rw [← evalDist_uniformSample_bind_update_map_dep t (fun g => F (g t))]
  simp only [Function.update_self]
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
  apply Measure.bind_congr_right
  filter_upwards [] with u
  exact OracleComp.evalDist_bind_const ($ᵗ (∀ i, R i)) (pure (F u))

end Marginalization

section EagerTable

variable {ι : Type} {spec : OracleSpec ι}

/-- Historical name for canonical cache completion of a dependent answer table. -/
abbrev tableExtendingDep (c : spec.QueryCache)
    (g : (q : spec.Domain) → spec.Range q) : (q : spec.Domain) → spec.Range q :=
  completeTable c g

section
variable [DecidableEq spec.Domain]

/-- Caching one answer updates exactly that coordinate of the completed table. -/
lemma tableExtendingDep_cacheQuery (c : spec.QueryCache)
    (g : (q : spec.Domain) → spec.Range q) (t : spec.Domain) (u : spec.Range t) :
    tableExtendingDep (c.cacheQuery t u) g = Function.update (tableExtendingDep c g) t u :=
  completeTable_cacheQuery c g t u

/-- Updating an uncached coordinate commutes with canonical cache completion. -/
lemma tableExtendingDep_update_of_none (c : spec.QueryCache)
    (g : (q : spec.Domain) → spec.Range q)
    {t : spec.Domain} (hc : c t = none) (u : spec.Range t) :
    Function.update (tableExtendingDep c g) t u = tableExtendingDep c (Function.update g t u) :=
  completeTable_update_of_none c g hc u

end

/-- The empty cache leaves the supplied dependent table unchanged. -/
lemma tableExtendingDep_empty (g : (q : spec.Domain) → spec.Range q) :
    tableExtendingDep (∅ : spec.QueryCache) g = g :=
  completeTable_empty g

section
variable [DecidableEq ι] [DecidableEq spec.Domain] [Fintype spec.Domain]
  [∀ q, Fintype (spec.Range q)] [∀ q, Nonempty (spec.Range q)]
  [∀ q, SampleableType (spec.Range q)] [SampleableType ((q : spec.Domain) → spec.Range q)]

/-- Canonical lazy/eager equivalence, retaining every initially cached dependent answer. -/
theorem evalDist_simulateQ_randomOracle_run'_eq_tableExtendingDep
    {α : Type} [MeasurableSpace α] (oa : OracleComp spec α) (c : spec.QueryCache) :
    𝒟[(simulateQ randomOracle oa).run' c] =
      𝒟[do let g ← $ᵗ ((q : spec.Domain) → spec.Range q);
            pure (evalWithAnswerFn (QueryImpl.ofFn (tableExtendingDep c g)) oa)] :=
  evalDist_simulateQ_randomOracle_run'_eq_completeTable oa c

/-- Empty-cache dependent-table equivalence in the current native measure semantics. -/
theorem evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTableDep
    {α : Type} [MeasurableSpace α] (oa : OracleComp spec α) :
    𝒟[(simulateQ randomOracle oa).run' ∅] =
      𝒟[do let g ← $ᵗ ((q : spec.Domain) → spec.Range q);
            pure (evalWithAnswerFn (QueryImpl.ofFn g) oa)] := by
  rw [evalDist_simulateQ_randomOracle_run'_eq_tableExtendingDep oa ∅]
  simp_rw [tableExtendingDep_empty]

end
end EagerTable

#print axioms evalDist_uniformSample_bind_update_dep
#print axioms evalDist_uniformTable_read_eq_uniform
#print axioms evalDist_simulateQ_randomOracle_run'_eq_tableExtendingDep

end OracleComp
