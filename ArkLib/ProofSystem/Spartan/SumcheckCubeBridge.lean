/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.ProofSystem.Sumcheck.Domain

/-!
# Spartan ↔ sum-check cube-reindex bridge (issue #114)

The Spartan zero-check / second-sum-check algebra (e.g. `secondSumCheckVirtualPolynomial`'s
Boolean-cube sum) is naturally indexed by Boolean-bit functions `Fin k → Fin 2`, whereas
`Sumcheck.Spec.relationRound` sums over the homogeneous product Finset
`(univ.map D) ^ᶠ k = Fintype.piFinset (fun _ => univ.map D)` of *embedded* domain points.

This module provides the reindexing bridge between the two — a prerequisite for instantiating the
sum-check oracle reductions on Spartan's virtual polynomials (`firstSumcheckResidual` /
`secondSumcheckResidual`), connecting the proven cube-sum identities to the sum-check input relation.
-/

open Finset

namespace Spartan

/-- **Cube-reindex bridge (general embedding).** A sum over the `k`-fold homogeneous product Finset
`Fintype.piFinset (fun _ => univ.map e)` equals the sum over index functions `Fin k → β` of the
embedded point `e ∘ Y`. The embedding `e` need only be injective. -/
theorem sum_piFinset_const_map {α β : Type*} {M : Type*} [AddCommMonoid M] [Fintype β]
    {k : ℕ} (e : β ↪ α) (f : (Fin k → α) → M) :
    (∑ x ∈ Fintype.piFinset (fun _ : Fin k => Finset.univ.map e), f x)
      = ∑ Y : Fin k → β, f (fun i => e (Y i)) := by
  classical
  have hmap : (fun _ : Fin k => Finset.univ.map e)
      = (fun _ : Fin k => (Finset.univ : Finset β).image e) := by
    funext _; exact Finset.map_eq_image e Finset.univ
  rw [hmap, Fintype.piFinset_image, Fintype.piFinset_univ, Finset.sum_image]
  intro Y _ Y' _ h
  funext i
  exact e.injective (congrFun h i)

/-- **Cube-reindex bridge (Boolean embedding).** Specializing `sum_piFinset_const_map` to the
canonical `Sumcheck.boolEmbedding`, the sum-check Boolean domain `(univ.map (boolEmbedding R)) ^ᶠ k`
reindexes to a sum over `Fin k → Fin 2` of the coerced point `(↑Y : Fin k → R)`. This is the exact
form consumed by the Spartan cube-sum identities (`secondSumCheckVirtualPolynomial_hypercubeSum_*`,
`zeroCheckVirtualPolynomial`), letting them feed `Sumcheck.Spec.relationRound`. -/
theorem sum_boolDomain_eq_sum_boolFn {R : Type*} {M : Type*} [CommSemiring R] [Nontrivial R]
    [AddCommMonoid M] {k : ℕ} (f : (Fin k → R) → M) :
    (∑ x ∈ Fintype.piFinset (fun _ : Fin k => Finset.univ.map (boolEmbedding R)), f x)
      = ∑ Y : Fin k → Fin 2, f (fun i => ((Y i : Fin 2) : R)) := by
  rw [sum_piFinset_const_map (boolEmbedding R) f]
  refine Finset.sum_congr rfl fun Y _ => ?_
  congr 1
  funext i
  generalize Y i = b
  fin_cases b <;> simp

#print axioms sum_piFinset_const_map
#print axioms sum_boolDomain_eq_sum_boolFn

end Spartan
