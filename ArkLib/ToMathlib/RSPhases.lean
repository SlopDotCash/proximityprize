/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Sumcheck.Domain
import ArkLib.Data.MvPolynomial.Multilinear

/-!
# Ring-Switching Phase Bricks

This module collects auxiliary lemmas and definitions supporting the algebraic correctness
of ring-switching techniques in interactive oracle reductions (IORs), specifically for
sum-check and batching protocols (e.g., as described in [DP24] or [BGKS20]).

These lemmas isolate the multilinear extension (MLE) and Boolean domain summation machinery
from the main protocol loop, showing that summations of multilinear extensions over the
Boolean hypercube $\mathbb{F}_2^k$ (embedded into a ring $R$) coincide with pointwise sums.

## Summary of Content

* `boolDomain_cube_eq_image`: Establishes that the Boolean hypercube in the ring $R$,
  defined as the image of the canonical embedding of $\mathbb{F}_2^k$, is equivalent
  to the hypercube defined in `SumcheckDomain`.
* `sum_boolDomain_cube`: Reindexes a summation over the embedding of the Boolean hypercube
  as a direct sum over the index set `Fin k → Fin 2`.
* `MLE_eval_boolEmbedding`: Evaluates the multilinear extension of a function
  $A : \mathbb{F}_2^k \to R$ at a Boolean point, yielding the function value $A(b)$.
* `sum_cube_MLE_mul_MLE`: Proves that the summation over the Boolean cube of the product of two
  multilinear extensions equals the pointwise inner product of their coefficient vectors.
* `sum_cube_MLE_mul`: Evaluates the sum of the product of a multilinear extension and an
  arbitrary polynomial over the Boolean cube.
* `BatchingConsistencyResidual`: Defines a relational constraint representing the consistency
  requirement in sum-check batching, asserting that the verifier's claimed evaluation $s_0$ matches
  the hypercube sum of the batched relation.
-/

namespace ArkLib.RingSwitching.Phases

open MvPolynomial Finset

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- The coordinatewise Boolean-cube point `j ↦ boolEmbedding R (b j)` agrees with the canonical
`Fin 2 → R` coercion `j ↦ ((b j : Fin 2) : R)` used by `MvPolynomial.MLE_eval_zeroOne`. -/
theorem boolEmbedding_apply_eq_coe (b : Fin 2) :
    (boolEmbedding R b : R) = ((b : Fin 2) : R) := by
  fin_cases b <;> simp [boolEmbedding]

/-- The Boolean hypercube embedding `(Fin k → Fin 2) ↪ (Fin k → R)`,
`b ↦ (j ↦ boolEmbedding R (b j))`, injective by `boolEmbedding`'s injectivity. -/
def boolCubeEmb (k : ℕ) : (Fin k → Fin 2) ↪ (Fin k → R) where
  toFun b := fun j => boolEmbedding R (b j)
  inj' := by
    intro a b hab; funext j; exact (boolEmbedding R).injective (congrFun hab j)

@[simp] theorem boolCubeEmb_apply (k : ℕ) (b : Fin k → Fin 2) (j : Fin k) :
    boolCubeEmb (R := R) k b j = boolEmbedding R (b j) := rfl

/-- The Boolean cube as the image of the full `Fin k → Fin 2` finset under `boolCubeEmb`. -/
theorem boolDomain_cube_eq_image (k : ℕ) :
    (boolDomain R k).cube
      = (Finset.univ : Finset (Fin k → Fin 2)).map (boolCubeEmb (R := R) k) := by
  ext x
  simp only [SumcheckDomain.mem_cube, points_boolDomain, Finset.mem_map, Finset.mem_univ,
    true_and, boolCubeEmb, Function.Embedding.coeFn_mk]
  constructor
  · intro hx
    -- each coordinate gives `∃ c, boolEmbedding c = x j`; choose witnesses into a `Fin k → Fin 2`.
    choose c hc using hx
    exact ⟨c, funext hc⟩
  · rintro ⟨b, rfl⟩ j
    exact ⟨b j, rfl⟩

/-- Reindex a sum over the Boolean cube `(boolDomain R k).cube` as a sum over `Fin k → Fin 2`. -/
theorem sum_boolDomain_cube {M : Type*} [AddCommMonoid M] (k : ℕ) (f : (Fin k → R) → M) :
    (∑ x ∈ (boolDomain R k).cube, f x)
      = ∑ b : Fin k → Fin 2, f (fun j => boolEmbedding R (b j)) := by
  rw [boolDomain_cube_eq_image, Finset.sum_map]
  rfl

/-- Evaluating an `MLE` at a Boolean-cube point reads off the defining evaluation function. -/
theorem MLE_eval_boolEmbedding {k : ℕ} (b : Fin k → Fin 2) (evals : (Fin k → Fin 2) → R) :
    MvPolynomial.eval (fun j => boolEmbedding R (b j)) (MLE evals) = evals b := by
  have hpt : (fun j => boolEmbedding R (b j)) = ((b : Fin k → Fin 2) : Fin k → R) := by
    funext j; exact boolEmbedding_apply_eq_coe (b j)
  rw [hpt]
  exact MLE_eval_zeroOne b evals

/-- **Central batching-completeness brick.** The Boolean-cube sum of a product of
two multilinear extensions `MLE A * MLE B` equals the pointwise-product sum over the Boolean
hypercube `Fin k → Fin 2`:
  `∑_{x ∈ {0,1}^k} (MLE A · MLE B)(x) = ∑_{b} A b · B b`.

This lemma establishes that the hypercube summation of the product of two multilinear
extensions reduces to the pointwise inner product of their values. -/
theorem sum_cube_MLE_mul_MLE {k : ℕ} (A B : (Fin k → Fin 2) → R) :
    (∑ x ∈ (boolDomain R k).cube,
        MvPolynomial.eval x (MLE A * MLE B))
      = ∑ b : Fin k → Fin 2, A b * B b := by
  rw [sum_boolDomain_cube]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MvPolynomial.eval_mul, MLE_eval_boolEmbedding, MLE_eval_boolEmbedding]

/-- **Mixed batching-completeness brick.** The Boolean-cube sum of `MLE A * p` for an arbitrary
multivariate polynomial `p`. The `MLE A` factor evaluates to `A b` on the Boolean cube,
while the `p` factor is evaluated at the corresponding coordinate-wise Boolean point.
This facilitates evaluating sum-check relations where only one of the multiplied components
is written explicitly as an MLE. -/
theorem sum_cube_MLE_mul {k : ℕ} (A : (Fin k → Fin 2) → R) (p : MvPolynomial (Fin k) R) :
    (∑ x ∈ (boolDomain R k).cube, MvPolynomial.eval x (MLE A * p))
      = ∑ b : Fin k → Fin 2, A b * MvPolynomial.eval (fun j => boolEmbedding R (b j)) p := by
  rw [sum_boolDomain_cube]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MvPolynomial.eval_mul, MLE_eval_boolEmbedding]

/-! ## Named Residual for Batching-Phase Completeness

In sum-check batching protocols, the verifier validates a claimed sum $s_0$ of a batched relation.
Using the algebraic properties shown above, this check reduces to verifying a pointwise relation
between the batching coefficients and the polynomial evaluations.

The predicate `BatchingConsistencyResidual A tEvals s0` asserts that the claimed value $s_0$
is equal to the inner product of the batching coefficients $A$ and the evaluation vector `tEvals`
over the Boolean hypercube. Through `sum_cube_MLE_mul`, this relation establishes the correctness
of the sum-check consistency condition for the batched polynomial. -/
def BatchingConsistencyResidual {k : ℕ} (A : (Fin k → Fin 2) → R)
    (tEvals : (Fin k → Fin 2) → R) (s0 : R) : Prop :=
  s0 = ∑ b : Fin k → Fin 2, A b * tEvals b

/-- The normalized batching value discharges the named consistency residual by reflexivity. -/
theorem batchingConsistencyResidual_sum {k : ℕ} (A : (Fin k → Fin 2) → R)
    (tEvals : (Fin k → Fin 2) → R) :
    BatchingConsistencyResidual A tEvals (∑ b : Fin k → Fin 2, A b * tEvals b) := by
  rfl

/-- **Reduction:** Given the named residual, the sum-check consistency equation
`s0 = ∑_{x ∈ boolDomain^k} (MLE A · p).eval x` holds, where `p` is the witness polynomial whose
cube evaluations are `tEvals` (i.e. `tEvals b = eval (boolEmbedding ∘ b) p`). This shows that
satisfying the pointwise algebraic relation is sufficient to guarantee the sum-check consistency
condition for the product polynomial. -/
theorem batchingConsistency_of_residual {k : ℕ} (A : (Fin k → Fin 2) → R)
    (p : MvPolynomial (Fin k) R) (s0 : R)
    (hres : BatchingConsistencyResidual A
      (fun b => MvPolynomial.eval (fun j => boolEmbedding R (b j)) p) s0) :
    s0 = ∑ x ∈ (boolDomain R k).cube, MvPolynomial.eval x (MLE A * p) := by
  rw [sum_cube_MLE_mul]
  exact hres

end ArkLib.RingSwitching.Phases
