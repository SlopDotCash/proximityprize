/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.Ring

/-! # Affine-decomposition descent (GS-kernel mathematics)

The abstract core of the "solution is linear in Z" step of the Guruswami–Sudan
list-correlated-agreement kernel (`solution_gamma_is_linear_in_Z`): a degree-`≤1`
polynomial whose coefficients descend along a ring homomorphism `φ : R →+* S`
is itself the `φ`-image of a degree-`≤1` polynomial over `R`. I.e. once the GS
power-series representative is shown polynomial of X-degree `≤ 1`, it has the
affine form `v₀ + X·v₁` with `v₀, v₁` pulled back along the coefficient embedding.
Fully general and standalone. -/

namespace GSKernel

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **Affine descent.** If `p : S[X]` has `natDegree ≤ 1` and each coefficient
lies in the range of `φ : R →+* S`, then `p = q.map φ` for some `q : R[X]` with
`natDegree ≤ 1` (concretely `q = C b + C a * X` with `φ a = p.coeff 1`,
`φ b = p.coeff 0`). -/
theorem exists_map_eq_X_add_C_of_natDegree_le_one
    (φ : R →+* S) (p : S[X]) (hp : p.natDegree ≤ 1)
    (hc : ∀ i, p.coeff i ∈ Set.range φ) :
    ∃ q : R[X], q.natDegree ≤ 1 ∧ p = q.map φ := by
  obtain ⟨a, ha⟩ := hc 1
  obtain ⟨b, hb⟩ := hc 0
  refine ⟨Polynomial.C a * Polynomial.X + Polynomial.C b, ?_, ?_⟩
  · -- natDegree (C a * X + C b) ≤ 1
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    refine max_le ?_ ?_
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simpa using Polynomial.natDegree_X_le)
    · simp [Polynomial.natDegree_C]
  · -- p = (C a * X + C b).map φ
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hp]
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        Polynomial.map_C, ha, hb]

end GSKernel
