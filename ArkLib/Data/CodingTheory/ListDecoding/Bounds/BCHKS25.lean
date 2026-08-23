/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Team
-/

import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# List-Decoding Multiplicity Bounds from BCHKS25
This file formalizes the multiplicity assignment bounds from
Brakerski, Canetti, Holmgren, Kalai, and Stephens-Davidowitz (BCHKS25).
-/

namespace CodingTheory.Bounds.BCHKS25

open Polynomial
open scoped BigOperators

variable {F : Type} [Field F]

/-- The BCHKS25 condition on polynomial evaluation: if the sum of multiplicities of roots
exceeds the total degree of the polynomial, the polynomial must identically vanish. -/
theorem bchks25_vanishing_of_multiplicity_sum_gt_degree
    (P : Polynomial F)
    (eval_points : Finset F)
    (multiplicities : F → ℕ)
    (h_mult : ∀ x ∈ eval_points, rootMultiplicity x P ≥ multiplicities x)
    (h_sum_gt : (eval_points.sum multiplicities) > P.natDegree) :
    P = 0 := by
  classical
  by_cases hP : P = 0
  · exact hP
  · exfalso
    -- Degree of the product of the `(X - C x)^{mult x}` is the multiplicity sum.
    have h_deg_eq : (∏ x ∈ eval_points, (X - C x) ^ multiplicities x).natDegree
        = eval_points.sum multiplicities := by
      clear h_mult h_sum_gt hP
      induction eval_points using Finset.induction_on with
      | empty => simp
      | insert a s has ih =>
        rw [Finset.prod_insert has, Finset.sum_insert has, natDegree_mul]
        · rw [natDegree_pow, natDegree_X_sub_C, mul_one, ih]
        · exact ((monic_X_sub_C a).pow _).ne_zero
        · exact (monic_prod_of_monic _ _ (fun i _ => (monic_X_sub_C i).pow _)).ne_zero
    -- That product divides `P` (coprime factors, each dividing via root multiplicity).
    have h_dvd : (∏ x ∈ eval_points, (X - C x) ^ multiplicities x) ∣ P := by
      clear h_sum_gt h_deg_eq
      revert h_mult
      induction eval_points using Finset.induction_on with
      | empty => intro _; simpa using one_dvd P
      | insert a s has ih =>
        intro h_mult
        rw [Finset.prod_insert has]
        have hdvd1 : (X - C a) ^ multiplicities a ∣ P :=
          dvd_trans (pow_dvd_pow _ (h_mult a (Finset.mem_insert_self a s)))
            (pow_rootMultiplicity_dvd P a)
        have hdvd2 : (∏ x ∈ s, (X - C x) ^ multiplicities x) ∣ P :=
          ih (fun x hx => h_mult x (Finset.mem_insert_of_mem hx))
        have hcoprime : IsCoprime ((X - C a) ^ multiplicities a)
            (∏ x ∈ s, (X - C x) ^ multiplicities x) := by
          apply IsCoprime.prod_right
          intro x hx
          apply IsCoprime.pow
          have hne : a ≠ x := by rintro rfl; exact has hx
          have h_inv : C (x - a) * C (x - a)⁻¹ = 1 := by
            rw [← C_mul, mul_inv_cancel₀, C_1]
            intro h; exact hne (eq_of_sub_eq_zero h).symm
          exact ⟨C (x - a)⁻¹, -C (x - a)⁻¹, by
            calc C (x - a)⁻¹ * (X - C a) + -C (x - a)⁻¹ * (X - C x)
              _ = C (x - a)⁻¹ * (X - C a - (X - C x)) := by ring
              _ = C (x - a)⁻¹ * C (x - a) := by congr 1; simp only [map_sub]; ring
              _ = 1 := by rw [mul_comm, h_inv]⟩
        exact IsCoprime.mul_dvd hcoprime hdvd1 hdvd2
    have h_deg : (∏ x ∈ eval_points, (X - C x) ^ multiplicities x).natDegree ≤ P.natDegree :=
      natDegree_le_of_dvd h_dvd hP
    rw [h_deg_eq] at h_deg
    omega

end CodingTheory.Bounds.BCHKS25
