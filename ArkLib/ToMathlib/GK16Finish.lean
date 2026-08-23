/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Gaussian elimination on degrees: distinct-degree recombination of an
independent polynomial family

This file proves the routine linear-algebra fact underlying the *general* hard
direction of GK16 Lemma 12 (the named residual `GK16Lemma12HardResidual`):

  **Every linearly independent finite family `P : Fin s → F[X]` admits an
  invertible `F`-linear recombination `Q j = ∑ i, c j i • P i` (`det c ≠ 0`)
  with every `Q j ≠ 0` and pairwise *distinct* `natDegree`s.**

This is Gaussian elimination on the degrees: while two members share a degree,
subtract a scalar multiple of one from the other to strictly drop one degree
(leading-coefficient cancellation). The process terminates by descent on the
sum of degrees; the elementary operations compose into an invertible matrix.

The main result is `exists_distinctDegree_recombination`.

## Key building blocks

- `recombination_comp` / `recombination_comp_det` — recombinations compose
  (matrices multiply; determinants multiply).
- `linearIndependent_recombination` — an invertible recombination of an
  independent family is independent (hence each member is nonzero).
- `exists_step_recombination` — one Gaussian step strictly drops the total
  degree when two members share a degree.
- `exists_distinctDegree_recombination` — the existence statement, by strong
  induction on the sum of degrees.
-/

open Polynomial Matrix

namespace ArkLib.FRS.GK16

variable {F : Type*} [Field F]

/-! ## Recombination infrastructure -/

/-- Composition of recombinations: if `Q j = ∑ i, c j i • P i` and
`R j = ∑ i, d j i • Q i`, then `R j = ∑ l, (∑ i, d j i * c i l) • P l`. -/
theorem recombination_comp {s : ℕ} (P Q R : Fin s → F[X])
    (c d : Fin s → Fin s → F)
    (hQ : ∀ j, Q j = ∑ i, c j i • P i)
    (hR : ∀ j, R j = ∑ i, d j i • Q i) :
    ∀ j, R j = ∑ l, (∑ i, d j i * c i l) • P l := by
  intro j
  rw [hR j]
  simp_rw [hQ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_smul]

/-- The composed recombination matrix is the matrix product, so determinants
multiply. -/
theorem recombination_comp_det {s : ℕ} (c d : Fin s → Fin s → F) :
    (Matrix.of (fun j l => ∑ i, d j i * c i l)).det
      = (Matrix.of d).det * (Matrix.of c).det := by
  have : (Matrix.of (fun j l => ∑ i, d j i * c i l))
      = (Matrix.of d) * (Matrix.of c) := by
    funext j l; simp [Matrix.mul_apply, Matrix.of_apply]
  rw [this, Matrix.det_mul]

/-- **An invertible recombination of an independent family is independent.** -/
theorem linearIndependent_recombination {s : ℕ} (P Q : Fin s → F[X])
    (c : Fin s → Fin s → F) (hc : (Matrix.of c).det ≠ 0)
    (hQ : ∀ j, Q j = ∑ i, c j i • P i)
    (hP : LinearIndependent F P) :
    LinearIndependent F Q := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a hsum j
  have hrw : ∑ l, (∑ j, a j * c j l) • P l = 0 := by
    rw [← hsum]
    simp_rw [hQ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.sum_smul]
  have hcoeff : ∀ l, ∑ j, a j * c j l = 0 :=
    (Fintype.linearIndependent_iff.mp hP) (fun l => ∑ j, a j * c j l) hrw
  have hmv : (Matrix.of c)ᵀ.mulVec a = 0 := by
    funext l
    simp only [Matrix.mulVec, Matrix.transpose_apply, Matrix.of_apply, dotProduct,
      Pi.zero_apply]
    rw [← hcoeff l]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_comm]
  have hdetT : (Matrix.of c)ᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdetT hmv) j

/-! ## The single elementary step -/

/-- **One Gaussian-elimination step.** Given an independent family `P` with two
distinct indices `j₁ ≠ j₂` of equal `natDegree`, subtracting the right scalar
multiple of `P j₁` from `P j₂` produces an invertible recombination `P'` whose
total degree `∑ (P' ·).natDegree` is strictly smaller. -/
theorem exists_step_recombination {s : ℕ} (P : Fin s → F[X])
    (hP : LinearIndependent F P)
    {j₁ j₂ : Fin s} (hne : j₁ ≠ j₂)
    (hdeg : (P j₁).natDegree = (P j₂).natDegree) :
    ∃ (P' : Fin s → F[X]) (c : Fin s → Fin s → F),
      (Matrix.of c).det ≠ 0 ∧
      (∀ j, P' j = ∑ i, c j i • P i) ∧
      (∑ j, (P' j).natDegree) < (∑ j, (P j).natDegree) := by
  classical
  have hPne : ∀ j, P j ≠ 0 := fun j => hP.ne_zero j
  have hlc1 : (P j₁).leadingCoeff ≠ 0 := by
    rw [Ne, Polynomial.leadingCoeff_eq_zero]; exact hPne j₁
  have hlc2 : (P j₂).leadingCoeff ≠ 0 := by
    rw [Ne, Polynomial.leadingCoeff_eq_zero]; exact hPne j₂
  set lam : F := (P j₂).leadingCoeff / (P j₁).leadingCoeff with hlam
  have hlam_ne : lam ≠ 0 := div_ne_zero hlc2 hlc1
  -- The transvection matrix: subtract `lam • P j₁` from row `j₂`.
  set c : Fin s → Fin s → F := fun j i =>
    if j = j₂ then (if i = j₂ then 1 else if i = j₁ then -lam else 0)
    else (if i = j then 1 else 0) with hc
  set P' : Fin s → F[X] := fun j => ∑ i, c j i • P i with hP'
  -- Recombination identity for `P'`.
  have hP'_eq : ∀ j, P' j = if j = j₂ then P j₂ - lam • P j₁ else P j := by
    intro j
    by_cases hj : j = j₂
    · rw [if_pos hj]
      show (∑ i, c j i • P i) = P j₂ - lam • P j₁
      rw [Finset.sum_eq_add_of_mem j₂ j₁ (Finset.mem_univ _) (Finset.mem_univ _)
        (Ne.symm hne) ?_]
      · have e1 : c j j₂ = 1 := by simp [hc, hj]
        have e2 : c j j₁ = -lam := by simp [hc, hj, hne]
        rw [e1, e2, one_smul, neg_smul, ← sub_eq_add_neg]
      · intro i _ hi
        have : c j i = 0 := by simp [hc, hj, hi.1, hi.2]
        rw [this, zero_smul]
    · rw [if_neg hj]
      show (∑ i, c j i • P i) = P j
      rw [Finset.sum_eq_single j]
      · have : c j j = 1 := by
          simp only [hc]; rw [if_neg hj, if_true]
        rw [this, one_smul]
      · intro i _ hi
        have : c j i = 0 := by
          simp only [hc]; rw [if_neg hj, if_neg hi]
        rw [this, zero_smul]
      · intro hcon; exact absurd (Finset.mem_univ j) hcon
  -- `c` is a transvection, so `det c = 1 ≠ 0`.
  have hc_det : (Matrix.of c).det ≠ 0 := by
    have htrans : Matrix.of c = Matrix.transvection j₂ j₁ (-lam) := by
      funext j i
      rw [Matrix.of_apply, Matrix.transvection, Matrix.add_apply,
        Matrix.one_apply, Matrix.single_apply]
      by_cases hj : j = j₂
      · -- row `j₂`: identity contributes only at `i = j₂`, single at `i = j₁`.
        by_cases hi2 : i = j₂
        · -- diagonal entry: `c = 1`; identity 1, single 0 (i = j₂ ≠ j₁).
          have hcji : c j i = 1 := by
            simp only [hc]; rw [if_pos hj, if_pos hi2]
          rw [hcji, if_pos (hj.trans hi2.symm),
            if_neg (fun h : j₂ = j ∧ j₁ = i => hne (hi2 ▸ h.2)), add_zero]
        · by_cases hi1 : i = j₁
          · -- entry `-lam`; identity 0 (j = j₂ ≠ j₁ = i), single -lam.
            have hcji : c j i = -lam := by
              simp only [hc]; rw [if_pos hj, if_neg hi2, if_pos hi1]
            rw [hcji, if_neg (fun h : j = i => hi2 (h ▸ hj)),
              if_pos ⟨hj.symm, hi1.symm⟩, zero_add]
          · -- entry 0; both contributions 0.
            have hcji : c j i = 0 := by
              simp only [hc]; rw [if_pos hj, if_neg hi2, if_neg hi1]
            rw [hcji, if_neg (fun h : j = i => hi2 (h ▸ hj)),
              if_neg (fun h : j₂ = j ∧ j₁ = i => hi1 h.2.symm), add_zero]
      · -- row `j ≠ j₂`: identity diagonal, single vanishes.
        by_cases hi : i = j
        · have hcji : c j i = 1 := by
            simp only [hc]; rw [if_neg hj, if_pos hi]
          rw [hcji, if_pos hi.symm,
            if_neg (fun h : j₂ = j ∧ j₁ = i => hj h.1.symm), add_zero]
        · have hcji : c j i = 0 := by
            simp only [hc]; rw [if_neg hj, if_neg hi]
          rw [hcji, if_neg (fun h : j = i => hi h.symm),
            if_neg (fun h : j₂ = j ∧ j₁ = i => hj h.1.symm), add_zero]
    rw [htrans, Matrix.det_transvection_of_ne j₂ j₁ (Ne.symm hne) (-lam)]
    exact one_ne_zero
  have hP'_recomb : ∀ j, P' j = ∑ i, c j i • P i := fun j => rfl
  -- `P'` is an invertible recombination, hence independent, so every `P' j ≠ 0`.
  have hP'_indep : LinearIndependent F P' :=
    linearIndependent_recombination P P' c hc_det hP'_recomb hP
  have hP'_ne : ∀ j, P' j ≠ 0 := fun j => hP'_indep.ne_zero j
  refine ⟨P', c, hc_det, hP'_recomb, ?_⟩
  -- Degree strictly drops at `j₂`, others unchanged.
  -- `degree (P' j₂) < degree (P j₂)`.
  have hsmul : lam • P j₁ = Polynomial.C lam * P j₁ := by
    rw [Polynomial.smul_eq_C_mul]
  have hdeg_smul : (lam • P j₁).degree = (P j₁).degree := by
    rw [hsmul, Polynomial.degree_C_mul (a := lam) hlam_ne]
  have hlc_smul : (lam • P j₁).leadingCoeff = (P j₂).leadingCoeff := by
    rw [hsmul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    rw [hlam, div_mul_cancel₀]
    exact hlc1
  have hdeg_eq : (P j₂).degree = (lam • P j₁).degree := by
    rw [hdeg_smul]
    rw [Polynomial.degree_eq_natDegree (hPne j₂), Polynomial.degree_eq_natDegree (hPne j₁)]
    rw [← hdeg]
  have hdrop : (P j₂ - lam • P j₁).degree < (P j₂).degree :=
    Polynomial.degree_sub_lt hdeg_eq (hPne j₂) hlc_smul.symm
  have hnatdrop : (P' j₂).natDegree < (P j₂).natDegree := by
    have hzero : P j₂ - lam • P j₁ ≠ 0 := by
      have := hP'_ne j₂; rwa [hP'_eq j₂, if_pos rfl] at this
    rw [hP'_eq j₂, if_pos rfl]
    exact Polynomial.natDegree_lt_natDegree hzero hdrop
  -- Sum drops: split off `j₂`.
  have hother : ∀ j, j ≠ j₂ → (P' j).natDegree = (P j).natDegree := by
    intro j hj; rw [hP'_eq j, if_neg hj]
  calc ∑ j, (P' j).natDegree
      = (P' j₂).natDegree + ∑ j ∈ Finset.univ.erase j₂, (P' j).natDegree := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₂)]; ring
    _ = (P' j₂).natDegree + ∑ j ∈ Finset.univ.erase j₂, (P j).natDegree := by
        congr 1
        refine Finset.sum_congr rfl (fun j hj => ?_)
        exact hother j (Finset.ne_of_mem_erase hj)
    _ < (P j₂).natDegree + ∑ j ∈ Finset.univ.erase j₂, (P j).natDegree := by
        exact Nat.add_lt_add_right hnatdrop _
    _ = ∑ j, (P j).natDegree := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₂)]; ring

/-! ## The Gaussian-elimination existence statement -/

/-- The identity recombination matrix `1` realises `P` itself as a recombination of
`P` with invertible (`det = 1`) transition. -/
private theorem id_recombination {s : ℕ} (P : Fin s → F[X]) :
    (Matrix.of (1 : Matrix (Fin s) (Fin s) F)).det ≠ 0 ∧
      (∀ j, P j = ∑ i, (1 : Matrix (Fin s) (Fin s) F) j i • P i) := by
  classical
  refine ⟨?_, fun j => ?_⟩
  · show (1 : Matrix (Fin s) (Fin s) F).det ≠ 0
    rw [Matrix.det_one]; exact one_ne_zero
  · rw [Finset.sum_eq_single j]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro i _ hi; rw [Matrix.one_apply_ne (Ne.symm hi), zero_smul]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon

/-- **Gaussian elimination on degrees (existence).** Every linearly independent
family `P : Fin s → F[X]` admits an *invertible* `F`-linear recombination
`Q j = ∑ i, c j i • P i` (`det c ≠ 0`) with every `Q j ≠ 0` and pairwise
*distinct* `natDegree`s.

Proof: strong induction on the total degree `∑ j, (P j).natDegree`. If the degrees
are already distinct we use the identity recombination. Otherwise two members share
a degree; `exists_step_recombination` produces an invertible recombination `P'` of
strictly smaller total degree (still independent by `linearIndependent_recombination`),
to which the induction hypothesis applies; the two recombinations compose
(`recombination_comp` / `recombination_comp_det`). -/
theorem exists_distinctDegree_recombination {s : ℕ} (P : Fin s → F[X])
    (hP : LinearIndependent F P) :
    ∃ (Q : Fin s → F[X]) (c : Fin s → Fin s → F),
      (Matrix.of c).det ≠ 0 ∧
      (∀ j, Q j = ∑ i, c j i • P i) ∧
      (∀ j, Q j ≠ 0) ∧
      Function.Injective (fun j => (Q j).natDegree) := by
  classical
  -- Strong induction on the total degree `n = ∑ natDegree`.
  generalize hn : (∑ j, (P j).natDegree) = n
  induction n using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    by_cases hinj : Function.Injective (fun j => (P j).natDegree)
    · -- Already distinct: the identity recombination works.
      obtain ⟨hdet, hrec⟩ := id_recombination P
      exact ⟨P, (1 : Matrix (Fin s) (Fin s) F), hdet, hrec,
        fun j => hP.ne_zero j, hinj⟩
    · -- Two members share a degree: do one Gaussian step, then recurse.
      rw [Function.not_injective_iff] at hinj
      obtain ⟨j₁, j₂, hdeg, hne⟩ := hinj
      obtain ⟨P', c, hc_det, hP'_rec, hP'_lt⟩ :=
        exists_step_recombination P hP hne hdeg
      have hP'_indep : LinearIndependent F P' :=
        linearIndependent_recombination P P' c hc_det hP'_rec hP
      -- Apply the IH to `P'` (smaller total degree).
      have hlt : (∑ j, (P' j).natDegree) < n := hn ▸ hP'_lt
      obtain ⟨Q, d, hd_det, hQ_rec, hQ_ne, hQ_inj⟩ :=
        ih (∑ j, (P' j).natDegree) hlt P' hP'_indep rfl
      -- Compose the two recombinations.
      refine ⟨Q, (fun j l => ∑ i, d j i * c i l), ?_, ?_, hQ_ne, hQ_inj⟩
      · rw [recombination_comp_det]; exact mul_ne_zero hd_det hc_det
      · exact recombination_comp P P' Q c d hP'_rec hQ_rec

end ArkLib.FRS.GK16
