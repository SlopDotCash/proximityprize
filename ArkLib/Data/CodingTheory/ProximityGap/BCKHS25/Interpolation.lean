/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import CompPoly.ToMathlib.Polynomial.BivariateDegree
import ArkLib.Data.CodingTheory.PolishchukSpielman
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Guruswami
import ArkLib.ToMathlib.Polynomial.EvalExt
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Interpolation ingredients for the [BCKHS25] route

Supporting lemmas for the low-`Z`-degree Berlekamp–Welch pair
([BCKHS25] Lemma 2.1) and the improved Guruswami–Sudan interpolant (§3):
this file currently provides the vanishing upgrade — a bivariate polynomial
whose `X`-degree is below the number of its `X`-vanishing points is zero —
which converts "the kernel solution is nontrivial" into "the error-locator
component is nonzero" in both constructions.
-/

namespace BCKHS25

-- Decidability/Fintype instances are threaded through the section; several
-- statement-level lemmas do not mention them directly.
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open Polynomial Polynomial.Bivariate

open Module

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A bivariate polynomial of `X`-degree less than the number of points at
which its `X`-evaluation vanishes is zero (coefficient-wise root counting).
The `A ≠ 0` upgrade of [BCKHS25] Lemma 2.1 and the §3 interpolant both reduce
to this. -/
theorem eq_zero_of_degreeX_lt_card_of_evalX_eq_zero {f : F[X][Y]}
    {s : Finset F} (hdeg : degreeX f < s.card)
    (h : ∀ a ∈ s, evalX a f = 0) : f = 0 := by
  classical
  ext j : 1
  show f.coeff j = (0 : F[X][Y]).coeff j
  rw [Polynomial.coeff_zero]
  -- the j-th Y-coefficient vanishes at every point of s
  have hc : ∀ a ∈ s, (f.coeff j).eval a = 0 := by
    intro a ha
    have h0 := h a ha
    have hcoeff : (evalX a f).coeff j = (f.coeff j).eval a := by
      simp [evalX, Polynomial.coeff]
    rw [h0] at hcoeff
    simpa using hcoeff.symm
  by_cases hj : j ∈ f.support
  · have hdegj : (f.coeff j).natDegree < s.card :=
      lt_of_le_of_lt (Finset.le_sup (f := fun n => (f.coeff n).natDegree) hj) hdeg
    exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (f.coeff j) s hc hdegj
  · exact Polynomial.notMem_support_iff.mp hj

/-- Abstract underdetermined-system existence: a linear map between
finite-dimensional spaces with strictly larger domain has a nonzero kernel
vector. -/
theorem exists_ne_zero_map_eq_zero {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (Φ : V →ₗ[K] W) (h : finrank K W < finrank K V) :
    ∃ v : V, v ≠ 0 ∧ Φ v = 0 := by
  have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) h
  rcases Submodule.ne_bot_iff _ |>.mp hk with ⟨v, hvmem, hv0⟩
  exact ⟨v, hv0, hvmem⟩

/-- Unknown index type for the (A, B) coefficient vector: `A` has `X`-degree
`< da` and `Z`-degree `< za`; `B` has `X`-degree `< db` and `Z`-degree `< zb`. -/
abbrev BWIdx (da za db zb : ℕ) := (Fin da × Fin za) ⊕ (Fin db × Fin zb)

/-- The Berlekamp–Welch constraint matrix over the line word `u₀ + Z·u₁`: row
`(x, j)` is the `Z^j`-coefficient of `B(ω_x, Z) − (u₀ x + Z·u₁ x)·A(ω_x, Z)`. -/
def BWMatrix' (da za db zb : ℕ) (domain : ι ↪ F) (u₀ u₁ : ι → F) :
    Matrix (ι × Fin zb) (BWIdx da za db zb) F :=
  fun (xj : ι × Fin zb) idx =>
    match idx with
    | Sum.inl (i, j') =>
        -- −(u₀ x · a_{i,j} + u₁ x · a_{i,j−1}) contribution
        (if (j' : ℕ) = (xj.2 : ℕ) then -(u₀ xj.1) * (domain xj.1) ^ (i : ℕ) else 0) +
        (if (j' : ℕ) + 1 = (xj.2 : ℕ) then -(u₁ xj.1) * (domain xj.1) ^ (i : ℕ) else 0)
    | Sum.inr (i, j') =>
        if (j' : ℕ) = (xj.2 : ℕ) then (domain xj.1) ^ (i : ℕ) else 0

/-- The dimension count: with `zb = za + 1` (B one Z-degree higher) and
`da·za + db·(za+1) > n·(za+1)`, the constraint system has a nontrivial
solution. -/
theorem exists_ne_zero_BWvec (da za db zb : ℕ) (_hzb : zb = za + 1)
    (domain : ι ↪ F) (u₀ u₁ : ι → F)
    (hcount : Fintype.card ι * zb < da * za + db * zb) :
    ∃ v : BWIdx da za db zb → F, v ≠ 0 ∧
      Matrix.mulVec (BWMatrix' da za db zb domain u₀ u₁) v = 0 := by
  classical
  have hfr : finrank F ((ι × Fin zb) → F) < finrank F (BWIdx da za db zb → F) := by
    simp only [Module.finrank_pi, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
    simpa using hcount
  obtain ⟨v, hv0, hker⟩ := exists_ne_zero_map_eq_zero
    (Matrix.mulVecLin (BWMatrix' da za db zb domain u₀ u₁)) hfr
  exact ⟨v, hv0, by simpa [Matrix.mulVecLin_apply] using hker⟩

/-- Package the `A`-block of a coefficient vector as a bivariate polynomial. -/
noncomputable def toPolyA {da za db zb : ℕ} (v : BWIdx da za db zb → F) : F[X][Y] :=
  ∑ j : Fin za, Polynomial.monomial (j : ℕ)
    (∑ i : Fin da, Polynomial.C (v (Sum.inl (i, j))) * Polynomial.X ^ (i : ℕ))

/-- Package the `B`-block of a coefficient vector as a bivariate polynomial. -/
noncomputable def toPolyB {da za db zb : ℕ} (v : BWIdx da za db zb → F) : F[X][Y] :=
  ∑ j : Fin zb, Polynomial.monomial (j : ℕ)
    (∑ i : Fin db, Polynomial.C (v (Sum.inr (i, j))) * Polynomial.X ^ (i : ℕ))

/-- The `Y`-coefficients of the packaged polynomial, evaluated in `X`: inside
the index range it is the coefficient-weighted power sum; beyond it, zero. -/
lemma coeff_evalX_toPolyB {da za db zb : ℕ} (v : BWIdx da za db zb → F)
    (a : F) (j : ℕ) :
    (evalX a (toPolyB v)).coeff j
      = if h : j < zb then ∑ i : Fin db, v (Sum.inr (i, ⟨j, h⟩)) * a ^ (i : ℕ) else 0 := by
  classical
  have hcoeff : (toPolyB v).coeff j
      = if h : j < zb then
          (∑ i : Fin db, Polynomial.C (v (Sum.inr (i, ⟨j, h⟩))) * Polynomial.X ^ (i : ℕ))
        else 0 := by
    simp only [toPolyB, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    by_cases h : j < zb
    · rw [dif_pos h, Finset.sum_eq_single (⟨j, h⟩ : Fin zb)]
      · simp
      · intro b _ hb
        have hne : ((j : ℕ) : ℕ) ≠ ((b : Fin _) : ℕ) := fun heq => hb (Fin.ext heq.symm)
        simp [hne.symm]
      · intro habs
        exact absurd (Finset.mem_univ _) habs
    · rw [dif_neg h]
      refine Finset.sum_eq_zero fun b _ => ?_
      have hne : (j : ℕ) ≠ ((b : Fin _) : ℕ) := fun heq => h (heq ▸ b.isLt)
      simp [hne.symm]
  have : (evalX a (toPolyB v)).coeff j = ((toPolyB v).coeff j).eval a := by
    simp [evalX, Polynomial.coeff]
  rw [this, hcoeff]
  by_cases h : j < zb
  · rw [dif_pos h, dif_pos h]
    simp [Polynomial.eval_finset_sum]
  · rw [dif_neg h, dif_neg h]
    simp

/-- Same for the `A`-block. -/
lemma coeff_evalX_toPolyA {da za db zb : ℕ} (v : BWIdx da za db zb → F)
    (a : F) (j : ℕ) :
    (evalX a (toPolyA v)).coeff j
      = if h : j < za then ∑ i : Fin da, v (Sum.inl (i, ⟨j, h⟩)) * a ^ (i : ℕ) else 0 := by
  classical
  have hcoeff : (toPolyA v).coeff j
      = if h : j < za then
          (∑ i : Fin da, Polynomial.C (v (Sum.inl (i, ⟨j, h⟩))) * Polynomial.X ^ (i : ℕ))
        else 0 := by
    simp only [toPolyA, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    by_cases h : j < za
    · rw [dif_pos h, Finset.sum_eq_single (⟨j, h⟩ : Fin za)]
      · simp
      · intro b _ hb
        have hne : ((j : ℕ) : ℕ) ≠ ((b : Fin _) : ℕ) := fun heq => hb (Fin.ext heq.symm)
        simp [hne.symm]
      · intro habs
        exact absurd (Finset.mem_univ _) habs
    · rw [dif_neg h]
      refine Finset.sum_eq_zero fun b _ => ?_
      have hne : (j : ℕ) ≠ ((b : Fin _) : ℕ) := fun heq => h (heq ▸ b.isLt)
      simp [hne.symm]
  have : (evalX a (toPolyA v)).coeff j = ((toPolyA v).coeff j).eval a := by
    simp [evalX, Polynomial.coeff]
  rw [this, hcoeff]
  by_cases h : j < za
  · rw [dif_pos h, dif_pos h]
    simp [Polynomial.eval_finset_sum]
  · rw [dif_neg h, dif_neg h]
    simp

/-- Coefficient recovery: the packaged polynomials are injective images of the
coefficient vector. -/
lemma coeff_coeff_toPolyA {da za db zb : ℕ} (v : BWIdx da za db zb → F)
    (i : Fin da) (j : Fin za) :
    ((toPolyA v).coeff (j : ℕ)).coeff (i : ℕ) = v (Sum.inl (i, j)) := by
  classical
  -- compute the Y-coefficient, then its X-coefficient
  have hYcoeff : (toPolyA v).coeff (j : ℕ)
      = ∑ i' : Fin da, Polynomial.C (v (Sum.inl (i', j))) * Polynomial.X ^ (i' : ℕ) := by
    simp only [toPolyA, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      have hne : ((j : Fin za) : ℕ) ≠ ((b : Fin za) : ℕ) := fun heq => hb (Fin.ext heq.symm)
      simp [hne.symm]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  rw [hYcoeff, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have hne : ((i : Fin da) : ℕ) ≠ ((b : Fin da) : ℕ) := fun heq => hb (Fin.ext heq.symm)
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

lemma coeff_coeff_toPolyB {da za db zb : ℕ} (v : BWIdx da za db zb → F)
    (i : Fin db) (j : Fin zb) :
    ((toPolyB v).coeff (j : ℕ)).coeff (i : ℕ) = v (Sum.inr (i, j)) := by
  classical
  have hYcoeff : (toPolyB v).coeff (j : ℕ)
      = ∑ i' : Fin db, Polynomial.C (v (Sum.inr (i', j))) * Polynomial.X ^ (i' : ℕ) := by
    simp only [toPolyB, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      have hne : ((j : Fin zb) : ℕ) ≠ ((b : Fin zb) : ℕ) := fun heq => hb (Fin.ext heq.symm)
      simp [hne.symm]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  rw [hYcoeff, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have hne : ((i : Fin db) : ℕ) ≠ ((b : Fin db) : ℕ) := fun heq => hb (Fin.ext heq.symm)
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

/-- The kernel rows are exactly the Y-coefficients of the Berlekamp–Welch
identity: if `mulVec (BWMatrix' …) v = 0` then at every domain point
`B(ω_x, Y) = (u₀ x + u₁ x · Y) · A(ω_x, Y)`. -/
lemma identity_of_mulVec_eq_zero {da za db zb : ℕ} (hzb : zb = za + 1)
    (domain : ι ↪ F) (u₀ u₁ : ι → F) (v : BWIdx da za db zb → F)
    (hker : Matrix.mulVec (BWMatrix' da za db zb domain u₀ u₁) v = 0) (x : ι) :
    evalX (domain x) (toPolyB v)
      = (Polynomial.C (u₀ x) + Polynomial.C (u₁ x) * Polynomial.X)
          * evalX (domain x) (toPolyA v) := by
  classical
  ext j : 1
  -- RHS coefficient: u₀·a_j + u₁·a_{j−1}
  have hrhs : ((Polynomial.C (u₀ x) + Polynomial.C (u₁ x) * Polynomial.X)
      * evalX (domain x) (toPolyA v)).coeff j
      = u₀ x * (evalX (domain x) (toPolyA v)).coeff j
        + u₁ x * (if j = 0 then 0 else (evalX (domain x) (toPolyA v)).coeff (j - 1)) := by
    rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul]
    congr 1
    rw [mul_assoc, mul_comm Polynomial.X, ← mul_assoc]
    cases j with
    | zero => simp
    | succ j' =>
        rw [Polynomial.coeff_mul_X]
        simp [Polynomial.coeff_C_mul]
  -- the kernel row at (x, j) for j < zb; trivial beyond
  rw [hrhs]
  simp only [coeff_evalX_toPolyB, coeff_evalX_toPolyA]
  by_cases hj : j < zb
  · rw [dif_pos hj]
    -- expand the vanishing kernel row
    have hrow := congrFun hker (x, ⟨j, hj⟩)
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hrow
    rw [Fintype.sum_sum_type] at hrow
    -- collapse the A-block double sum
    have hAblock : (∑ p : Fin da × Fin za,
        BWMatrix' da za db zb domain u₀ u₁ (x, ⟨j, hj⟩) (Sum.inl p) * v (Sum.inl p))
        = -(u₀ x) * (if h : j < za then
              ∑ i : Fin da, v (Sum.inl (i, ⟨j, h⟩)) * (domain x) ^ (i : ℕ) else 0)
          + -(u₁ x) * (if h : j - 1 < za ∧ 1 ≤ j then
              ∑ i : Fin da, v (Sum.inl (i, ⟨j - 1, h.1⟩)) * (domain x) ^ (i : ℕ) else 0) := by
      rw [Fintype.sum_prod_type]
      simp only [BWMatrix', add_mul, Finset.sum_add_distrib]
      congr 1
      · -- the u₀-part: collapse j' = j
        by_cases h : j < za
        · rw [dif_pos h, Finset.mul_sum]
          rw [Finset.sum_comm]
          rw [Finset.sum_eq_single (⟨j, h⟩ : Fin za)]
          · refine Finset.sum_congr rfl fun i _ => ?_
            simp [mul_comm, mul_left_comm]
          · intro b _ hb
            have hne : ((b : Fin za) : ℕ) ≠ j := fun heq => hb (Fin.ext heq)
            refine Finset.sum_eq_zero fun i _ => ?_
            simp [hne]
          · intro habs
            exact absurd (Finset.mem_univ _) habs
        · rw [dif_neg h, mul_zero]
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun b _ => ?_
          have hne : ((b : Fin za) : ℕ) ≠ j := fun heq => h (heq ▸ b.isLt)
          simp [hne]
      · -- the u₁-part: collapse j' + 1 = j
        by_cases h : j - 1 < za ∧ 1 ≤ j
        · rw [dif_pos h, Finset.mul_sum]
          rw [Finset.sum_comm]
          rw [Finset.sum_eq_single (⟨j - 1, h.1⟩ : Fin za)]
          · refine Finset.sum_congr rfl fun i _ => ?_
            have hcond : (j - 1) + 1 = j := Nat.succ_pred_eq_of_pos h.2
            simp [hcond, mul_comm, mul_left_comm]
          · intro b _ hb
            have hne : ¬(((b : Fin za) : ℕ) + 1 = j) := by
              intro heq
              apply hb
              apply Fin.ext
              change ((b : Fin za) : ℕ) = j - 1
              omega
            refine Finset.sum_eq_zero fun i _ => ?_
            simp [hne]
          · intro habs
            exact absurd (Finset.mem_univ _) habs
        · rw [dif_neg h, mul_zero]
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun b _ => ?_
          have hblt : ((b : Fin za) : ℕ) < za := b.isLt
          have hne : ¬(((b : Fin za) : ℕ) + 1 = j) := by
            intro heq
            exact h ⟨by omega, by omega⟩
          simp [hne]
    -- collapse the B-block double sum
    have hBblock : (∑ p : Fin db × Fin zb,
        BWMatrix' da za db zb domain u₀ u₁ (x, ⟨j, hj⟩) (Sum.inr p) * v (Sum.inr p))
        = ∑ i : Fin db, v (Sum.inr (i, ⟨j, hj⟩)) * (domain x) ^ (i : ℕ) := by
      rw [Fintype.sum_prod_type]
      simp only [BWMatrix']
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin zb)]
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp [mul_comm]
      · intro b _ hb
        have hne : ((b : Fin zb) : ℕ) ≠ j := fun heq => hb (Fin.ext heq)
        refine Finset.sum_eq_zero fun i _ => ?_
        simp [hne]
      · intro habs
        exact absurd (Finset.mem_univ _) habs
    rw [hAblock, hBblock] at hrow
    -- rearrange: B-sum = u₀·A_j + u₁·A_{j−1}
    by_cases hza : j < za
    · by_cases hj1 : j - 1 < za ∧ 1 ≤ j
      · rw [dif_pos hza, dif_pos hj1] at hrow
        rw [dif_pos hza]
        have hj0 : ¬(j = 0) := by omega
        rw [if_neg hj0, dif_pos hj1.1]
        linear_combination hrow
      · -- j = 0 (since j < za ≤ ... and ¬(j−1<za ∧ 1≤j) with j<za means ¬1≤j)
        have hj0 : j = 0 := by omega
        rw [dif_pos hza, dif_neg hj1] at hrow
        rw [dif_pos hza, if_pos hj0]
        linear_combination hrow
    · -- j ≥ za: A_j term vanishes; j−1 may still be < za (j = za case)
      rw [dif_neg hza] at hrow
      rw [dif_neg hza]
      by_cases hj1 : j - 1 < za ∧ 1 ≤ j
      · rw [dif_pos hj1] at hrow
        have hj0 : ¬(j = 0) := by omega
        rw [if_neg hj0, dif_pos hj1.1]
        linear_combination hrow
      · rw [dif_neg hj1] at hrow
        by_cases hj0 : j = 0
        · rw [if_pos hj0]
          linear_combination hrow
        · rw [if_neg hj0]
          have : ¬(j - 1 < za) := by omega
          rw [dif_neg this]
          linear_combination hrow
  · -- j ≥ zb: everything vanishes
    rw [dif_neg hj]
    have hza : ¬(j < za) := by omega
    rw [dif_neg hza]
    have hj0 : ¬(j = 0) := by omega
    rw [if_neg hj0]
    have hj1 : ¬(j - 1 < za) := by omega
    rw [dif_neg hj1]
    ring

/-- The Y-coefficients of `toPolyA` in explicit sum form (in-range). -/
private lemma coeff_toPolyA {da za db zb : ℕ} (v : BWIdx da za db zb → F)
    {j : ℕ} (hjza : j < za) :
    (toPolyA v).coeff j
      = ∑ i : Fin da, Polynomial.C (v (Sum.inl (i, ⟨j, hjza⟩))) * Polynomial.X ^ (i : ℕ) := by
  classical
  simp only [toPolyA, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single (⟨j, hjza⟩ : Fin za)]
  · simp
  · intro b _ hb
    have hne : (((⟨j, hjza⟩ : Fin za)) : ℕ) ≠ ((b : Fin za) : ℕ) := fun heq => hb (Fin.ext heq.symm)
    simp [hne.symm]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

private lemma coeff_toPolyB {da za db zb : ℕ} (v : BWIdx da za db zb → F)
    {j : ℕ} (hjzb : j < zb) :
    (toPolyB v).coeff j
      = ∑ i : Fin db, Polynomial.C (v (Sum.inr (i, ⟨j, hjzb⟩))) * Polynomial.X ^ (i : ℕ) := by
  classical
  simp only [toPolyB, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single (⟨j, hjzb⟩ : Fin zb)]
  · simp
  · intro b _ hb
    have hne : (((⟨j, hjzb⟩ : Fin zb)) : ℕ) ≠ ((b : Fin zb) : ℕ) := fun heq => hb (Fin.ext heq.symm)
    simp [hne.symm]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

/-- Out-of-range Y-coefficients vanish. -/
private lemma coeff_toPolyA_eq_zero {da za db zb : ℕ} (v : BWIdx da za db zb → F)
    {j : ℕ} (hjza : ¬ j < za) : (toPolyA v).coeff j = 0 := by
  classical
  simp only [toPolyA, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  refine Finset.sum_eq_zero fun b _ => ?_
  have hne : (j : ℕ) ≠ ((b : Fin za) : ℕ) := fun heq => hjza (heq ▸ b.isLt)
  simp [hne.symm]

private lemma coeff_toPolyB_eq_zero {da za db zb : ℕ} (v : BWIdx da za db zb → F)
    {j : ℕ} (hjzb : ¬ j < zb) : (toPolyB v).coeff j = 0 := by
  classical
  simp only [toPolyB, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  refine Finset.sum_eq_zero fun b _ => ?_
  have hne : (j : ℕ) ≠ ((b : Fin zb) : ℕ) := fun heq => hjzb (heq ▸ b.isLt)
  simp [hne.symm]

/-- Each in-range coefficient has X-degree < da (power-sum shape). -/
private lemma natDegree_coeff_toPolyA_lt {da za db zb : ℕ} (hda : 0 < da)
    (v : BWIdx da za db zb → F) (j : ℕ) :
    ((toPolyA v).coeff j).natDegree < da := by
  classical
  by_cases hjza : j < za
  · rw [coeff_toPolyA v hjza]
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_)
      (Nat.sub_lt hda Nat.one_pos)
    refine le_trans Polynomial.natDegree_mul_le ?_
    simp only [Polynomial.natDegree_C, Polynomial.natDegree_pow, Polynomial.natDegree_X,
      mul_one, Nat.zero_add]
    omega
  · rw [coeff_toPolyA_eq_zero v hjza]
    simpa using hda

private lemma natDegree_coeff_toPolyB_lt {da za db zb : ℕ} (hdb : 0 < db)
    (v : BWIdx da za db zb → F) (j : ℕ) :
    ((toPolyB v).coeff j).natDegree < db := by
  classical
  by_cases hjzb : j < zb
  · rw [coeff_toPolyB v hjzb]
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_)
      (Nat.sub_lt hdb Nat.one_pos)
    refine le_trans Polynomial.natDegree_mul_le ?_
    simp only [Polynomial.natDegree_C, Polynomial.natDegree_pow, Polynomial.natDegree_X,
      mul_one, Nat.zero_add]
    omega
  · rw [coeff_toPolyB_eq_zero v hjzb]
    simpa using hdb

/-- X-degree bounds for the packaged polynomials. -/
lemma degreeX_toPolyA_lt {da za db zb : ℕ} (hda : 0 < da)
    (v : BWIdx da za db zb → F) : degreeX (toPolyA v) < da := by
  classical
  rw [degreeX, Finset.sup_lt_iff (by exact_mod_cast hda)]
  intro j _
  exact natDegree_coeff_toPolyA_lt hda v j

lemma degreeX_toPolyB_lt {da za db zb : ℕ} (hdb : 0 < db)
    (v : BWIdx da za db zb → F) : degreeX (toPolyB v) < db := by
  classical
  rw [degreeX, Finset.sup_lt_iff (by exact_mod_cast hdb)]
  intro j _
  exact natDegree_coeff_toPolyB_lt hdb v j

/-- Y-degree bounds. -/
lemma natDegreeY_toPolyA_lt {da za db zb : ℕ} (hza : 0 < za)
    (v : BWIdx da za db zb → F) : natDegreeY (toPolyA v) < za := by
  classical
  rw [natDegreeY, toPolyA]
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_)
    (Nat.sub_lt hza Nat.one_pos)
  refine le_trans (Polynomial.natDegree_monomial_le _) ?_
  omega

lemma natDegreeY_toPolyB_lt {da za db zb : ℕ} (hzb : 0 < zb)
    (v : BWIdx da za db zb → F) : natDegreeY (toPolyB v) < zb := by
  classical
  rw [natDegreeY, toPolyB]
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_)
    (Nat.sub_lt hzb Nat.one_pos)
  refine le_trans (Polynomial.natDegree_monomial_le _) ?_
  omega

/-- **[BCKHS25] Lemma 2.1 (assembled).** With more unknowns than constraints,
there is a Berlekamp–Welch pair `(A, B)` for the line word: `A ≠ 0`, both with
the stated degree bounds, satisfying `B(ω_x, Y) = (u₀ x + u₁ x·Y)·A(ω_x, Y)`
at every domain point. -/
theorem exists_BW_pair (da za db zb : ℕ) (hzb : zb = za + 1)
    (hda : 0 < da) (hdb : 0 < db) (hza : 0 < za)
    (domain : ι ↪ F) (u₀ u₁ : ι → F)
    (hcount : Fintype.card ι * zb < da * za + db * zb)
    (hdbn : db ≤ Fintype.card ι) :
    ∃ A B : F[X][Y], A ≠ 0 ∧
      degreeX A < da ∧ natDegreeY A < za ∧
      degreeX B < db ∧ natDegreeY B < zb ∧
      ∀ x : ι, evalX (domain x) B
        = (Polynomial.C (u₀ x) + Polynomial.C (u₁ x) * Polynomial.X)
            * evalX (domain x) A := by
  classical
  obtain ⟨v, hv0, hker⟩ := exists_ne_zero_BWvec da za db zb hzb domain u₀ u₁ hcount
  refine ⟨toPolyA v, toPolyB v, ?_, degreeX_toPolyA_lt hda v, natDegreeY_toPolyA_lt hza v,
    degreeX_toPolyB_lt hdb v, natDegreeY_toPolyB_lt (by omega) v,
    fun x => identity_of_mulVec_eq_zero hzb domain u₀ u₁ v hker x⟩
  -- A ≠ 0: otherwise B vanishes at every domain point, hence B = 0, hence v = 0
  intro hA0
  apply hv0
  -- B vanishes at all domain points
  have hBvanish : ∀ a ∈ Finset.univ.image domain, evalX a (toPolyB v) = 0 := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨x, -, rfl⟩
    rw [identity_of_mulVec_eq_zero hzb domain u₀ u₁ v hker x, hA0]
    have h0 : evalX (domain x) (0 : F[X][Y]) = 0 := by
      rw [evalX_eq_map]
      simp
    rw [h0, mul_zero]
  have hcard : degreeX (toPolyB v) < (Finset.univ.image domain).card := by
    rw [Finset.card_image_of_injective _ domain.injective, Finset.card_univ]
    exact lt_of_lt_of_le (degreeX_toPolyB_lt hdb v) hdbn
  have hB0 : toPolyB v = 0 :=
    eq_zero_of_degreeX_lt_card_of_evalX_eq_zero hcard hBvanish
  -- both blocks of v vanish
  funext idx
  match idx with
  | Sum.inl (i, j) =>
      have := coeff_coeff_toPolyA v i j
      rw [hA0] at this
      simpa using this.symm
  | Sum.inr (i, j) =>
      have := coeff_coeff_toPolyB v i j
      rw [hB0] at this
      simpa using this.symm

/-- The `Y`-evaluation of a bivariate polynomial has `X`-degree at most
`degreeX`. -/
lemma natDegree_evalY_le_degreeX (z : F) (f : F[X][Y]) :
    (evalY z f).natDegree ≤ degreeX f := by
  have heval : evalY z f = ∑ j ∈ f.support, f.coeff j * (Polynomial.C z : F[X]) ^ j := by
    simp [evalY, Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [heval]
  refine Polynomial.natDegree_sum_le_of_forall_le (s := f.support)
    (f := fun j => f.coeff j * (Polynomial.C z : F[X]) ^ j) (n := degreeX f) ?_
  intro j hj
  have hj_le : (f.coeff j).natDegree ≤ degreeX f :=
    Polynomial.Bivariate.coeff_natDegree_le_degreeX f j
  have hmul : (f.coeff j * (Polynomial.C z : F[X]) ^ j).natDegree ≤ (f.coeff j).natDegree := by
    simpa [Polynomial.C_pow] using
      (Polynomial.natDegree_mul_C_le (f := f.coeff j) (a := z ^ j))
  exact le_trans hmul hj_le

/-- Evaluation order commutes: `(evalX x f).eval z = (evalY z f).eval x`. -/
lemma evalX_eval_comm (x z : F) (f : F[X][Y]) :
    (evalX x f).eval z = (evalY z f).eval x := by
  calc (evalX x f).eval z
      = (f.map (Polynomial.evalRingHom x)).eval z := by rw [evalX_eq_map]
    _ = f.eval₂ (Polynomial.evalRingHom x) z := by
        simpa using (Polynomial.eval_map (f := Polynomial.evalRingHom x) (p := f) (x := z))
    _ = (Polynomial.eval (Polynomial.C z) f).eval x := by
        simpa [evalY] using
          (Polynomial.eval₂_at_apply (p := f) (f := Polynomial.evalRingHom x)
            (r := Polynomial.C z))

/-- The per-`z` instantiation of the Berlekamp–Welch identity: evaluating the
`Y`-identity at `Y := z` gives the pointwise equation at every domain point. -/
lemma evalY_BW_identity {A B : F[X][Y]} (domain : ι ↪ F) (u₀ u₁ : ι → F)
    (hid : ∀ x : ι, evalX (domain x) B
      = (Polynomial.C (u₀ x) + Polynomial.C (u₁ x) * Polynomial.X)
          * evalX (domain x) A)
    (z : F) (x : ι) :
    (evalY z B).eval (domain x) = (u₀ x + u₁ x * z) * (evalY z A).eval (domain x) := by
  rw [← evalX_eval_comm, ← evalX_eval_comm, hid x]
  simp [Polynomial.eval_add, Polynomial.eval_mul]

/-- Steps 1–2 of Claim 2.3: given the BW pair and a degree-`k` proximate at
`z` agreeing outside ≤ `e` points, the bivariate factors at `Y := z`:
`evalY z B = P_z · evalY z A` (by-degree equality on the agreement set). -/
lemma evalY_eq_proximate_mul {k e h : ℕ}
    (hn : k + 2 * e + h + 1 ≤ Fintype.card ι)
    {A B : F[X][Y]} (domain : ι ↪ F) (u₀ u₁ : ι → F)
    (hA : degreeX A < e + h + 1) (hB : degreeX B < k + e + h + 1)
    (hid : ∀ x : ι, evalX (domain x) B
      = (Polynomial.C (u₀ x) + Polynomial.C (u₁ x) * Polynomial.X)
          * evalX (domain x) A)
    {z : F} {p : F[X]} (hp : p.natDegree ≤ k)
    (hprox : (Finset.univ.filter
      (fun x => p.eval (domain x) ≠ u₀ x + u₁ x * z)).card ≤ e) :
    evalY z B = p * evalY z A := by
  classical
  -- the agreement set has ≥ k + e + h + 1 points
  set Agr : Finset ι := Finset.univ.filter (fun x => p.eval (domain x) = u₀ x + u₁ x * z)
    with hAgr
  have hAgr_card : k + e + h + 1 ≤ Agr.card := by
    have hsplit : Agr.card + (Finset.univ.filter
        (fun x => p.eval (domain x) ≠ u₀ x + u₁ x * z)).card = Fintype.card ι := by
      rw [hAgr, Finset.card_filter_add_card_filter_not]
      · simp
    omega
  -- both sides have degree < k + e + h + 1 and agree on the embedded agreement set
  refine Polynomial.eq_of_eval_eq_degree (n := k + e + h + 1) ?_ ?_
    (Agr.image domain) ?_ ?_
  · -- degree of evalY z B
    have hlt : (evalY z B).natDegree < k + e + h + 1 :=
      lt_of_le_of_lt (natDegree_evalY_le_degreeX z B) hB
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.mpr hlt)
  · -- degree of p * evalY z A
    have hA' := natDegree_evalY_le_degreeX z A
    have hAe : (evalY z A).natDegree ≤ e + h := le_trans hA' (by omega)
    have hmul : (p * evalY z A).natDegree < k + e + h + 1 := by
      have h1 : (p * evalY z A).natDegree ≤ p.natDegree + (evalY z A).natDegree :=
        Polynomial.natDegree_mul_le
      omega
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.mpr hmul)
  · -- enough agreement points
    rw [Finset.card_image_of_injective _ domain.injective]
    exact hAgr_card
  · -- pointwise agreement
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
    have hagree : p.eval (domain x) = u₀ x + u₁ x * z := (Finset.mem_filter.mp hx).2
    rw [evalY_BW_identity domain u₀ u₁ hid z x, Polynomial.eval_mul, hagree]

section PSApplication
-- The in-tree `polishchuk_spielman` is stated over `Type 0`; this section
-- matches it (the rest of the file is universe-polymorphic).
variable {F : Type} [Field F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

set_option maxHeartbeats 3200000 in
-- The Polishchuk–Spielman composition elaborates a large bivariate factorization term.
/-- **[BCKHS25] Claim 2.3 (joint proximate).** If every `z ∈ S` admits a
degree-`k` proximate within Hamming distance `e` of the line combination, and
`S` is large enough relative to the Polishchuk–Spielman ratio, then there is a
JOINT pair `(p₀, p₁)` of degree-`k` polynomials agreeing with `(u₀, u₁)`
outside at most `e + h` points. -/
theorem exists_joint_proximate (k e h DZ : ℕ)
    (hn : k + 2 * e + h + 1 = Fintype.card ι)
    (hDZ : e + 1 ≤ (h + 1) * DZ) (hDZ0 : 0 < DZ)
    (domain : ι ↪ F) (u₀ u₁ : ι → F) (S : Finset F) (hS0 : 0 < S.card)
    (prox : ∀ z ∈ S, ∃ p : F[X], p.natDegree ≤ k ∧
      (Finset.univ.filter (fun x => p.eval (domain x) ≠ u₀ x + u₁ x * z)).card ≤ e)
    (hratio : ((k + e + h : ℕ) : ℚ) / (Fintype.card ι : ℚ)
      + ((DZ : ℕ) : ℚ) / (S.card : ℚ) < 1) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      (Finset.univ.filter
        (fun x => ¬(p₀.eval (domain x) = u₀ x ∧ p₁.eval (domain x) = u₁ x))).card
        ≤ e + h := by
  classical
  -- 1. the BW pair from the dimension count
  have hcount : Fintype.card ι * (DZ + 1)
      < (e + h + 1) * DZ + (k + e + h + 1) * (DZ + 1) := by
    rw [← hn]
    nlinarith [hDZ, hDZ0]
  obtain ⟨A, B, hA0, hAx, hAy, hBx, hBy, hid⟩ :=
    exists_BW_pair (e + h + 1) DZ (k + e + h + 1) (DZ + 1) rfl
      (by omega) (by omega) hDZ0 domain u₀ u₁ hcount (by omega)
  -- 2. proximates
  set pz : F → F[X] := fun z => if hz : z ∈ S then (prox z hz).choose else 0 with hpz
  have hpz_deg : ∀ z ∈ S, (pz z).natDegree ≤ k := by
    intro z hz
    simp only [hpz, dif_pos hz]
    exact (prox z hz).choose_spec.1
  have hpz_prox : ∀ z ∈ S, (Finset.univ.filter
      (fun x => (pz z).eval (domain x) ≠ u₀ x + u₁ x * z)).card ≤ e := by
    intro z hz
    simp only [hpz, dif_pos hz]
    exact (prox z hz).choose_spec.2
  -- 3. Polishchuk–Spielman
  have hcard_pos : 0 < Fintype.card ι := by omega
  set Px : Finset F := Finset.univ.image domain with hPx
  have hPx_card : Px.card = Fintype.card ι := by
    rw [hPx, Finset.card_image_of_injective _ domain.injective, Finset.card_univ]
  haveI : Nonempty Px :=
    (Finset.card_pos.mp (by rw [hPx_card]; omega)).to_subtype
  haveI : Nonempty S := (Finset.card_pos.mp hS0).to_subtype
  set quotY : F → F[X] := fun a =>
    Polynomial.C (u₀ (Function.invFun domain a))
      + Polynomial.C (u₁ (Function.invFun domain a)) * Polynomial.X with hquotY
  have hsAx : e + h ≥ degreeX A := by omega
  have hsBx : k + e + h ≥ degreeX B := by omega
  have hsAy : DZ - 1 ≥ natDegreeY A := by omega
  have hsBy : DZ ≥ natDegreeY B := by omega
  have hsPx : ((⟨Fintype.card ι, hcard_pos⟩ : ℕ+) : ℕ) ≤ Px.card := by
    rw [hPx_card]
  have hsQx : ∀ z ∈ S, (pz z).natDegree ≤ (k + e + h) - (e + h) ∧
      evalY z B = (pz z) * evalY z A := by
    intro z hz
    refine ⟨by have := hpz_deg z hz; omega, ?_⟩
    exact evalY_eq_proximate_mul (by omega) domain u₀ u₁ hAx hBx hid
      (hpz_deg z hz) (hpz_prox z hz)
  have hsQy : ∀ a ∈ Px, (quotY a).natDegree ≤ DZ - (DZ - 1) ∧
      evalX a B = (quotY a) * evalX a A := by
    intro a ha
    rcases Finset.mem_image.mp (hPx ▸ ha) with ⟨x, -, rfl⟩
    have hinv : Function.invFun domain (domain x) = x :=
      Function.leftInverse_invFun domain.injective x
    constructor
    · have h1 : (quotY (domain x)).natDegree ≤ 1 := by
        simp only [hquotY, hinv]
        refine le_trans (Polynomial.natDegree_add_le _ _) ?_
        refine max_le (by simp [Polynomial.natDegree_C]) ?_
        refine le_trans (Polynomial.natDegree_mul_le) ?_
        simp [Polynomial.natDegree_C, Polynomial.natDegree_X]
      omega
    · simp only [hquotY, hinv]
      exact hid x
  have hsRatio : 1 > ((k + e + h : ℕ) : ℚ) / ((⟨Fintype.card ι, hcard_pos⟩ : ℕ+) : ℚ)
      + ((DZ : ℕ) : ℚ) / ((⟨S.card, hS0⟩ : ℕ+) : ℚ) := by
    exact_mod_cast hratio
  have hPS := polishchuk_spielman (e + h) (DZ - 1) (k + e + h) DZ
    ⟨Fintype.card ι, hcard_pos⟩ ⟨S.card, hS0⟩
    (by omega) (by omega) A B hA0 hsAx hsBx hsAy hsBy
    Px S pz quotY hsPx (le_refl _) hsQx hsQy hsRatio
  obtain ⟨P, hBPA, hPx_deg, hPy_deg, ⟨Qx, hQx_card, hQx_sub, hQx_eval⟩, -⟩ := hPS
  -- 4. extract the pair and count disagreements
  refine ⟨P.coeff 0, P.coeff 1,
    le_trans (Polynomial.Bivariate.coeff_natDegree_le_degreeX P 0) (by omega),
    le_trans (Polynomial.Bivariate.coeff_natDegree_le_degreeX P 1) (by omega), ?_⟩
  have hagree : ∀ x : ι, domain x ∈ Qx →
      (P.coeff 0).eval (domain x) = u₀ x ∧ (P.coeff 1).eval (domain x) = u₁ x := by
    intro x hx
    have heq := hQx_eval (domain x) hx
    have hinv : Function.invFun domain (domain x) = x :=
      Function.leftInverse_invFun domain.injective x
    rw [hquotY] at heq
    simp only [hinv] at heq
    have hcoeff_eval : ∀ j : ℕ, (evalX (domain x) P).coeff j = (P.coeff j).eval (domain x) := by
      intro j
      simp [evalX, Polynomial.coeff]
    constructor
    · have hc0 : (evalX (domain x) P).coeff 0
          = (Polynomial.C (u₀ x) + Polynomial.C (u₁ x) * Polynomial.X).coeff 0 := by
        rw [heq]
      rw [hcoeff_eval 0] at hc0
      simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X] using hc0
    · have hc1 : (evalX (domain x) P).coeff 1
          = (Polynomial.C (u₀ x) + Polynomial.C (u₁ x) * Polynomial.X).coeff 1 := by
        rw [heq]
      rw [hcoeff_eval 1] at hc1
      simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X] using hc1
  -- disagreement set is inside the complement of the Qx-preimage
  have hsub : (Finset.univ.filter
      (fun x => ¬((P.coeff 0).eval (domain x) = u₀ x ∧ (P.coeff 1).eval (domain x) = u₁ x)))
      ⊆ Finset.univ.filter (fun x => domain x ∉ Qx) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro hmem
    exact hx (hagree x hmem)
  refine le_trans (Finset.card_le_card hsub) ?_
  -- |{x : domain x ∉ Qx}| = n − |Qx ∩ image| = n − |Qx| ≤ e + h
  have hQx_in_im : Qx ⊆ Px := hQx_sub
  have hpre : (Finset.univ.filter (fun x => domain x ∈ Qx)).card = Qx.card := by
    rw [← Finset.card_image_of_injective
      (Finset.univ.filter (fun x => domain x ∈ Qx)) domain.injective]
    congr 1
    apply Finset.Subset.antisymm
    · intro a ha
      rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
      exact (Finset.mem_filter.mp hx).2
    · intro a ha
      have haPx : a ∈ Px := hQx_in_im ha
      rcases Finset.mem_image.mp (hPx ▸ haPx) with ⟨x, -, rfl⟩
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, ha⟩, rfl⟩
  have hsplit : (Finset.univ.filter (fun x => domain x ∈ Qx)).card
      + (Finset.univ.filter (fun x => domain x ∉ Qx)).card = Fintype.card ι := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have hQge : (Fintype.card ι : ℕ) - (e + h) ≤ Qx.card := by
    have := hQx_card
    simp only [PNat.mk_coe] at this
    omega
  omega

/-- **Forward distance bridge.** A joint agreement pair `(p₀, p₁)` whose joint
disagreement set with `(u₀, u₁)` has at most `m` points makes EVERY line
combination `u₀ + z·u₁` within Hamming distance `m` of `p₀ + z·p₁` (evaluated on
the domain). This is the direction used to turn the joint proximate of Claim 2.3
into the list-decoding-regime proximity-gap conclusion: a witness that the whole
affine line is close, uniformly in `z`.

Derivation: at any point `x` outside the joint disagreement set we have both
`p₀.eval (domain x) = u₀ x` and `p₁.eval (domain x) = u₁ x`, hence
`(p₀ + z·p₁).eval (domain x) = u₀ x + z·u₁ x` for every `z`; so the per-`z`
disagreement set is contained in the (fixed) joint disagreement set. -/
lemma hammingDist_line_le_of_jointDisagreement_le {m : ℕ}
    (domain : ι ↪ F) (u₀ u₁ : ι → F) {p₀ p₁ : F[X]}
    (hdis : (Finset.univ.filter
      (fun x => ¬(p₀.eval (domain x) = u₀ x ∧ p₁.eval (domain x) = u₁ x))).card ≤ m)
    (z : F) :
    hammingDist (fun x => u₀ x + z * u₁ x)
      (fun x => (p₀ + Polynomial.C z * p₁).eval (domain x)) ≤ m := by
  classical
  -- the per-`z` disagreement set lies inside the (fixed) joint disagreement set
  have hsub : (Finset.univ.filter (fun x =>
        (fun x => u₀ x + z * u₁ x) x ≠ (fun x => (p₀ + Polynomial.C z * p₁).eval (domain x)) x))
      ⊆ Finset.univ.filter
        (fun x => ¬(p₀.eval (domain x) = u₀ x ∧ p₁.eval (domain x) = u₁ x)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro hagree
    apply hx
    -- at an agreement point the line combinations coincide
    have h0 : p₀.eval (domain x) = u₀ x := hagree.1
    have h1 : p₁.eval (domain x) = u₁ x := hagree.2
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, h0, h1]
  calc hammingDist (fun x => u₀ x + z * u₁ x)
        (fun x => (p₀ + Polynomial.C z * p₁).eval (domain x))
      = (Finset.univ.filter (fun x =>
          (fun x => u₀ x + z * u₁ x) x
            ≠ (fun x => (p₀ + Polynomial.C z * p₁).eval (domain x)) x)).card := by
        simp [hammingDist]
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ m := hdis

/-- **[BCKHS25] Theorem 2.2 (Hensel-free list-decoding-regime proximity gap,
assembled).**

Let `(u₀, u₁)` be a line word on `domain` and let `S` be a set of `z`-values,
each admitting a degree-`k` proximate within Hamming distance `e` of the line
combination `u₀ + z·u₁` (the per-`z` list-decoding hypothesis). If `S` is large
enough that the Polishchuk–Spielman ratio closes (`hratio`) and the degree
budget holds (`hn`, `hDZ`), then there is a SINGLE pair `(p₀, p₁)` of degree-`k`
polynomials that is simultaneously a proximate for EVERY `z`: the line
`u₀ + z·u₁` is within Hamming distance `e + h` of `p₀ + z·p₁` on the domain,
uniformly in `z`. In coding-theoretic terms, the whole affine line lies within
relative distance `(e + h)/n` of the (curve over the) Reed–Solomon code.

This is the Hensel-free route's lift of the proximity gap into the
list-decoding regime: Claim 2.3 (`exists_joint_proximate`, itself built from
Lemma 2.1's Berlekamp–Welch pair via Polishchuk–Spielman) produces the joint
proximate, and the forward distance bridge converts the joint-agreement bound
into the uniform per-`z` closeness that is the proximity-gap conclusion. -/
theorem proximity_gap_listDecoding (k e h DZ : ℕ)
    (hn : k + 2 * e + h + 1 = Fintype.card ι)
    (hDZ : e + 1 ≤ (h + 1) * DZ) (hDZ0 : 0 < DZ)
    (domain : ι ↪ F) (u₀ u₁ : ι → F) (S : Finset F) (hS0 : 0 < S.card)
    (prox : ∀ z ∈ S, ∃ p : F[X], p.natDegree ≤ k ∧
      (Finset.univ.filter (fun x => p.eval (domain x) ≠ u₀ x + u₁ x * z)).card ≤ e)
    (hratio : ((k + e + h : ℕ) : ℚ) / (Fintype.card ι : ℚ)
      + ((DZ : ℕ) : ℚ) / (S.card : ℚ) < 1) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z : F, hammingDist (fun x => u₀ x + z * u₁ x)
        (fun x => (p₀ + Polynomial.C z * p₁).eval (domain x)) ≤ e + h := by
  classical
  obtain ⟨p₀, p₁, hp₀, hp₁, hdis⟩ :=
    exists_joint_proximate k e h DZ hn hDZ hDZ0 domain u₀ u₁ S hS0 prox hratio
  exact ⟨p₀, p₁, hp₀, hp₁,
    fun z => hammingDist_line_le_of_jointDisagreement_le domain u₀ u₁ hdis z⟩

end PSApplication

/-- **[BCKHS25] Lemma 3.1, integer-cap wrapper.** The improved
Guruswami-Sudan interpolation step used by the BCKHS25 route is already proved
in the BCIKS20 list-decoding development as
`ProximityGap.modified_guruswami_has_a_solution`. This wrapper exposes that
proved theorem under the BCKHS25 file, with the honest integer-side conditions
currently required by the shared GS box. The remaining paper-to-Lean work is
the real-parameter arithmetic that discharges `hDx` and `hYZ` from the
BCKHS25 constants; the interpolation object itself is no longer an open
construction. -/
theorem exists_modified_guruswami_interpolant {K : Type} [Field K] [DecidableEq K]
    [DecidableEq (RatFunc K)] {m n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    {ωs : Fin n ↪ K} {u₀ u₁ : Fin n → K}
    (hDx : ((ProximityGap.gsDpg n m k : ℕ) : ℝ) <
      ProximityGap.D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((ProximityGap.gsDpg n m k + ProximityGap.gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n))) :
    ∃ Q, ProximityGap.ModifiedGuruswami (F := K) m n k ωs Q u₀ u₁ := by
  exact ProximityGap.modified_guruswami_has_a_solution (F := K) hn hk hDx hYZ

end BCKHS25
