/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.CharP.Basic

import CompPoly.Data.MvPolynomial.Notation
import ArkLib.Data.MvPolynomial.Interpolation

/-!
  # Multilinear Polynomials

  This is the special case of polynomial interpolation, when we consider multilinear polynomials and
  evaluation on the hypercube `σ → Fin 2`.
-/

noncomputable section

namespace MvPolynomial

open BigOperators Fintype Finset

universe u

variable {σ : Type*} {R : Type*}

instance coeFunctionFin2 [NatCast R] : Coe (σ → Fin 2) (σ → R) where
  coe := fun vec i => vec i

variable [CommRing R]

def toEvalsZeroOne (p : MvPolynomial σ R) : (σ → Fin 2) → R :=
  fun x => eval (x : σ → R) p

abbrev singleEqPolynomial (r : R) (x : MvPolynomial σ R) : MvPolynomial σ R :=
  (1 - C r) * (1 - x) + C r * x

theorem singleEqPolynomial_nf (r : R) (x : MvPolynomial σ R) :
    singleEqPolynomial r x = (2 * C r - 1) * x + (1 - C r) := by
  ring_nf

theorem singleEqPolynomial_symm (r : R) (s : R) :
    (singleEqPolynomial r (C s) : MvPolynomial σ R) = singleEqPolynomial s (C r) := by ring_nf

@[simp]
theorem singleEqPolynomial_zero (x : MvPolynomial σ R) : singleEqPolynomial (0 : R) x = 1 - x := by
  unfold singleEqPolynomial; simp

@[simp]
theorem singleEqPolynomial_one (x : MvPolynomial σ R) : singleEqPolynomial (1 : R) x = x := by
  unfold singleEqPolynomial; simp

-- @[simp]
theorem singleEqPolynomial_zeroOne (r : Fin 2) (x : MvPolynomial σ R) :
    singleEqPolynomial (r : R) x = if r = 0 then 1 - x else x := by
  fin_cases r <;> simp

-- @[simp]
theorem singleEqPolynomial_zeroOne_C (r : Fin 2) (x : Fin 2) :
    (singleEqPolynomial (r : R) (C x) : MvPolynomial σ R) = if x = r then 1 else 0 := by
  fin_cases r <;> fin_cases x <;> simp

-- @[simp]
-- theorem singleEqPolynomial_eval_zeroOne (x : Fin n → Fin 2) (r : Fin n → Fin 2) (i : Fin n) :
--     (eval fun i => ↑↑(x i))
--     (match r i with
--     | 0 => 1 - X i
--     | 1 => X i) = 1 := by

variable [Fintype σ]

abbrev eqPolynomial' : R[X (σ ⊕ σ)] :=
  ∏ i : σ, ((1 - X (.inl i)) * (1 - X (.inr i)) + (X (.inl i)) * X (.inr i))

-- Should be in `R[X σ ⊕ σ]`
abbrev eqPolynomial (r : σ → R) : R[X σ] :=
  ∏ i : σ, singleEqPolynomial (r i) (X i)

/-- The equality polynomial value `eq̃(r, r') := eval r' (eqPolynomial r)` — the multilinear
extension of the equality indicator on `{0,1}^σ`. Equals `1` iff `r = r'` on the Boolean cube.
This is the canonical `eq̃` used in multilinear-extension-based sumcheck protocols (Binius
ring-switching, Hachi range checks, …). -/
noncomputable def eqTilde (r r' : σ → R) : R := eval r' (eqPolynomial r)

theorem eqPolynomial_expanded (r : σ → R) :
    eqPolynomial r = ∏ i : σ, ((1 - C (r i)) * (1 - X i) + C (r i) * X i) := rfl

theorem eqPolynomial_symm (x : σ → R) (y : σ → R) :
    MvPolynomial.eval y (eqPolynomial x) = MvPolynomial.eval x (eqPolynomial y) := by
  simp only [map_prod, map_add, map_mul, map_sub, map_one, eval_C, eval_X]
  congr
  funext
  ring_nf

/-- **Product factorization of the equality kernel.**  The multilinear equality kernel
`eqTilde r r' = eval r' (eqPolynomial r)` factors coordinate-wise as
`∏ᵢ ((1 - rᵢ)(1 - r'ᵢ) + rᵢ · r'ᵢ)`.  This is the closed form used throughout sum-check soundness
analysis. -/
theorem eqTilde_eq_prod (r r' : σ → R) :
    eqTilde r r' = ∏ i : σ, ((1 - r i) * (1 - r' i) + r i * r' i) := by
  unfold eqTilde
  rw [eqPolynomial_expanded, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [map_add, map_mul, map_sub, map_one, eval_C, eval_X]

/-- **The equality kernel is symmetric.**  `eqTilde r r' = eqTilde r' r` — immediate from
`eqPolynomial_symm`, recorded directly on `eqTilde`. -/
theorem eqTilde_symm (r r' : σ → R) : eqTilde r r' = eqTilde r' r :=
  eqPolynomial_symm r r'

-- @[simp]
theorem eqPolynomial_zeroOne (r : σ → Fin 2) : (eqPolynomial r : MvPolynomial σ R) =
    ∏ i : σ, if r i = 0 then 1 - X i else X i := by
  unfold eqPolynomial; congr; funext i; simp [singleEqPolynomial_zeroOne]

@[simp]
theorem eqPolynomial_eval_zeroOne (r x : σ → Fin 2) :
    eval (x : σ → R) (eqPolynomial r) = if x = r then 1 else 0 := by
  unfold eqPolynomial
  simp only [map_prod, map_add, map_natCast, map_mul, map_sub, map_one, eval_X]
  by_cases h : x = r
  · subst h
    have (i : Fin 2) : (1 - (i : R)) * (1 - (i : R)) + i * i = 1 := by
      fin_cases i <;> ring_nf <;> simp
    simp [this]
  · rw [if_neg h]
    have : ∃ i : σ, x i ≠ r i := Function.ne_iff.mp h
    obtain ⟨i, hi⟩ := this
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    by_cases h' : r i = 0
    · simp_all [Fin.eq_one_of_ne_zero]
    · have : x i = 0 := by fin_omega
      simp_all [Fin.eq_one_of_ne_zero]

variable [DecidableEq σ]

/-- Multilinear extension of evaluations on the `σ`-indexed hypercube, where the evaluations are
  represented as `(σ → Fin 2) → R` -/
def MLE (evals : (σ → Fin 2) → R) : MvPolynomial σ R :=
    ∑ x : σ → Fin 2, (eqPolynomial (x : σ → R)) * C (evals x)

/-- Multilinear extension of evaluations on the `n`-dimensional hypercube, where the evaluations are
  represented as `Fin (2 ^ n) → R` -/
def MLE' {n : ℕ} (evals : Fin (2 ^ n) → R) : MvPolynomial (Fin n) R :=
  MLE (evals ∘ finFunctionFinEquiv)

theorem MLE_expanded (evals : (σ → Fin 2) → R) : MLE evals =
    ∑ x : σ → Fin 2, (∏ i : σ, ((1 - C (x i : R)) * (1 - X i) + C (x i : R) * X i))
      * C (evals x) := by
  unfold MLE; congr

@[simp]
theorem MLE_eval_zeroOne (x : σ → Fin 2) (evals : (σ → Fin 2) → R) :
    MvPolynomial.eval (x : σ → R) (MLE evals) = evals x := by
  simp only [MLE, eval_sum, eval_mul, eqPolynomial_eval_zeroOne]
  simp

@[simp]
theorem MLE'_eval_zeroOne {n : ℕ} (x : Fin n → Fin 2) (evals : Fin (2 ^ n) → R) :
    MvPolynomial.eval (x : Fin n → R) (MLE' evals) = evals (finFunctionFinEquiv x) := by
  simp [MLE', MLE_eval_zeroOne]

theorem eval_zeroOne_eq_MLE_toEvalsZeroOne (p : MvPolynomial σ R) (x : σ → Fin 2) :
    eval (x : σ → R) p = eval (x : σ → R) (MLE p.toEvalsZeroOne) := by
  simp only [MLE_eval_zeroOne, toEvalsZeroOne]

section DegreeOf

omit [Fintype σ] in
theorem singleEqPolynomial_degreeOf (r : R) (i j : σ) :
    degreeOf i (singleEqPolynomial r (X j)) ≤ if i = j then 1 else 0 := by
  rw [singleEqPolynomial_nf]
  calc
    _ ≤ max (degreeOf i ((2 * C r - 1) * X j)) (degreeOf i (1 - C r)) := by
      exact degreeOf_add_le i _ _
    _ ≤ max (degreeOf i (2 * C r - 1) + degreeOf i (X j))
            (degreeOf i (1 - C r)) := by
      gcongr
      repeat exact degreeOf_mul_le i _ _
    _ = max (degreeOf i (C (2 * r - 1)) + degreeOf i (X j))
            (degreeOf i (C (1 - r))) := by
      congr
      · simp only [map_sub, map_mul, map_one, sub_left_inj]; congr
      · simp only [map_sub, map_one]
    _ = max (0 + degreeOf i (X j)) 0 := by
      congr <;>
      exact degreeOf_C (R := R) _ i
    _ ≤ max (0 + (if i = j then 1 else 0)) 0 := by
      gcongr
      by_cases h : i = j
      · simpa only [h] using degreeOf_X_le (R := R) j i
      · simpa only [h] using le_of_eq (degreeOf_X_of_ne (R := R) (i := i) (j := j) h)
    _ = if i = j then 1 else 0 := by norm_num

omit [DecidableEq σ] in
theorem eqPolynomial_mem_restrictDegree (r : σ → R) : (eqPolynomial r) ∈ R⦃≤ 1⦄[X σ] := by
  classical
  rw [mem_restrictDegree_iff_degreeOf_le]
  intro i
  calc
    _ ≤ ∑ j : σ, degreeOf i (singleEqPolynomial (r j) (X j)) := by
      exact degreeOf_prod_le i _ _
    _ ≤ ∑ j : σ, if i = j then 1 else 0 := by
      gcongr
      exact singleEqPolynomial_degreeOf _ _ _
    _ = 1 := by norm_num

omit [DecidableEq σ] in
theorem eqPolynomial_degreeOf (r : σ → R) (i : σ) : degreeOf i (eqPolynomial r) ≤ 1 := by
  apply (mem_restrictDegree_iff_degreeOf_le _ _).mp
  exact eqPolynomial_mem_restrictDegree r

theorem MLE_mem_restrictDegree (evals : (σ → Fin 2) → R) : (MLE evals) ∈ R⦃≤ 1⦄[X σ] := by
  classical
  rw [mem_restrictDegree_iff_degreeOf_le]
  intro i
  calc
    _ ≤ (@Finset.univ (σ → Fin 2) _).sup
          fun x => degreeOf i ((eqPolynomial (x : σ → R)) * C (evals x)) := by
      exact degreeOf_sum_le i _ _
    _ ≤ (@Finset.univ (σ → Fin 2) _).sup
          fun x => degreeOf i (eqPolynomial (x : σ → R)) + degreeOf i (C (evals x)) := by
      gcongr
      exact degreeOf_mul_le i _ _
    _ ≤ (@Finset.univ (σ → Fin 2) _).sup fun x => 1 + 0 := by
      gcongr <;>
      simp [eqPolynomial_degreeOf]
    _ ≤ 1 := by simp

theorem MLE_degreeOf (evals : (σ → Fin 2) → R) (i : σ) : degreeOf i (MLE evals) ≤ 1 := by
  apply (mem_restrictDegree_iff_degreeOf_le _ _).mp
  exact MLE_mem_restrictDegree evals

/-- **Total degree of a multilinear polynomial.**  A polynomial with `degreeOf i ≤ 1` in each of
its `|σ|` variables has total degree at most `|σ|` — each monomial's exponents sum over the `≤ 1`
per-variable degrees.  This is the degree fact underlying multilinear Schwartz–Zippel / sum-check
round soundness (a nonzero multilinear polynomial has at most `|σ|/|F|` of its points as zeros). -/
theorem totalDegree_le_card_of_mem_restrictDegree_one {p : MvPolynomial σ R}
    (hp : p ∈ R⦃≤ 1⦄[X σ]) : p.totalDegree ≤ Fintype.card σ := by
  rw [mem_restrictDegree_iff_degreeOf_le] at hp
  apply Finset.sup_le
  intro m hm
  calc (m.sum fun _ e => e)
      = ∑ i ∈ m.support, m i := rfl
    _ ≤ ∑ i : σ, m i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ ∑ _i : σ, 1 :=
        Finset.sum_le_sum fun i _ => le_trans (monomial_le_degreeOf i hm) (hp i)
    _ = Fintype.card σ := by simp [Finset.card_univ]

/-- The multilinear extension of any evaluation function has total degree at most `|σ|`. -/
theorem MLE_totalDegree_le (evals : (σ → Fin 2) → R) : (MLE evals).totalDegree ≤ Fintype.card σ :=
  totalDegree_le_card_of_mem_restrictDegree_one (MLE_mem_restrictDegree evals)

end DegreeOf

/-! ### Linearity of the multilinear extension in the evaluation function

`MLE evals = ∑ x, eqPolynomial x * C (evals x)` is manifestly `R`-linear in `evals`.  These
lemmas record additivity, scalar homogeneity, and commutation with finite sums — the algebraic
foundation behind sum-check-style reductions, where the multilinear extension of a *linear
combination* of evaluation vectors (e.g. a matrix-vector product `M *ᵥ z = ∑ⱼ zⱼ • colⱼ`) splits
as the same combination of the column extensions. -/
section Linearity

/-- **MLE is additive in the evaluation function.** -/
theorem MLE_add (f g : (σ → Fin 2) → R) : MLE (f + g) = MLE f + MLE g := by
  unfold MLE
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.add_apply, map_add, mul_add]

/-- **MLE is scalar-homogeneous in the evaluation function.** -/
theorem MLE_smul (c : R) (f : (σ → Fin 2) → R) : MLE (c • f) = C c * MLE f := by
  unfold MLE
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/-- **MLE commutes with finite sums of evaluation functions.** -/
theorem MLE_sum {ι : Type*} (s : Finset ι) (f : ι → (σ → Fin 2) → R) :
    MLE (∑ j ∈ s, f j) = ∑ j ∈ s, MLE (f j) := by
  unfold MLE
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_apply, map_sum, Finset.mul_sum]

/-- **Pointwise form of `MLE_sum`.**  The multilinear extension of a pointwise finite sum of
evaluation functions is the sum of their extensions — the shape that arises when an evaluation
vector is written as a linear combination, `evals x = ∑ⱼ g j x`. -/
theorem MLE_sum_pointwise {ι : Type*} (s : Finset ι) (g : ι → (σ → Fin 2) → R) :
    MLE (fun x => ∑ j ∈ s, g j x) = ∑ j ∈ s, MLE (g j) := by
  rw [← MLE_sum]
  congr 1
  funext x
  exact (Finset.sum_apply x s g).symm

/-- **MLE of a scaled-sum (matrix-vector) evaluation vector.**  When the evaluation function is a
linear combination `evals x = ∑ⱼ z j * g j x` (the shape of a matrix-vector product
`(M *ᵥ z) i = ∑ⱼ M i j * z j`, with `g j` the `j`-th column evaluations and `z j` the scalars),
its extension splits as `∑ⱼ z j • MLE (g j)`.  This is the algebraic identity underlying the
sum-check decomposition `MLE(M *ᵥ z)(r) = ∑ⱼ z j · MLE(colⱼ)(r)`. -/
theorem MLE_scaled_sum {ι : Type*} (s : Finset ι) (z : ι → R) (g : ι → (σ → Fin 2) → R) :
    MLE (fun x => ∑ j ∈ s, z j * g j x) = ∑ j ∈ s, C (z j) * MLE (g j) := by
  rw [show (fun x => ∑ j ∈ s, z j * g j x) = ∑ j ∈ s, z j • g j by
        funext x; rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun j _ => rfl]
  rw [MLE_sum]
  exact Finset.sum_congr rfl fun j _ => MLE_smul (z j) (g j)

/-- **MLE evaluation as an eq-weighted sum over the hypercube.**  Evaluating the multilinear
extension at any point `r` is the `eqTilde`-weighted sum of the hypercube evaluations:
`eval r (MLE f) = ∑_{x ∈ {0,1}^σ} eqTilde r x · f x`, where `eqTilde r x = eval x (eqPolynomial r)`
is the multilinear equality kernel.  This is the fundamental identity underlying sum-check folding
(the general-ring analogue of the specialized `MLE_eval_eq_sum_eqTilde` in `RingSwitching/Prelude`). -/
theorem MLE_eval_eq_sum_eqTilde (f : (σ → Fin 2) → R) (r : σ → R) :
    eval r (MLE f) = ∑ x : σ → Fin 2, eqTilde r (x : σ → R) * f x := by
  unfold MLE
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [eval_mul, eval_C]
  simp only [eqTilde]
  rw [eqPolynomial_symm]

/-- **Evaluation form of `MLE_scaled_sum`.**  Evaluating the multilinear extension of a
matrix-vector evaluation vector at a point `r` splits as the scalar combination of the column
extensions evaluated at `r`:
`eval r (MLE (fun x => ∑ⱼ z j * g j x)) = ∑ⱼ z j * eval r (MLE (g j))`.
This is the directly-usable sum-check decomposition (e.g. Spartan's `evalClaimValue idx`
`= ∑ⱼ 𝕫 j * eval r_x (MLE colⱼ)`). -/
theorem MLE_eval_scaled_sum {ι : Type*} (s : Finset ι) (z : ι → R) (g : ι → (σ → Fin 2) → R)
    (r : σ → R) :
    eval r (MLE (fun x => ∑ j ∈ s, z j * g j x))
      = ∑ j ∈ s, z j * eval r (MLE (g j)) := by
  rw [MLE_scaled_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [eval_mul, eval_C]

end Linearity

-- Note: add lemmas about the uniqueness of multilinear polynomials up to evaluations on hypercube

variable [DecidableEq R] [IsDomain R]

omit [Fintype σ] [DecidableEq σ] [DecidableEq R] in
theorem is_multilinear_eq_iff_eq_evals_zeroOne (p : MvPolynomial σ R) (q : MvPolynomial σ R)
    [Finite σ]
    (hp : p ∈ R⦃≤ 1⦄[X σ]) (hq : q ∈ R⦃≤ 1⦄[X σ]) :
    p = q ↔ p.toEvalsZeroOne = q.toEvalsZeroOne := by
  classical
  letI := Fintype.ofFinite σ
  constructor <;> intro h
  · simp only [h]
  · unfold toEvalsZeroOne at h
    rw [mem_restrictDegree_iff_degreeOf_le] at hp hq
    let S : σ → Finset R := fun i => {0, 1}
    have hDegree : ∀ i, degreeOf i (p - q) < #(S i) := fun i => by
      have hSi : #(S i) = 2 := by simp [S]
      rw [hSi]
      apply Nat.lt_of_le_pred (by decide)
      apply le_trans (degreeOf_sub_le i _ _)
      simp [hp, hq]
    have hEval : ∀ x ∈ piFinset fun i => S i, eval (x : σ → R) (p - q) = 0 := fun x hx => by
      simp only [eval_sub, sub_eq_zero]
      have hx' : ∀ i, x i = 0 ∨ x i = 1 := by
        simpa [S] using hx
      let y : σ → Fin 2 := fun i => if x i = 0 then 0 else 1
      have : x = y := by
        ext i
        have := hx' i
        by_cases h : x i = 0 <;> simp_all [y]
      rw [this]
      apply funext_iff.mp at h
      exact h y
    suffices p - q = 0 by exact eq_of_sub_eq_zero this
    exact eq_zero_of_degreeOf_lt_card_of_eval_eq_zero S hDegree hEval

omit [DecidableEq R] in
theorem is_multilinear_iff_eq_evals_zeroOne {p : MvPolynomial σ R} :
    p ∈ R⦃≤ 1⦄[X σ] ↔ MLE p.toEvalsZeroOne = p := by
  classical
  constructor <;> intro h
  · refine (is_multilinear_eq_iff_eq_evals_zeroOne (MLE p.toEvalsZeroOne) p
      (MLE_mem_restrictDegree p.toEvalsZeroOne) h).mpr ?_
    unfold toEvalsZeroOne; simp only [MLE_eval_zeroOne]
  · rw [←h]
    exact MLE_mem_restrictDegree p.toEvalsZeroOne

omit [DecidableEq R] in
/-- **Direct uniqueness of the multilinear extension.**  A multilinear polynomial `p` that agrees
with `evals` on the Boolean hypercube *is* the multilinear extension `MLE evals`.  This is the
most directly-usable form of MLE uniqueness: it discharges interpolation arguments where one has
exhibited a multilinear `p` and checked its hypercube values. -/
theorem eq_MLE_of_isMultilinear_of_eval_eq {p : MvPolynomial σ R} (evals : (σ → Fin 2) → R)
    (hp : p ∈ R⦃≤ 1⦄[X σ]) (heval : ∀ x : σ → Fin 2, eval (x : σ → R) p = evals x) :
    p = MLE evals := by
  have hte : p.toEvalsZeroOne = evals := funext heval
  rw [← hte]
  exact (is_multilinear_iff_eq_evals_zeroOne.mp hp).symm

/-- Equivalence between multilinear polynomials and their evaluations on the Boolean hypercube -/
def MLEEquiv : R⦃≤ 1⦄[X σ] ≃ ((σ → Fin 2) → R) where
  toFun := fun p x => MvPolynomial.eval (x : σ → R) p
  invFun := fun evals => ⟨MLE evals, MLE_mem_restrictDegree evals⟩
  left_inv := fun ⟨p, hp⟩ => by
    simp only [Subtype.mk.injEq]
    exact is_multilinear_iff_eq_evals_zeroOne.mp hp
  right_inv := fun evals => by simp only [MLE_eval_zeroOne]

def MLEEquivFin {n : ℕ} : R⦃≤ 1⦄[X (Fin n)] ≃ (Fin (2 ^ n) → R) :=
  Equiv.trans MLEEquiv (Equiv.piCongr finFunctionFinEquiv (fun _ => Equiv.refl _))

end MvPolynomial

end
