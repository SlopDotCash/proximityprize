/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Team
-/

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import ArkLib.Data.Polynomial.Multivariate.HasseDerivative

/-!
# List-Decoding Capacity Bounds from GKL24

This file formalizes the polynomial interpolation bounds for list-decoding capacity
as presented in Guruswami-Kopparty-Lovelock 2024 (GKL24).

The central result, `gkl24_interpolation_existence`, is the Guruswami–Sudan interpolation
step: given evaluation points with prescribed multiplicities, if the total number of
linear interpolation conditions
`∑_p binom(mult p + 1, 2)` is strictly smaller than the number of available monomial
coefficients `(deg_X + 1)(deg_Y + 1)`, then there is a *nonzero* bivariate polynomial
`Q(X, Y)` of `X`-degree `≤ deg_X` and `Y`-degree `≤ deg_Y` that vanishes at every point
with the prescribed Hasse-derivative multiplicity. The proof is the standard
"more unknowns than equations" linear-algebra argument: the interpolation conditions form
a homogeneous linear system whose coefficient matrix has fewer rows than columns, hence a
nontrivial kernel vector, which we assemble into `Q`.
-/

namespace CodingTheory.Bounds.GKL24

open MvPolynomial Matrix
open _root_.ArkLib.MvPolynomial
open scoped BigOperators

variable {F : Type} [Field F]

/-- Generates a list of all pairs `(i, j)` with `i + j < m`. -/
def pairs_lt : ℕ → List (ℕ × ℕ)
| 0 => []
| (m + 1) => pairs_lt m ++ (List.range (m + 1)).map (fun i => (i, m - i))

lemma length_pairs_lt (m : ℕ) : (pairs_lt m).length * 2 = m * (m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pairs_lt, List.length_append, List.length_map, List.length_range]
    linarith

/-- `pairs_lt m` contains exactly the pairs with index sum below `m`. -/
lemma mem_pairs_lt {i j m : ℕ} : (i, j) ∈ pairs_lt m ↔ i + j < m := by
  induction m with
  | zero => simp [pairs_lt]
  | succ m ih =>
    constructor
    · intro h
      rw [pairs_lt, List.mem_append] at h
      rcases h with h | h
      · have := ih.mp h; omega
      · simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at h
        obtain ⟨a, ha, ha1, ha2⟩ := h
        omega
    · intro h
      rw [pairs_lt, List.mem_append]
      rcases lt_or_ge (i + j) m with h' | h'
      · exact Or.inl (ih.mpr h')
      · right
        simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
        exact ⟨i, by omega, rfl, by omega⟩

/-- Maps a pair to a `Fin 2` multi-index. -/
noncomputable def d_of_pair (p : ℕ × ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 p.1 + Finsupp.single 1 p.2

@[simp] lemma d_of_pair_apply_zero (p : ℕ × ℕ) : (d_of_pair p) 0 = p.1 := by
  simp [d_of_pair, Finsupp.add_apply, Finsupp.single_apply]

@[simp] lemma d_of_pair_apply_one (p : ℕ × ℕ) : (d_of_pair p) 1 = p.2 := by
  simp [d_of_pair, Finsupp.add_apply, Finsupp.single_apply]

/-- Every `Fin 2 →₀ ℕ` multi-index is `d_of_pair` of its two values. -/
lemma d_of_pair_eq (d : Fin 2 →₀ ℕ) : d_of_pair (d 0, d 1) = d := by
  apply Finsupp.ext
  intro k
  fin_cases k <;> simp [d_of_pair, Finsupp.add_apply, Finsupp.single_apply]

/-- The degree sum of a `Fin 2 →₀ ℕ` multi-index is the sum of its two values. -/
lemma d_sum_eq (d : Fin 2 →₀ ℕ) : (d.sum fun _ v => v) = d 0 + d 1 := by
  rw [Finsupp.sum_fintype]
  · exact Fin.sum_univ_two _
  · intro _; rfl

/-- Generates conditions for a given point and multiplicity. -/
noncomputable def cond_list (p : F × F) (m : ℕ) : List ((F × F) × (Fin 2 →₀ ℕ)) :=
  (pairs_lt m).map (fun pair => (p, d_of_pair pair))

/-- Generates all conditions over all points. -/
noncomputable def all_conds (points : List (F × F)) (multiplicities : (F × F) → ℕ) :
    List ((F × F) × (Fin 2 →₀ ℕ)) :=
  points.flatMap (fun p => cond_list p (multiplicities p))

lemma length_all_conds (points : List (F × F)) (multiplicities : (F × F) → ℕ) :
    (all_conds points multiplicities).length
      = (points.map (fun p => (multiplicities p + 1) * multiplicities p / 2)).sum := by
  induction points with
  | nil => simp [all_conds]
  | cons p ps ih =>
    have hunf : all_conds (p :: ps) multiplicities
        = cond_list p (multiplicities p) ++ all_conds ps multiplicities := by
      simp only [all_conds, List.flatMap_cons]
    rw [hunf, List.length_append, ih, cond_list, List.length_map,
      List.map_cons, List.sum_cons]
    have h : (pairs_lt (multiplicities p)).length = (multiplicities p + 1) * multiplicities p / 2 := by
      have h2 := length_pairs_lt (multiplicities p)
      rw [mul_comm (multiplicities p) (multiplicities p + 1)] at h2
      omega
    rw [h]

/-- The index type for monomials `X^i Y^j` with `i ≤ deg_X`, `j ≤ deg_Y`. -/
abbrev MonomialIndex (deg_X deg_Y : ℕ) := Fin (deg_X + 1) × Fin (deg_Y + 1)

/-- The bivariate monomial `X^i Y^j` (with unit coefficient) attached to a column index. -/
noncomputable def colMonomial (deg_X deg_Y : ℕ) (mono : MonomialIndex deg_X deg_Y) :
    MvPolynomial (Fin 2) F :=
  monomial (d_of_pair (mono.1.val, mono.2.val)) 1

/-- The matrix representing the evaluation of Hasse derivatives at the interpolation
conditions. Row `k` is the `k`-th condition `(point, multi-index)`; column `mono` is the
monomial `X^i Y^j`. The entry is the value of the corresponding Hasse derivative of that
monomial at that point. -/
noncomputable def GKL24Matrix
    (points : List (F × F))
    (multiplicities : (F × F) → ℕ)
    (deg_X deg_Y : ℕ) :
    Matrix (Fin (all_conds points multiplicities).length) (MonomialIndex deg_X deg_Y) F :=
  fun k mono =>
    let p_d := (all_conds points multiplicities).get k
    eval ![p_d.1.1, p_d.1.2] (hasseDeriv p_d.2 (colMonomial deg_X deg_Y mono))

/-- A linear map from `Fin m` rows to `n > m` columns has a nontrivial kernel vector. -/
lemma matrix_exists_mulVec_eq_zero_of_lt {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix (Fin m) n F) (h : m < Fintype.card n) :
    ∃ v : n → F, v ≠ 0 ∧ A.mulVec v = 0 := by
  by_contra h_not
  push_neg at h_not
  have h_inj : Function.Injective A.toLin' := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra h_nz
    exact h_not v h_nz hv
  have hle := LinearMap.finrank_le_finrank_of_injective h_inj
  have : Fintype.card n ≤ m := by
    simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hle
  omega

/-- The kernel vector assembles into a nonzero polynomial. -/
lemma Q_of_v_ne_zero {deg_X deg_Y : ℕ} (v : MonomialIndex deg_X deg_Y → F) (hv : v ≠ 0) :
    (∑ mono, v mono • colMonomial deg_X deg_Y mono : MvPolynomial (Fin 2) F) ≠ 0 := by
  intro h_sum
  apply hv
  funext mono0
  have h_coeff := congr_arg (MvPolynomial.coeff (d_of_pair (mono0.1.val, mono0.2.val))) h_sum
  simp only [colMonomial, MvPolynomial.coeff_zero, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, smul_eq_mul] at h_coeff
  rw [Finset.sum_eq_single mono0] at h_coeff
  · simpa using h_coeff
  · intro b _ hb
    have hne : d_of_pair (b.1.val, b.2.val) ≠ d_of_pair (mono0.1.val, mono0.2.val) := by
      intro hc
      apply hb
      have h0 := congrArg (fun f => (f : Fin 2 →₀ ℕ) 0) hc
      have h1 := congrArg (fun f => (f : Fin 2 →₀ ℕ) 1) hc
      simp only [d_of_pair_apply_zero, d_of_pair_apply_one] at h0 h1
      exact Prod.ext (Fin.ext h0) (Fin.ext h1)
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ mono0) h

/-- Hasse derivatives are `F`-linear. -/
lemma hasseDeriv_smul (dd : Fin 2 →₀ ℕ) (c : F) (p : MvPolynomial (Fin 2) F) :
    hasseDeriv dd (c • p) = c • hasseDeriv dd p := by
  have htC : taylor (C c) = (C (C c) : MvPolynomial (Fin 2) (MvPolynomial (Fin 2) F)) := by
    simp only [taylor, eval₂Hom_C, RingHom.comp_apply]
  simp only [hasseDeriv, smul_eq_C_mul, map_mul, htC, MvPolynomial.coeff_C_mul]

/-- `eval ∘ hasseDeriv` distributes over finite sums of polynomials. -/
lemma eval_hasseDeriv_sum {ι : Type*} (a : Fin 2 → F) (dd : Fin 2 →₀ ℕ)
    (s : Finset ι) (f : ι → MvPolynomial (Fin 2) F) :
    eval a (hasseDeriv dd (∑ i ∈ s, f i)) = ∑ i ∈ s, eval a (hasseDeriv dd (f i)) := by
  simp only [hasseDeriv, map_sum, MvPolynomial.coeff_sum]

/-- **Guruswami–Sudan interpolation existence.**
If the number of interpolation conditions `∑_p binom(mult p + 1, 2)` is strictly below the
monomial-coefficient count `(deg_X + 1)(deg_Y + 1)`, there is a nonzero `Q(X, Y)` of the
prescribed degree vanishing at each point with the prescribed Hasse multiplicity. -/
theorem gkl24_interpolation_existence
    (points : Finset (F × F))
    (multiplicities : (F × F) → ℕ)
    (deg_X deg_Y : ℕ)
    (h_dim : (points.sum (fun p => (multiplicities p + 1) * multiplicities p / 2))
      < (deg_X + 1) * (deg_Y + 1)) :
    ∃ Q : MvPolynomial (Fin 2) F, Q ≠ 0 ∧
      (MvPolynomial.degreeOf 0 Q ≤ deg_X) ∧
      (MvPolynomial.degreeOf 1 Q ≤ deg_Y) ∧
      ∀ p ∈ points, ArkLib.MvPolynomial.mult_ge ![p.1, p.2] (multiplicities p) Q := by
  classical
  set pts := points.toList with hpts
  -- The interpolation system has fewer conditions than monomial coefficients.
  have hcard : (all_conds pts multiplicities).length < Fintype.card (MonomialIndex deg_X deg_Y) := by
    rw [length_all_conds]
    have ecard : Fintype.card (MonomialIndex deg_X deg_Y) = (deg_X + 1) * (deg_Y + 1) := by
      simp [MonomialIndex, Fintype.card_prod, Fintype.card_fin]
    rw [ecard, hpts, Finset.sum_map_toList]
    exact h_dim
  -- Extract a nontrivial kernel vector of the condition matrix.
  obtain ⟨v, hv_ne, hv_zero⟩ :=
    matrix_exists_mulVec_eq_zero_of_lt (GKL24Matrix pts multiplicities deg_X deg_Y) hcard
  set Q := (∑ mono : MonomialIndex deg_X deg_Y, v mono • colMonomial deg_X deg_Y mono :
    MvPolynomial (Fin 2) F) with hQdef
  -- Every monomial of `Q` is one of the bounded column monomials.
  have hmem : ∀ m ∈ Q.support,
      ∃ mono : MonomialIndex deg_X deg_Y, m = d_of_pair (mono.1.val, mono.2.val) := by
    intro m hm
    rw [hQdef] at hm
    rcases Finset.mem_biUnion.mp (MvPolynomial.support_sum hm) with ⟨mono, _, hmono⟩
    refine ⟨mono, ?_⟩
    have h2 := MvPolynomial.support_smul hmono
    have h3 := MvPolynomial.support_monomial_subset (s := d_of_pair (mono.1.val, mono.2.val)) h2
    rwa [Finset.mem_singleton] at h3
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · rw [hQdef]; exact Q_of_v_ne_zero v hv_ne
  · -- `X`-degree bound.
    rw [MvPolynomial.degreeOf_le_iff]
    intro m hm
    obtain ⟨mono, rfl⟩ := hmem m hm
    rw [d_of_pair_apply_zero]
    exact mono.1.is_le
  · -- `Y`-degree bound.
    rw [MvPolynomial.degreeOf_le_iff]
    intro m hm
    obtain ⟨mono, rfl⟩ := hmem m hm
    rw [d_of_pair_apply_one]
    exact mono.2.is_le
  · -- Vanishing with the prescribed Hasse multiplicity at every point.
    intro p hp d hd
    -- `d` corresponds to a condition row indexed by `(p, d)`.
    have hsum : (d.sum fun _ v => v) = d 0 + d 1 := d_sum_eq d
    have hmem_pair : (d 0, d 1) ∈ pairs_lt (multiplicities p) := by
      rw [mem_pairs_lt]; rw [hsum] at hd; exact hd
    have hmem_cond : (p, d) ∈ all_conds pts multiplicities := by
      rw [all_conds, List.mem_flatMap]
      refine ⟨p, ?_, ?_⟩
      · rw [hpts]; exact Finset.mem_toList.mpr hp
      · rw [cond_list, List.mem_map]
        exact ⟨(d 0, d 1), hmem_pair, by rw [d_of_pair_eq]⟩
    obtain ⟨k, hk⟩ := List.get_of_mem hmem_cond
    -- Read off the matrix entries at this row.
    have hAk : ∀ mono, GKL24Matrix pts multiplicities deg_X deg_Y k mono
        = eval ![p.1, p.2] (hasseDeriv d (colMonomial deg_X deg_Y mono)) := by
      intro mono
      simp only [GKL24Matrix]
      rw [hk]
    -- The kernel relation at this row is exactly the desired vanishing.
    have hmulvec : (GKL24Matrix pts multiplicities deg_X deg_Y).mulVec v k = 0 := by
      rw [hv_zero]; rfl
    have hmv : (GKL24Matrix pts multiplicities deg_X deg_Y).mulVec v k
        = ∑ mono, GKL24Matrix pts multiplicities deg_X deg_Y k mono * v mono := by
      rw [Matrix.mulVec, dotProduct]
    -- Expand `eval (hasseDeriv d Q)` linearly over the monomials of `Q`.
    rw [hQdef, eval_hasseDeriv_sum]
    have hterm : ∀ mono : MonomialIndex deg_X deg_Y,
        eval ![p.1, p.2] (hasseDeriv d (v mono • colMonomial deg_X deg_Y mono))
          = GKL24Matrix pts multiplicities deg_X deg_Y k mono * v mono := by
      intro mono
      rw [hasseDeriv_smul, smul_eq_C_mul, map_mul, eval_C, hAk mono]
      ring
    rw [Finset.sum_congr rfl (fun mono _ => hterm mono), ← hmv, hmulvec]

end CodingTheory.Bounds.GKL24
