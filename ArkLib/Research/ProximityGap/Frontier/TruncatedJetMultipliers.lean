/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.CanonicalQuarticSiteOrder
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-! # Independent monomial multiples of a translated plane jet

Order the jet monomials first by total degree and then by value exponent.
Multiplying those of degree below μ-r by an equation of order r has a
triangular minor whose diagonal is the leading coefficient of the equation.
The columns are the literal mixed coefficients of the polynomial products.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped BigOperators Matrix

namespace ArkLib.ProximityGap.Frontier.TruncatedJetMultipliers

/-- First index is total degree and second index is the value exponent. -/
abbrev JetIdx (μ : ℕ) := (i : Fin μ) × Fin (i.val+1)

theorem card_jetIdx (μ : ℕ) : Fintype.card (JetIdx μ) = μ*(μ+1)/2 := by
  simp only [JetIdx, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i+1)]
  have hh := Finset.sum_range_id_mul_two μ
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  cases μ with
  | zero => simp
  | succ μ =>
    simp only [Nat.succ_sub_one] at hh
    have he : ((∑ i ∈ range (μ+1), i)+(μ+1))*2 = (μ+1)*(μ+1+1) := by
      nlinarith only [hh]
    omega

private def key {μ : ℕ} (x : JetIdx μ) : ℕ ×ₗ ℕ := toLex (x.1.val,x.2.val)

private theorem key_injective (μ : ℕ) : Function.Injective (@key μ) := by
  rintro ⟨i,j⟩ ⟨u,v⟩ h
  have hh := congrArg ofLex h
  change (i.val,j.val) = (u.val,v.val) at hh
  have hi : i = u := Fin.ext (congrArg Prod.fst hh)
  subst u
  have hj : j = v := Fin.ext (congrArg Prod.snd hh)
  subst v
  rfl

private noncomputable local instance (μ : ℕ) : LinearOrder (JetIdx μ) :=
  LinearOrder.lift' key (key_injective μ)

/-- Lexicographically least monomial on the first nonzero homogeneous part. -/
structure Leader {R : Type*} [CommRing R] (F : R[X][X]) (r j : ℕ) : Prop where
  value_le : j ≤ r
  nonzero : (F.coeff j).coeff (r-j) ≠ 0
  lower : ∀ v q, v+q < r ∨ (v+q = r ∧ v < j) → (F.coeff v).coeff q = 0

variable {R : Type*} [CommRing R]

/-- Shift the leading monomial by the multiplier monomial. -/
def pivotRow {r j μ : ℕ} (hj : j ≤ r) (hr : r ≤ μ) (x : JetIdx (μ-r)) : JetIdx μ :=
  ⟨⟨r+x.1.val, by have := x.1.isLt; omega⟩,
    ⟨j+x.2.val, by change j+x.2.val < r+x.1.val+1; have := x.2.isLt; omega⟩⟩

/-- The genuine polynomial multiple by the monomial corresponding to a column. -/
def monomialMultiple {ν : ℕ} (F : R[X][X]) (c : JetIdx ν) : R[X][X] :=
  (F * Polynomial.C ((Polynomial.X : R[X])^(c.1.val-c.2.val))) * (Polynomial.X : R[X][X])^c.2.val

/-- Actual truncated coefficient vector of a plane polynomial. -/
def jet {μ : ℕ} (F : R[X][X]) (i : JetIdx μ) : R :=
  (F.coeff i.2.val).coeff (i.1.val-i.2.val)

/-- Columns of the multiplication matrix, truncated after the degree-μ-1 part. -/
def columns (μ ν : ℕ) (F : R[X][X]) : Matrix (JetIdx μ) (JetIdx ν) R :=
  fun i c => jet (monomialMultiple F c) i

private lemma columns_apply {μ ν : ℕ} (F : R[X][X]) (i : JetIdx μ) (c : JetIdx ν) :
    columns μ ν F i c =
    if c.2.val ≤ i.2.val ∧ c.1.val-c.2.val ≤ i.1.val-i.2.val then
      (F.coeff (i.2.val-c.2.val)).coeff (i.1.val-i.2.val-(c.1.val-c.2.val)) else 0 := by
  unfold columns jet monomialMultiple
  by_cases hv : c.2.val ≤ i.2.val <;> by_cases ht : c.1.val-c.2.val ≤ i.1.val-i.2.val <;>
    simp only [coeff_mul_X_pow', hv, ht, coeff_mul_C, coeff_zero, and_self, true_and,
      false_and, ite_true, ite_false]

/-- The maximal minor is a pure power of one actual coefficient. -/
theorem pivot_determinant {μ r j : ℕ} (F : R[X][X]) (h : Leader F r j) (hr : r ≤ μ) :
    ((columns μ (μ-r) F).submatrix (pivotRow h.value_le hr) id).det =
      ((F.coeff j).coeff (r-j)) ^ Fintype.card (JetIdx (μ-r)) := by
  let M := (columns μ (μ-r) F).submatrix (pivotRow h.value_le hr) id
  have entry (a b : JetIdx (μ-r)) : M a b =
      if b.2.val ≤ j+a.2.val ∧ b.1.val-b.2.val ≤ r+a.1.val-(j+a.2.val) then
        (F.coeff (j+a.2.val-b.2.val)).coeff
          (r+a.1.val-(j+a.2.val)-(b.1.val-b.2.val)) else 0 := by
    exact columns_apply F (pivotRow h.value_le hr a) b
  have hj := h.value_le
  have ht : M.IsLowerTriangular := by
    intro a b hab
    change key a < key b at hab
    simp only [key, Prod.Lex.toLex_lt_toLex] at hab
    change a.1.val < b.1.val ∨ a.1.val = b.1.val ∧ a.2.val < b.2.val at hab
    rw [entry]
    split_ifs with hle
    · apply h.lower
      have ha := a.2.isLt
      have hb := b.2.isLt
      omega
    · rfl
  have hd (a : JetIdx (μ-r)) : M a a = (F.coeff j).coeff (r-j) := by
    have ha := a.2.isLt
    rw [entry, ite_eq_left_iff.mpr (fun hn => False.elim (hn (by omega))), Nat.add_sub_cancel_right]
    have he : r+a.1.val-(j+a.2.val)-(a.1.val-a.2.val) = r-j := by omega
    rw [he]
  change M.det = _
  simp only [Matrix.det_of_isLowerTriangular M ht, hd, Finset.prod_const,
    Finset.card_univ]

/-- The low-degree multiplier columns are independent over any integral domain,
including the polynomial ring in the scalar before specialization. -/
theorem columns_injective [IsDomain R] {μ r j : ℕ} (F : R[X][X])
    (h : Leader F r j) (hr : r ≤ μ) : Function.Injective (columns μ (μ-r) F).mulVec := by
  intro x y hxy
  apply Matrix.mulVec_injective_of_det_ne_zero (M :=
    (columns μ (μ-r) F).submatrix (pivotRow h.value_le hr) id)
    (by rw [pivot_determinant F h hr]; exact pow_ne_zero _ h.nonzero)
  funext a
  exact congrFun hxy (pivotRow h.value_le hr a)

/-- Actual rank retained at a site. -/
theorem columns_rank {K : Type*} [Field K] {μ r j : ℕ} (F : K[X][X])
    (h : Leader F r j) (hr : r ≤ μ) :
    (columns μ (μ-r) F).rank = (μ-r)*(μ-r+1)/2 := by
  rw [Matrix.rank, LinearMap.finrank_range_of_inj (columns_injective F h hr),
    Module.finrank_eq_card_basis (Pi.basisFun K (JetIdx (μ-r))), card_jetIdx]

/-- Mixed Taylor translation at a received point, with value as outer variable. -/
def translate {K : Type} [Field K] (F : K[X][X]) (a : K) (w : K[X]) : K[X][X] :=
  (F.taylor w).map (Polynomial.taylorAlgHom a).toRingHom

@[simp] theorem translate_coeff {K : Type} [Field K] (F : K[X][X]) (a : K) (w : K[X])
    (i q : ℕ) : ((translate F a w).coeff i).coeff q = (((F.taylor w).coeff i).taylor a).coeff q := by
  rw [translate, coeff_map]
  rfl

/-- A primitive polynomial supplies a leading monomial at precisely its actual site order. -/
theorem exists_leader_at_site {K : Type} [Field K] (F : K[X][X]) (hF : F.IsPrimitive)
    (a : K) (w : K[X]) :
    ∃ j, Leader (translate F a w) (CanonicalQuarticSiteOrder.siteOrder F a w) j := by
  classical
  let r := CanonicalQuarticSiteOrder.siteOrder F a w
  let G := translate F a w
  have hz : ∀ i q, i+q < r → (G.coeff i).coeff q = 0 := by
    simpa only [G, translate_coeff] using
      (CanonicalQuarticSiteOrder.le_siteOrder_iff_jet F hF a w r).mp le_rfl
  have hn : ¬ ∀ i q, i+q < r+1 → (G.coeff i).coeff q = 0 := by
    intro he
    have hlt := (CanonicalQuarticSiteOrder.le_siteOrder_iff_jet F hF a w (r+1)).mpr
      (by simpa only [G, translate_coeff] using he)
    change r+1 ≤ r at hlt
    omega
  push Not at hn
  obtain ⟨i,q,hd,hn⟩ := hn
  have hsum : i+q = r := by by_contra hh; exact hn (hz i q (by omega))
  have hall : ∃ v, v ≤ r ∧ (G.coeff v).coeff (r-v) ≠ 0 :=
    ⟨i, by omega, by rwa [show r-i=q by omega]⟩
  refine ⟨Nat.find hall, (Nat.find_spec hall).1, (Nat.find_spec hall).2, ?_⟩
  intro v q hbefore
  rcases hbefore with hh | ⟨he,hl⟩
  · exact hz v q hh
  · have hm := Nat.find_min hall hl
    change (G.coeff v).coeff q = 0
    by_contra hc
    exact hm ⟨by omega, by rwa [show r-v=q by omega]⟩

/-- Specializing at a scalar preserves every genuine polynomial multiple identity,
including labels at which the leading jet monomial disappears. -/
theorem specialize_multiple {K : Type*} [Field K] {μ ν : ℕ} (z : K)
    (F : K[X][X][X]) (q : JetIdx ν → K[X]) (p : JetIdx μ → K[X])
    (h : (columns μ ν F).mulVec q = p) (i : JetIdx μ) :
    (p i).eval z = ∑ c, ((columns μ ν F i c).eval z) * (q c).eval z := by
  have he := congrArg (fun P : K[X] => P.eval z) (congrFun h i)
  simpa only [Matrix.mulVec, dotProduct, eval_finsetSum, eval_mul] using he.symm

end ArkLib.ProximityGap.Frontier.TruncatedJetMultipliers

open ArkLib.ProximityGap.Frontier.TruncatedJetMultipliers in
#print axioms columns_rank
open ArkLib.ProximityGap.Frontier.TruncatedJetMultipliers in
#print axioms exists_leader_at_site
