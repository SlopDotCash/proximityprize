/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-! # Determinant multiplicity from a low-rank local approximation

Bordering an approximation of inner dimension `e` by an identity block expresses the
desired determinant by the Schur complement. Every term of the bordered determinant
selects at least `n - e` entries of the error in distinct rows and columns.
-/

namespace ProximityGap.PaleyDefectMinor

open Finset Matrix

variable {R : Type*} [CommRing R] {n e : ℕ}

/-- If an entrywise error is divisible by powers with given weights, any lower bound
on the weight of every matching of at least `n-e` entries is a determinant exponent. -/
theorem pow_dvd_det_of_weighted_approx (M : Matrix (Fin n) (Fin n) R)
    (U : Matrix (Fin n) (Fin e) R) (V : Matrix (Fin e) (Fin n) R) (t : R)
    (w : Fin n → Fin n → ℕ) (N : ℕ)
    (hentry : ∀ i j, t ^ w i j ∣ (M - U * V) i j)
    (hmatch : ∀ (S : Finset (Fin n)) (f : S ↪ Fin n), n - e ≤ S.card →
      N ≤ ∑ j : S, w (f j) j) : t ^ N ∣ M.det := by
  classical
  let Z := M - U * V
  let B := Matrix.fromBlocks Z U (-V) (1 : Matrix (Fin e) (Fin e) R)
  have hdet : B.det = M.det := by simp [B, Z, Matrix.det_fromBlocks_one₂₂]
  rw [← hdet, Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  apply dvd_mul_of_dvd_right
  rw [Fintype.prod_sum_type]
  apply dvd_mul_of_dvd_left
  let S := univ.filter (fun j : Fin n => (σ (Sum.inl j)).isLeft)
  have hl (j : S) : (σ (Sum.inl j.val)).isLeft := (mem_filter.mp j.property).2
  have hr (j : ↥Sᶜ) : (σ (Sum.inl j.val)).isRight := by
    apply Sum.not_isLeft.mp
    exact fun h => (mem_compl.mp j.property) (mem_filter.mpr ⟨mem_univ _, h⟩)
  let f : S ↪ Fin n := {
    toFun j := (σ (Sum.inl j.val)).getLeft (hl j)
    inj' := by
      intro i j hij
      apply Subtype.ext
      apply Sum.inl.inj
      apply σ.injective
      simpa only [Sum.inl_getLeft] using congrArg (Sum.inl (β := Fin e)) hij }
  have hf (j : S) : Sum.inl (f j) = σ (Sum.inl j.val) := Sum.inl_getLeft _ _
  let g (j : ↥Sᶜ) : Fin e := (σ (Sum.inl j.val)).getRight (hr j)
  have hg : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    apply Sum.inl.inj
    apply σ.injective
    simpa only [g, Sum.inr_getRight] using congrArg (Sum.inr (α := Fin n)) hij
  have hc := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin] at hc
  refine (pow_dvd_pow t (hmatch S f (by omega))).trans ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  have hprod : (∏ j : S, t ^ w (f j) j) ∣ ∏ j : S, B (σ (Sum.inl j.val)) (Sum.inl j.val) := by
    apply Finset.prod_dvd_prod_of_dvd
    intro j _
    rw [← hf j]
    exact hentry (f j) j
  refine hprod.trans ?_
  rw [Finset.prod_coe_sort S (fun i : Fin n => B (σ (Sum.inl i)) (Sum.inl i))]
  exact Finset.prod_dvd_prod_of_subset S univ _ (subset_univ _)

/-- A uniform order-`s` error from a matrix factoring through `e` coordinates forces
the determinant to vanish to order at least `s * (n - e)`. -/
theorem pow_dvd_det_of_approx (M : Matrix (Fin n) (Fin n) R)
    (U : Matrix (Fin n) (Fin e) R) (V : Matrix (Fin e) (Fin n) R)
    (t : R) (s : ℕ) (hentry : ∀ i j, t ^ s ∣ (M - U * V) i j) :
    t ^ (s * (n-e)) ∣ M.det := by
  apply pow_dvd_det_of_weighted_approx M U V t (fun _ _ => s) _ hentry
  intro S f hS
  simpa [Nat.mul_comm] using Nat.mul_le_mul_left s hS

private theorem twice_sum_ge (S : Finset ℕ) :
    S.card * (S.card - 1) ≤ 2 * ∑ i ∈ S, i := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S ha ih =>
    have hn : a ∉ S := fun h => lt_irrefl a (ha a h)
    have hcard : S.card ≤ a := (Finset.card_le_card
      (show S ⊆ range a from fun i hi => mem_range.mpr (ha i hi))).trans_eq (card_range _)
    rw [card_insert_of_notMem hn, sum_insert hn]
    rcases Nat.eq_zero_or_pos S.card with h | h
    · simp [h]
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
      rw [hm] at ih hcard ⊢
      simp only [Nat.succ_sub_one] at ih ⊢
      nlinarith

private theorem twice_sum_emb_ge {ι : Type*} [Fintype ι] (f : ι ↪ ℕ) :
    Fintype.card ι * (Fintype.card ι - 1) ≤ 2 * ∑ i, f i := by
  simpa only [card_map, card_univ, sum_map, Function.Embedding.coeFn_mk] using
    twice_sum_ge (univ.map f)

/-- If entry `i,j` of the error vanishes to order `s + (h-i) + (h-j)`, both the
row and column indices in each matching are distinct. Their two triangular sums
yield an additional `r(r-1)` orders, where `r = h+1-e`. -/
theorem pow_dvd_det_of_derivative_approx {h : ℕ} (M : Matrix (Fin (h+1)) (Fin (h+1)) R)
    (U : Matrix (Fin (h+1)) (Fin e) R) (V : Matrix (Fin e) (Fin (h+1)) R)
    (t : R) (s : ℕ) (hentry : ∀ i j, t ^ (s + (h-i.val) + (h-j.val)) ∣ (M - U * V) i j) :
    let r := h + 1 - e
    t ^ (r * s + r * (r - 1)) ∣ M.det := by
  let r := h + 1 - e
  apply pow_dvd_det_of_weighted_approx M U V t (fun i j => s + (h - i.val) + (h - j.val)) _ hentry
  intro S f hS
  let weight : Fin (h+1) ↪ ℕ := {
    toFun i := h - i.val
    inj' := by intro i j he; apply Fin.ext; change h - i.val = h - j.val at he; omega }
  have h₁ := twice_sum_emb_ge (f.trans weight)
  have h₂ := twice_sum_emb_ge ((Function.Embedding.subtype (· ∈ S)).trans weight)
  rw [Fintype.card_coe] at h₁ h₂
  change S.card * (S.card - 1) ≤ 2 * ∑ j : S, (h - (f j).val) at h₁
  change S.card * (S.card - 1) ≤ 2 * ∑ j : S, (h - j.val.val) at h₂
  have hs : r * s ≤ S.card * s := Nat.mul_le_mul_right s hS
  have ht : r * (r - 1) ≤ S.card * (S.card - 1) :=
    Nat.mul_le_mul hS (Nat.sub_le_sub_right hS 1)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
  change r * s + r * (r - 1) ≤ S.card * s + (∑ j : S, (h - (f j).val)) +
    (∑ j : S, (h - j.val.val))
  omega

open Polynomial

/-- Hankel matrix of ordinary derivatives normalized by the corresponding falling
factorial of the shift degree. -/
noncomputable def normalizedHankel {K : Type*} [Field K] (F : K[X]) (D h : ℕ) :
    Matrix (Fin (h+1)) (Fin (h+1)) K[X] := fun i j =>
  C ((D.descFactorial (i.val + j.val) : K)⁻¹) * derivative^[i.val + j.val] F

/-- The normalized derivative matrix of a sum of shifted powers factors through one
column per summand over the polynomial ring itself. -/
theorem normalizedHankel_shifted_powers_factors {K : Type*} [Field K]
    (a c : Fin e → K) (D h : ℕ) (hD : 2*h ≤ D)
    (hunit : ∀ k ≤ 2*h, (D.descFactorial k : K) ≠ 0) :
    ∃ (U : Matrix (Fin (h+1)) (Fin e) K[X]) (V : Matrix (Fin e) (Fin (h+1)) K[X]),
      normalizedHankel (∑ l : Fin e, C (c l) * (X + C (a l)) ^ D) D h = U * V := by
  let W := ∑ l : Fin e, C (c l) * (X + C (a l)) ^ D
  let U : Matrix (Fin (h+1)) (Fin e) K[X] := fun i l =>
    C (c l) * (X + C (a l)) ^ (D - 2*h + (h-i.val))
  let V : Matrix (Fin e) (Fin (h+1)) K[X] := fun l j => (X + C (a l)) ^ (h-j.val)
  have heq : normalizedHankel W D h = U * V := by
    ext i j : 1
    let k := i.val + j.val
    let z : K := D.descFactorial k
    have hz : z ≠ 0 := hunit k (by dsimp [k]; omega)
    change C z⁻¹ * derivative^[k] W = (U * V) i j
    rw [Matrix.mul_apply, show W = _ from rfl, iterate_derivative_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [iterate_derivative_C_mul, iterate_derivative_X_add_pow, nsmul_eq_mul, ← C_eq_natCast]
    change C z⁻¹ * (C (c l) * (C z * (X + C (a l)) ^ (D-k))) = _
    calc
      _ = C (c l) * (C z⁻¹ * C z) * (X + C (a l)) ^ (D-k) := by ring
      _ = _ := by
        rw [← C_mul, inv_mul_cancel₀ hz, C_1, mul_one]
        dsimp only [U, V]
        rw [mul_assoc, ← pow_add]
        congr 2
        dsimp [k]
        omega
  exact ⟨U,V,heq⟩

/-- Polynomial contact with an approximant whose normalized derivative matrix factors
through `e` columns gives a weighted determinant divisor. -/
theorem pow_dvd_normalizedHankel_of_factored_contact {K : Type*} [Field K]
    (F W t : K[X]) (D h s : ℕ) (U : Matrix (Fin (h+1)) (Fin e) K[X])
    (V : Matrix (Fin e) (Fin (h+1)) K[X]) (heq : normalizedHankel W D h = U * V)
    (hcontact : t ^ (s + 2*h) ∣ F - W) :
    let r := h + 1 - e
    t ^ (r * s + r * (r - 1)) ∣ (normalizedHankel F D h).det := by
  apply pow_dvd_det_of_derivative_approx (normalizedHankel F D h) U V t s
  intro i j
  let k := i.val + j.val
  have hdvd := pow_sub_dvd_iterate_derivative_of_pow_dvd k
    hcontact
  have hw : s + (h-i.val) + (h-j.val) = s + 2*h - k := by dsimp [k]; omega
  rw [hw, ← heq, Matrix.sub_apply]
  change t ^ (s + 2*h - k) ∣ C ((D.descFactorial k : K)⁻¹) * derivative^[k] F -
    C ((D.descFactorial k : K)⁻¹) * derivative^[k] W
  rw [← mul_sub, ← iterate_derivative_sub]
  exact dvd_mul_of_dvd_right hdvd _

/-- A single contact congruence to `e` shifted powers implies the full weighted
multiplicity of the normalized Hankel determinant. In the Hanson–Petridis
application `t = X - C b` and the shifted powers are the exceptional signs. -/
theorem pow_dvd_normalizedHankel_of_contact {K : Type*} [Field K] (F t : K[X])
    (a c : Fin e → K) (D h s : ℕ) (hD : 2*h ≤ D)
    (hunit : ∀ k ≤ 2*h, (D.descFactorial k : K) ≠ 0)
    (hcontact : t ^ (s + 2*h) ∣ F - ∑ l : Fin e, C (c l) * (X + C (a l)) ^ D) :
    let r := h + 1 - e
    t ^ (r * s + r * (r - 1)) ∣ (normalizedHankel F D h).det := by
  obtain ⟨U,V,heq⟩ := normalizedHankel_shifted_powers_factors a c D h hD hunit
  exact pow_dvd_normalizedHankel_of_factored_contact F _ t D h s U V heq hcontact

#print axioms pow_dvd_normalizedHankel_of_contact
#print axioms pow_dvd_det_of_derivative_approx
#print axioms pow_dvd_det_of_weighted_approx
#print axioms pow_dvd_det_of_approx

end ProximityGap.PaleyDefectMinor
