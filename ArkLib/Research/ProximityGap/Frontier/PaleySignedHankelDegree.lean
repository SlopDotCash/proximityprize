/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyDefectMinor
import ArkLib.Research.ProximityGap.Frontier.PaleyInterpolationContact
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Nonvanishing and minority-corrected degree of the arbitrary-sign Paley Hankel determinant

Formalizes the Wronskian/column-reversal Vandermonde theorem of
`docs/research/proximity-gap/paley-signed-square-root.md`:
for every odd prime `p`, every `A ⊆ ZMod p` with `2 ≤ |A| ≤ (p - 1)/2 + 1`, every individual
site sign function `w : ZMod p → ℤ` with `w u ∈ {±1}` on `A`, and every width `1 ≤ x ≤ |A| / 2`,
the normalized Hankel determinant `signedDet A w (x - 1)` is nonzero and has degree at most
`D_x = x(d + a - 2x) - (x - s)_+(a - x - s)_+`, where `s` is the minority sign count on `A`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

namespace ProximityGap.PaleySignedHankelDegree

open Finset Matrix Polynomial
open PaleyDefectMinor PaleyInterpolationContact
open scoped Polynomial

section Defs

variable {p : ℕ} [Fact p.Prime]

/-- Signed quadratic-character row sum `W_w(b) = ∑ u ∈ A, w u * χ(b + u)`. -/
def signedShiftSum (A : Finset (ZMod p)) (w : ZMod p → ℤ) (b : ZMod p) : ℤ :=
  ∑ u ∈ A, w u * quadraticChar (ZMod p) (b + u)

/-- Lagrange-weighted shifted power sum with arbitrary per-site signs `w u`. -/
noncomputable def signedPowerSum (A U : Finset (ZMod p)) (w : ZMod p → ℤ) (D : ℕ) : (ZMod p)[X] :=
  ∑ u ∈ U, C (Lagrange.nodalWeight A id u * (w u : ZMod p)) * (X + C u) ^ D

/-- Normalized `(h + 1) × (h + 1)` Hankel determinant for the arbitrary-sign power sum at
degree `D = p / 2 + (A.card - 2)`. -/
noncomputable def signedDet (A : Finset (ZMod p)) (w : ZMod p → ℤ) (h : ℕ) : (ZMod p)[X] :=
  let D := p / 2 + (A.card - 2)
  (normalizedHankel (signedPowerSum A A w D) D h).det

/-- Minority sign count `min(#{u ∈ A | w u = 1}, #{u ∈ A | w u = -1})`. -/
noncomputable def minorityCount (A : Finset (ZMod p)) (w : ZMod p → ℤ) : ℕ :=
  min (A.filter fun u => w u = 1).card (A.filter fun u => w u = -1).card

/-- Sharp minority-corrected degree budget `D_x = x(d + a - 2x) - (x - s)_+(a - x - s)_+`. -/
def degreeBudget (d a x s : ℕ) : ℕ :=
  x * (d + a - 2 * x) - (x - s) * (a - x - s)

end Defs

section Helpers

private theorem twice_sum_distinct_ge {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) :
    n * (n - 1) ≤ 2 * ∑ i : Fin n, f i := by
  have hge : ∀ S : Finset ℕ, S.card * (S.card - 1) ≤ 2 * ∑ a ∈ S, a := by
    intro S
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
  have := hge (univ.map ⟨f, hf⟩)
  simpa only [card_map, card_univ, Fintype.card_fin, sum_map, Function.Embedding.coeFn_mk] using this

private theorem twice_sum_distinct_le {n b : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f)
    (hb : ∀ i, f i ≤ b) :
    2 * (∑ i : Fin n, f i) + n * (n - 1) ≤ 2 * n * b := by
  have hinv : Function.Injective (fun i : Fin n => b - f i) := fun i j hij => by
    dsimp only at hij
    exact hf (by have := hb i; have := hb j; omega)
  have h1 := twice_sum_distinct_ge (fun i : Fin n => b - f i) hinv
  have h2 : (∑ i : Fin n, (b - f i)) + ∑ i : Fin n, f i = n * b := by
    rw [← sum_add_distrib]
    have hcongr : ∑ i : Fin n, (b - f i + f i) = ∑ _i : Fin n, b :=
      sum_congr rfl fun i _ => Nat.sub_add_cancel (hb i)
    rw [hcongr, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  have h3 : 2 * n * b = 2 * (n * b) := by ring
  omega

private theorem nz_cast_zmod {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 0 < n) (hp : n < p) :
    (n : ZMod p) ≠ 0 := by
  intro hz
  have h := congrArg ZMod.val hz
  rw [ZMod.val_natCast_of_lt hp, ZMod.val_zero] at h
  omega

theorem descFactorial_ne_zero_zmod {p : ℕ} [Fact p.Prime] {D : ℕ} (hD : D < p)
    {k : ℕ} (hk : k ≤ D) : (D.descFactorial k : ZMod p) ≠ 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Nat.cast_mul]
    exact mul_ne_zero (nz_cast_zmod (by omega) (by omega)) (ih (by omega))

private theorem choose_ne_zero_zmod {p : ℕ} [Fact p.Prime] {N : ℕ} (hN : N < p)
    {k : ℕ} (hk : k ≤ N) : (N.choose k : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdiv
  have htf : N.choose k ∣ N.factorial := ⟨k.factorial * (N - k).factorial, by
    rw [← mul_assoc, Nat.choose_mul_factorial_mul_factorial hk]⟩
  exact (not_le.mpr hN) ((Fact.out : p.Prime).dvd_factorial.mp (hdiv.trans htf))

private theorem nodalWeight_ne_zero {K : Type*} [Field K] [DecidableEq K]
    (A : Finset K) {u : K} (_hu : u ∈ A) : Lagrange.nodalWeight A id u ≠ 0 := by
  unfold Lagrange.nodalWeight
  rw [Finset.prod_ne_zero_iff]
  intro v hv
  exact inv_ne_zero (sub_ne_zero.mpr (ne_of_mem_erase hv).symm)

private theorem nodalWeight_eval_sum {K : Type*} [Field K] [DecidableEq K]
    (A : Finset K) (P : K[X]) (hdeg : P.natDegree < A.card) :
    ∑ u ∈ A, Lagrange.nodalWeight A id u * P.eval u = P.coeff (A.card - 1) := by
  rcases Nat.eq_zero_or_pos A.card with ha0 | ha_pos
  · simp [Finset.card_eq_zero.mp ha0] at hdeg
  · have hP : P = ∑ k ∈ range A.card, C (P.coeff k) * X ^ k := by
      simpa only [← Polynomial.C_mul_X_pow_eq_monomial] using Polynomial.as_sum_range' P A.card hdeg
    conv_lhs =>
      arg 2; ext u
      rw [hP, eval_finsetSum, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ k ∈ range A.card,
        ∑ u ∈ A, Lagrange.nodalWeight A id u * (C (P.coeff k) * X ^ k).eval u =
          if k = A.card - 1 then P.coeff (A.card - 1) else 0 := by
      intro k hk
      have hklt : k < A.card := mem_range.mp hk
      have hpull : ∑ u ∈ A, Lagrange.nodalWeight A id u * (C (P.coeff k) * X ^ k).eval u =
          P.coeff k * ∑ u ∈ A, Lagrange.nodalWeight A id u * (0 + u) ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [eval_mul, eval_C, eval_pow, eval_X, zero_add]
        ring
      rw [hpull, nodalWeight_shift_moment A 0 hklt]
      split_ifs with he
      · rw [he, mul_one]
      · rw [mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    simp [show A.card - 1 < A.card by omega]

end Helpers

/-! ## 2. Wronskian nonvanishing and minority-corrected degree bound -/

section WronskianDegree

variable {p : ℕ} [Fact p.Prime]

/-- Falling-factorial polynomial `∏_{m < k} (X - m)`. -/
private noncomputable def descPoly (k : ℕ) : (ZMod p)[X] :=
  ∏ m ∈ range k, (X - C (m : ZMod p))

private theorem descPoly_monic (k : ℕ) : (descPoly (p := p) k).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

private theorem descPoly_natDegree (k : ℕ) : (descPoly (p := p) k).natDegree = k := by
  unfold descPoly
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

private theorem descPoly_eval_natCast (k n : ℕ) :
    (descPoly (p := p) k).eval (n : ZMod p) = (n.descFactorial k : ZMod p) := by
  induction k with
  | zero => simp [descPoly]
  | succ k ih =>
    rw [descPoly, prod_range_succ, eval_mul, eval_sub, eval_X, eval_C, ← descPoly, ih,
      Nat.descFactorial_succ, Nat.cast_mul, mul_comm]
    by_cases hkn : k ≤ n
    · rw [Nat.cast_sub hkn]
    · have hlt : n < k := by omega
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt, Nat.cast_zero, mul_zero, mul_zero]

/-- Falling-factorial Vandermonde determinant is nonzero for distinct naturals `< p`. -/
private theorem det_descFactorial_ne_zero {m : ℕ} (l : Fin m → ℕ)
    (hinj : Function.Injective l) (hlt : ∀ j, l j < p) :
    Matrix.det (fun i j : Fin m => ((l j).descFactorial i.val : ZMod p)) ≠ 0 := by
  let L : Matrix (Fin m) (Fin m) (ZMod p) := Matrix.of fun i r => (descPoly i.val).coeff r.val
  let V : Matrix (Fin m) (Fin m) (ZMod p) := Matrix.of fun r j => (l j : ZMod p) ^ r.val
  have hmul : (fun i j : Fin m => ((l j).descFactorial i.val : ZMod p)) = L * V := by
    ext i j
    rw [← descPoly_eval_natCast i.val (l j), Matrix.mul_apply]
    have hdeg : (descPoly (p := p) i.val).natDegree < m := by
      rw [descPoly_natDegree]; exact i.isLt
    rw [Polynomial.as_sum_range' (descPoly (p := p) i.val) m hdeg, eval_finsetSum,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [L, V]
  have hL_lower : L.IsLowerTriangular := by
    intro i r hir
    dsimp [L]
    apply coeff_eq_zero_of_natDegree_lt
    rw [descPoly_natDegree]
    exact hir
  have hL_det : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular L hL_lower]
    refine Finset.prod_eq_one fun i _ => ?_
    have h1 := (descPoly_monic (p := p) i.val).leadingCoeff
    rw [leadingCoeff, descPoly_natDegree] at h1
    exact h1
  have hV_det : V.det ≠ 0 := by
    have hVT : Vᵀ = Matrix.vandermonde (fun j => (l j : ZMod p)) := by
      ext j r; rfl
    rw [← Matrix.det_transpose, hVT, Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    apply hinj
    have hval := congrArg ZMod.val hij
    rw [ZMod.val_natCast_of_lt (hlt i), ZMod.val_natCast_of_lt (hlt j)] at hval
    exact hval
  rw [hmul, Matrix.det_mul, hL_det, one_mul]
  exact hV_det

/-- Normalized Wronskian matrix `W i j = (N.descFactorial i)⁻¹ * g_j^(i)`. -/
private noncomputable def normWronskian {m : ℕ} (N : ℕ) (g : Fin m → (ZMod p)[X]) :
    Matrix (Fin m) (Fin m) (ZMod p)[X] :=
  fun i j => C ((N.descFactorial i.val : ZMod p)⁻¹) * derivative^[i.val] (g j)

private theorem coeff_prod_le {K : Type*} [Field K] {ι : Type*} (S : Finset ι) (P : ι → K[X])
    (w : ι → ℕ) (hw : ∀ i ∈ S, (P i).natDegree ≤ w i) :
    (∏ i ∈ S, P i).coeff (∑ i ∈ S, w i) = ∏ i ∈ S, (P i).coeff (w i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    simp only [prod_insert ha, sum_insert ha]
    have hS (i) (hi : i ∈ S) := hw i (mem_insert_of_mem hi)
    rw [coeff_mul_add_eq_of_natDegree_le (hw a (mem_insert_self _ _))
      ((natDegree_prod_le _ _).trans (sum_le_sum hS)), ih hS]

/-- If `g_0, ..., g_{m-1}` are nonzero polynomials of distinct degrees `l_j ≤ N < p`, then
`det (normWronskian N g)` is nonzero with exact degree `(∑ l_j) - m(m-1)/2`. -/
private theorem normWronskian_det_ne_zero_and_deg {m : ℕ} (N : ℕ) (hN : N < p) (hmN : m ≤ N + 1)
    (g : Fin m → (ZMod p)[X]) (hg_ne : ∀ j, g j ≠ 0)
    (hg_le : ∀ j, (g j).natDegree ≤ N) (hg_inj : Function.Injective fun j => (g j).natDegree) :
    (normWronskian N g).det ≠ 0 ∧
      (normWronskian N g).det.natDegree = (∑ j : Fin m, (g j).natDegree) - m * (m - 1) / 2 := by
  classical
  let l : Fin m → ℕ := fun j => (g j).natDegree
  have hsum_ge : m * (m - 1) ≤ 2 * ∑ j : Fin m, l j := twice_sum_distinct_ge l hg_inj
  have htri : ∑ i : Fin m, i.val = m * (m - 1) / 2 := by
    have h := sum_range_id_mul_two m
    have h1 : ∑ i : Fin m, i.val = ∑ i ∈ range m, i := Fin.sum_univ_eq_sum_range id m
    omega
  set T : ℕ := (∑ j : Fin m, l j) - m * (m - 1) / 2
  have hperm_deg : ∀ σ : Equiv.Perm (Fin m),
      (∏ j : Fin m, normWronskian N g (σ j) j).natDegree ≤ T := by
    intro σ
    by_cases hlt : ∃ j : Fin m, l j < (σ j).val
    · obtain ⟨j₀, hj₀⟩ := hlt
      have hz : normWronskian N g (σ j₀) j₀ = 0 := by
        unfold normWronskian
        rw [iterate_derivative_eq_zero hj₀, mul_zero]
      have hprod0 : ∏ j : Fin m, normWronskian N g (σ j) j = 0 :=
        Finset.prod_eq_zero (mem_univ j₀) hz
      rw [hprod0, natDegree_zero]
      exact Nat.zero_le _
    · push Not at hlt
      refine (natDegree_prod_le _ _).trans ?_
      have hle : ∑ j : Fin m, (normWronskian N g (σ j) j).natDegree ≤
          ∑ j : Fin m, (l j - (σ j).val) :=
        Finset.sum_le_sum fun j _ =>
          (natDegree_C_mul_le _ _).trans (natDegree_iterate_derivative (g j) (σ j).val)
      have hsub : (∑ j : Fin m, (l j - (σ j).val)) + ∑ j : Fin m, (σ j).val =
          ∑ j : Fin m, l j := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun j _ => Nat.sub_add_cancel (hlt j)
      have hperm : ∑ j : Fin m, (σ j).val = ∑ i : Fin m, i.val := Equiv.sum_comp σ _
      rw [hperm, htri] at hsub
      exact hle.trans (by dsimp [T]; omega)
  have hdeg_le : (normWronskian N g).det.natDegree ≤ T := by
    rw [Matrix.det_apply]
    exact natDegree_sum_le_of_forall_le _ _ fun σ _ =>
      (natDegree_smul_le _ _).trans (hperm_deg σ)
  -- Compute coefficient at `T`:
  let S : Matrix (Fin m) (Fin m) (ZMod p) := fun i j =>
    (N.descFactorial i.val : ZMod p)⁻¹ * ((l j).descFactorial i.val : ZMod p) * (g j).leadingCoeff
  have hcoeff_T : (normWronskian N g).det.coeff T = S.det := by
    rw [Matrix.det_apply, finsetSum_coeff, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [coeff_smul]
    congr 1
    by_cases hlt : ∃ j : Fin m, l j < (σ j).val
    · obtain ⟨j₀, hj₀⟩ := hlt
      have hz1 : normWronskian N g (σ j₀) j₀ = 0 := by
        unfold normWronskian
        rw [iterate_derivative_eq_zero hj₀, mul_zero]
      have hz2 : S (σ j₀) j₀ = 0 := by
        dsimp [S]
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr hj₀, Nat.cast_zero, mul_zero, zero_mul]
      have hp1 : ∏ j : Fin m, normWronskian N g (σ j) j = 0 :=
        Finset.prod_eq_zero (mem_univ j₀) hz1
      have hp2 : ∏ j : Fin m, S (σ j) j = 0 :=
        Finset.prod_eq_zero (mem_univ j₀) hz2
      rw [hp1, coeff_zero, hp2]
    · push Not at hlt
      have hsum_w : ∑ j : Fin m, (l j - (σ j).val) = T := by
        have hsub : (∑ j : Fin m, (l j - (σ j).val)) + ∑ j : Fin m, (σ j).val =
            ∑ j : Fin m, l j := by
          rw [← sum_add_distrib]
          exact sum_congr rfl fun j _ => Nat.sub_add_cancel (hlt j)
        have hperm : ∑ j : Fin m, (σ j).val = ∑ i : Fin m, i.val := Equiv.sum_comp σ _
        rw [hperm, htri] at hsub
        dsimp [T]; omega
      rw [← hsum_w, coeff_prod_le univ (fun j => normWronskian N g (σ j) j)
        (fun j => l j - (σ j).val) (fun j _ =>
          (natDegree_C_mul_le _ _).trans (natDegree_iterate_derivative (g j) (σ j).val))]
      refine Finset.prod_congr rfl fun j _ => ?_
      unfold normWronskian
      rw [coeff_C_mul, coeff_iterate_derivative, Nat.sub_add_cancel (hlt j), nsmul_eq_mul,
        show (g j).coeff (l j) = (g j).leadingCoeff from rfl]
      dsimp [S]; ring
  have hS_ne : S.det ≠ 0 := by
    let D₁ : Matrix (Fin m) (Fin m) (ZMod p) := Matrix.diagonal fun i =>
      (N.descFactorial i.val : ZMod p)⁻¹
    let F : Matrix (Fin m) (Fin m) (ZMod p) := fun i j => ((l j).descFactorial i.val : ZMod p)
    let D₂ : Matrix (Fin m) (Fin m) (ZMod p) := Matrix.diagonal fun j => (g j).leadingCoeff
    have hS_fac : S = D₁ * F * D₂ := by
      ext i j
      dsimp only [D₁, D₂]
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hS_fac, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · rw [Finset.prod_ne_zero_iff]
      intro i _
      exact inv_ne_zero (descFactorial_ne_zero_zmod hN (by have := i.isLt; omega))
    · exact det_descFactorial_ne_zero l hg_inj fun j => (hg_le j).trans_lt hN
    · rw [Finset.prod_ne_zero_iff]
      intro j _
      exact leadingCoeff_ne_zero.mpr (hg_ne j)
  have hne : (normWronskian N g).det ≠ 0 := fun hz => by
    rw [hz, coeff_zero] at hcoeff_T
    exact hS_ne hcoeff_T.symm
  refine ⟨hne, le_antisymm hdeg_le (le_natDegree_of_ne_zero (by rwa [hcoeff_T]))⟩

/-- Elementary column reduction produces an invertible scalar matrix turning any linearly
independent `n`-tuple of polynomials into one with distinct degrees, preserving a degree upper
bound `b` and leaving a suffix `[k, n)` whose degrees are already distinct untouched. -/
private theorem exists_echelon_transform {K : Type*} [Field K] {n : ℕ}
    (g : Fin n → K[X]) (hli : ∀ c : Fin n → K, (∑ j, C (c j) * g j) = 0 → c = 0)
    (b : ℕ) (hb : ∀ j, (g j).natDegree ≤ b)
    (k : ℕ) (_hk : k ≤ n)
    (hsuf_inj : ∀ j₁ j₂ : Fin n, k ≤ j₁.val → k ≤ j₂.val →
      (g j₁).natDegree = (g j₂).natDegree → j₁ = j₂) :
    ∃ M : Matrix (Fin n) (Fin n) K, M.det ≠ 0 ∧
      (∀ j, (∑ i, C (M i j) * g i) ≠ 0) ∧
      Function.Injective (fun j => (∑ i, C (M i j) * g i).natDegree) ∧
      (∀ j, (∑ i, C (M i j) * g i).natDegree ≤ b) ∧
      (∀ j : Fin n, k ≤ j.val → (∑ i, C (M i j) * g i).natDegree = (g j).natDegree) := by
  classical
  -- Strong induction on the prefix degree sum `∑ j, if j.val < k then (g j).natDegree + 1 else 0`.
  suffices hmain : ∀ S : ℕ, ∀ g : Fin n → K[X],
      (∑ j : Fin n, if j.val < k then (g j).natDegree + 1 else 0) = S →
      (∀ c : Fin n → K, (∑ j, C (c j) * g j) = 0 → c = 0) →
      (∀ j, (g j).natDegree ≤ b) →
      (∀ j₁ j₂ : Fin n, k ≤ j₁.val → k ≤ j₂.val →
        (g j₁).natDegree = (g j₂).natDegree → j₁ = j₂) →
      ∃ M : Matrix (Fin n) (Fin n) K, M.det ≠ 0 ∧
        (∀ j, (∑ i, C (M i j) * g i) ≠ 0) ∧
        Function.Injective (fun j => (∑ i, C (M i j) * g i).natDegree) ∧
        (∀ j, (∑ i, C (M i j) * g i).natDegree ≤ b) ∧
        (∀ j : Fin n, k ≤ j.val → (∑ i, C (M i j) * g i).natDegree = (g j).natDegree) from
    hmain _ g rfl hli hb hsuf_inj
  intro S
  induction S using Nat.strong_induction_on with
  | h S ih =>
    intro g hS hli hb hsuf_inj
    have hg_ne : ∀ j, g j ≠ 0 := fun j hj => by
      have h0 := hli (Pi.single j 1) (by
        rw [Finset.sum_eq_single j]
        · simp [hj]
        · intro i _ hij; simp [Pi.single_eq_of_ne hij]
        · intro h; exact absurd (mem_univ j) h)
      have := congrFun h0 j
      simp at this
    by_cases hinj : Function.Injective (fun j => (g j).natDegree)
    · refine ⟨1, by simp, ?_, ?_, ?_, ?_⟩
      · intro j
        have heq : (∑ i, C ((1 : Matrix (Fin n) (Fin n) K) i j) * g i) = g j := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro i _ hij; simp [Matrix.one_apply_ne hij]
          · intro h; exact absurd (mem_univ j) h
        rw [heq]; exact hg_ne j
      · intro j₁ j₂ h
        dsimp only at h
        have heq : ∀ j, (∑ i, C ((1 : Matrix (Fin n) (Fin n) K) i j) * g i) = g j := fun j => by
          rw [Finset.sum_eq_single j]
          · simp
          · intro i _ hij; simp [Matrix.one_apply_ne hij]
          · intro h; exact absurd (mem_univ j) h
        rw [heq j₁, heq j₂] at h
        exact hinj h
      · intro j
        have heq : (∑ i, C ((1 : Matrix (Fin n) (Fin n) K) i j) * g i) = g j := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro i _ hij; simp [Matrix.one_apply_ne hij]
          · intro h; exact absurd (mem_univ j) h
        rw [heq]; exact hb j
      · intro j _
        have heq : (∑ i, C ((1 : Matrix (Fin n) (Fin n) K) i j) * g i) = g j := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro i _ hij; simp [Matrix.one_apply_ne hij]
          · intro h; exact absurd (mem_univ j) h
        rw [heq]
    · unfold Function.Injective at hinj
      push Not at hinj
      obtain ⟨u₁, u₂, hdeg_eq, hne_u⟩ := hinj
      have hex : ∃ j₁ j₂ : Fin n, j₁ ≠ j₂ ∧ j₁.val < k ∧ (g j₁).natDegree = (g j₂).natDegree := by
        by_cases h1 : u₁.val < k
        · exact ⟨u₁, u₂, hne_u, h1, hdeg_eq⟩
        · by_cases h2 : u₂.val < k
          · exact ⟨u₂, u₁, hne_u.symm, h2, hdeg_eq.symm⟩
          · exact absurd (hsuf_inj u₁ u₂ (by omega) (by omega) hdeg_eq) hne_u
      obtain ⟨j₁, j₂, hjne, hj1_lt, hdeg_eq⟩ := hex
      set c : K := (g j₁).leadingCoeff / (g j₂).leadingCoeff
      -- Transvection `E = transvection j₂ j₁ (-c)` satisfies `∑ i, C (E i j) * g i = g j` for `j ≠ j₁`
      -- and `g j₁ - C c * g j₂` for `j = j₁`.
      let E : Matrix (Fin n) (Fin n) K := Matrix.transvection j₂ j₁ (-c)
      have hE_det : E.det = 1 := Matrix.det_transvection_of_ne j₂ j₁ hjne.symm (-c)
      let g' : Fin n → K[X] := fun j => ∑ i, C (E i j) * g i
      have hE_entry : ∀ i j : Fin n, E i j =
          (if i = j then (1 : K) else 0) + (if j₂ = i ∧ j₁ = j then -c else 0) := fun i j => by
        change ((1 : Matrix (Fin n) (Fin n) K) + Matrix.single j₂ j₁ (-c)) i j = _
        rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      have hg'_val : ∀ j, g' j = if j = j₁ then g j₁ - C c * g j₂ else g j := fun j => by
        dsimp only [g']
        simp_rw [hE_entry]
        by_cases hj : j = j₁
        · subst j
          have hsplit2 : ∀ i : Fin n,
              C ((if i = j₁ then (1 : K) else 0) + (if j₂ = i ∧ j₁ = j₁ then -c else 0)) * g i =
              (if i = j₁ then g j₁ else 0) + (if i = j₂ then -(C c * g j₂) else 0) := fun i => by
            by_cases h1 : i = j₁
            · subst i
              simp only [↓reduceIte, hjne.symm, false_and, add_zero, map_one, one_mul, hjne]
            · by_cases h2 : i = j₂
              · subst i
                simp only [h1, ↓reduceIte, and_self, zero_add, map_neg]
                ring
              · simp only [h1, h2, Ne.symm h2, false_and, ↓reduceIte, add_zero, map_zero, zero_mul]
          rw [Finset.sum_congr rfl (fun i _ => by convert hsplit2 i), Finset.sum_add_distrib]
          simp [sub_eq_add_neg]
        · simp only [hj, ↓reduceIte]
          rw [Finset.sum_eq_single j]
          · simp only [↓reduceIte, Ne.symm hj, and_false, add_zero, map_one, one_mul]
          · intro i _ hij
            simp only [hij, Ne.symm hj, and_false, ↓reduceIte, add_zero, map_zero, zero_mul]
          · intro h; exact absurd (mem_univ j) h
      have hli' : ∀ d : Fin n → K, (∑ j, C (d j) * g' j) = 0 → d = 0 := by
        intro d hd
        have hrew : ∑ j, C (d j) * g' j = ∑ i, C ((E.mulVec d) i) * g i := by
          simp_rw [g', Finset.mul_sum, ← mul_assoc, ← C_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_mul, ← map_sum]
          congr 2
          simp only [Matrix.mulVec, dotProduct]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
        rw [hrew] at hd
        have hEd := hli (E.mulVec d) hd
        have hinv : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E (by rw [hE_det]; exact isUnit_one)
        have : d = E⁻¹.mulVec (E.mulVec d) := by
          rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
        rw [this, hEd, Matrix.mulVec_zero]
      have hg'j1_ne : g' j₁ ≠ 0 := by
        intro hz
        have h0 := hli' (Pi.single j₁ 1) (by
          rw [Finset.sum_eq_single j₁]
          · simp [hz]
          · intro i _ hij; simp [Pi.single_eq_of_ne hij]
          · intro h; exact absurd (mem_univ j₁) h)
        have := congrFun h0 j₁
        simp at this
      have hdeg_lt : (g' j₁).natDegree < (g j₁).natDegree := by
        have hgj1 : g' j₁ = g j₁ - C c * g j₂ := by rw [hg'_val j₁]; simp
        have hle : (g' j₁).natDegree ≤ (g j₁).natDegree := by
          rw [hgj1]
          exact (natDegree_sub_le _ _).trans
            (max_le le_rfl ((natDegree_C_mul_le c (g j₂)).trans hdeg_eq.symm.le))
        have hcoeff0 : (g' j₁).coeff (g j₁).natDegree = 0 := by
          rw [hgj1, coeff_sub, coeff_C_mul, show (g j₁).coeff (g j₁).natDegree = (g j₁).leadingCoeff from rfl,
            hdeg_eq, show (g j₂).coeff (g j₂).natDegree = (g j₂).leadingCoeff from rfl,
            div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr (hg_ne j₂)), sub_self]
        refine lt_of_le_of_ne hle fun heq => ?_
        have hlc0 : (g' j₁).leadingCoeff = 0 := by rw [leadingCoeff, heq]; exact hcoeff0
        exact leadingCoeff_ne_zero.mpr hg'j1_ne hlc0
      have hb' : ∀ j, (g' j).natDegree ≤ b := fun j => by
        by_cases hj : j = j₁
        · subst j; exact hdeg_lt.le.trans (hb j₁)
        · rw [hg'_val j]; simp only [hj, ↓reduceIte]; exact hb j
      have hsuf_eq : ∀ j : Fin n, k ≤ j.val → g' j = g j := fun j hj => by
        rw [hg'_val j]; simp only [show j ≠ j₁ from fun h => by subst h; omega, ↓reduceIte]
      have hsuf_inj' : ∀ a₁ a₂ : Fin n, k ≤ a₁.val → k ≤ a₂.val →
          (g' a₁).natDegree = (g' a₂).natDegree → a₁ = a₂ := fun a₁ a₂ h1 h2 h => by
        rw [hsuf_eq a₁ h1, hsuf_eq a₂ h2] at h
        exact hsuf_inj a₁ a₂ h1 h2 h
      have hS' : (∑ j : Fin n, if j.val < k then (g' j).natDegree + 1 else 0) < S := by
        rw [← hS]
        refine Finset.sum_lt_sum (fun j _ => ?_) ⟨j₁, mem_univ j₁, ?_⟩
        · by_cases hjk : j.val < k
          · simp only [hjk, ↓reduceIte]
            by_cases hj : j = j₁
            · subst j; omega
            · rw [hg'_val j]; simp only [hj, ↓reduceIte]; exact le_rfl
          · simp [hjk]
        · simp only [hj1_lt, ↓reduceIte]; omega
      obtain ⟨M', hM'_det, hM'_ne, hM'_inj, hM'_le, hM'_suf⟩ := ih _ hS' g' rfl hli' hb' hsuf_inj'
      refine ⟨E * M', by rw [Matrix.det_mul, hE_det, one_mul]; exact hM'_det, ?_, ?_, ?_, ?_⟩
      all_goals
        have hcomp : ∀ j, (∑ i, C ((E * M') i j) * g i) = ∑ r, C (M' r j) * g' r := fun j => by
          simp_rw [g', Finset.mul_sum, ← mul_assoc, ← C_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_mul, ← map_sum]
          congr 2
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun r _ => mul_comm _ _
      · intro j; rw [hcomp j]; exact hM'_ne j
      · intro a₁ a₂ h; dsimp only at h; rw [hcomp a₁, hcomp a₂] at h; exact hM'_inj h
      · intro j; rw [hcomp j]; exact hM'_le j
      · intro j hj; rw [hcomp j, hM'_suf j hj, hsuf_eq j hj]

/-- Lift `P ↦ ∑ u ∈ A, c_u w_u P(u) (X + u)^N`. -/
private noncomputable def liftPoly (A : Finset (ZMod p)) (w : ZMod p → ℤ) (N : ℕ)
    (P : (ZMod p)[X]) : (ZMod p)[X] :=
  ∑ u ∈ A, C (Lagrange.nodalWeight A id u * (w u : ZMod p) * P.eval u) * (X + C u) ^ N

private theorem liftPoly_coeff (A : Finset (ZMod p)) (w : ZMod p → ℤ) (N r : ℕ)
    (P : (ZMod p)[X]) :
    (liftPoly A w N P).coeff r =
      (N.choose r : ZMod p) *
        ∑ u ∈ A, Lagrange.nodalWeight A id u * (w u : ZMod p) * P.eval u * u ^ (N - r) := by
  unfold liftPoly
  rw [finsetSum_coeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [coeff_C_mul, coeff_X_add_C_pow]
  ring

private theorem liftPoly_natDegree_le (A : Finset (ZMod p)) (w : ZMod p → ℤ) (N : ℕ)
    (P : (ZMod p)[X]) : (liftPoly A w N P).natDegree ≤ N := by
  unfold liftPoly
  refine natDegree_sum_le_of_forall_le _ _ fun u _ => ?_
  exact (natDegree_C_mul_le _ _).trans (by simp [natDegree_pow])

/-- `liftPoly` is injective on polynomials of degree `< A.card` when `A.card - 1 ≤ N < p` and
`w u ∈ {±1}` on `A`. -/
private theorem liftPoly_injective (_hp : p ≠ 2) (A : Finset (ZMod p)) (w : ZMod p → ℤ)
    (hw : ∀ u ∈ A, w u = 1 ∨ w u = -1) {N : ℕ} (hN_lo : A.card - 1 ≤ N) (hN_hi : N < p)
    {P : (ZMod p)[X]} (hP_deg : P.natDegree < A.card) (hzero : liftPoly A w N P = 0) :
    P = 0 := by
  classical
  -- For every `0 ≤ k < A.card`, coefficient `N - k` of `liftPoly A w N P` vanishes.
  have hmom : ∀ k < A.card,
      ∑ u ∈ A, (Lagrange.nodalWeight A id u * (w u : ZMod p) * P.eval u) * u ^ k = 0 := by
    intro k hk
    have hcoeff : (liftPoly A w N P).coeff (N - k) = 0 := by rw [hzero, coeff_zero]
    rw [liftPoly_coeff, Nat.sub_sub_self (by omega : k ≤ N)] at hcoeff
    exact (mul_eq_zero.mp hcoeff).resolve_left (choose_ne_zero_zmod hN_hi (Nat.sub_le N k))
  -- Vandermonde on `e : Fin A.card ≃ A`:
  let e : Fin A.card ≃ A := A.equivFin.symm
  let V : Matrix (Fin A.card) (Fin A.card) (ZMod p) :=
    (Matrix.vandermonde fun j => (e j).1)ᵀ
  let vec : Fin A.card → ZMod p :=
    fun j => Lagrange.nodalWeight A id (e j).1 * (w (e j).1 : ZMod p) * P.eval (e j).1
  have hVvec : V.mulVec vec = 0 := by
    ext k
    simp only [Matrix.mulVec, dotProduct, V, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Pi.zero_apply]
    have hsum := hmom k.val k.isLt
    rw [← A.sum_attach, Finset.attach_eq_univ, ← e.sum_comp] at hsum
    simpa only [vec, mul_comm] using hsum
  have hV_det : V.det ≠ 0 := by
    rw [Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hvec0 : vec = 0 := by
    have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.mpr hV_det)
    calc vec = (1 : Matrix _ _ _).mulVec vec := (Matrix.one_mulVec vec).symm
      _ = (V⁻¹ * V).mulVec vec := by rw [hinv]
      _ = V⁻¹.mulVec (V.mulVec vec) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hVvec, Matrix.mulVec_zero]
  have heval0 : ∀ u ∈ A, P.eval u = 0 := by
    intro u hu
    have h := congrFun hvec0 (e.symm ⟨u, hu⟩)
    simp only [vec, Equiv.apply_symm_apply, Pi.zero_apply] at h
    have hw_ne : (w u : ZMod p) ≠ 0 := by
      rcases hw u hu with h1 | h1 <;> rw [h1]
      · simp
      · simp
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (nodalWeight_ne_zero A hu) hw_ne)
  by_contra hP_ne
  have hcard : A.card ≤ P.roots.card := by
    have hsub : A.val ⊆ P.roots := by
      rw [Multiset.subset_iff]
      intro u hu
      exact (mem_roots hP_ne).mpr (heval0 u hu)
    exact Multiset.card_le_card ((Multiset.le_iff_subset A.nodup).mpr hsub)
  have hle := Polynomial.card_roots' P
  omega

/-- Reversing columns and applying the unit-diagonal upper-triangular transform turns
`normalizedHankel (signedPowerSum A A w D) D h` into `normWronskian (D - h) (liftPoly (X^j))`
up to a `±1` sign. -/
private theorem det_signedHankel_eq_pm_wronskian (A : Finset (ZMod p)) (w : ZMod p → ℤ)
    {D h : ℕ} (h2h : 2 * h ≤ D) (hD : D < p) :
    ∃ ε : (ZMod p)[X], (ε = 1 ∨ ε = -1) ∧
      (normWronskian (D - h) (fun j : Fin (h + 1) => liftPoly A w (D - h) (X ^ j.val))).det =
        ε * (normalizedHankel (signedPowerSum A A w D) D h).det := by
  classical
  let N := D - h
  have hN_lt : N < p := by dsimp [N]; omega
  let J := normalizedHankel (signedPowerSum A A w D) D h
  have hJ_entry : ∀ i j : Fin (h + 1),
      J i j = ∑ u ∈ A, C (Lagrange.nodalWeight A id u * (w u : ZMod p)) *
        (X + C u) ^ (D - (i.val + j.val)) := by
    intro i j
    let k := i.val + j.val
    have hk : k ≤ D := by dsimp [k]; omega
    have hdk : (D.descFactorial k : ZMod p) ≠ 0 := descFactorial_ne_zero_zmod hD hk
    change C ((D.descFactorial k : ZMod p)⁻¹) * derivative^[k] (signedPowerSum A A w D) = _
    unfold signedPowerSum
    rw [iterate_derivative_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [iterate_derivative_C_mul, iterate_derivative_X_add_pow, nsmul_eq_mul, ← C_eq_natCast]
    calc C ((D.descFactorial k : ZMod p)⁻¹) *
            (C (Lagrange.nodalWeight A id u * (w u : ZMod p)) *
              (C (D.descFactorial k : ZMod p) * (X + C u) ^ (D - k)))
        = C (Lagrange.nodalWeight A id u * (w u : ZMod p)) *
            (C ((D.descFactorial k : ZMod p)⁻¹) * C (D.descFactorial k : ZMod p)) *
            (X + C u) ^ (D - k) := by ring
      _ = C (Lagrange.nodalWeight A id u * (w u : ZMod p)) * (X + C u) ^ (D - k) := by
            rw [← C_mul, inv_mul_cancel₀ hdk, C_1, mul_one]
  -- Reversed columns `J_rev i k = J i (Fin.rev k)`:
  let J_rev : Matrix (Fin (h + 1)) (Fin (h + 1)) (ZMod p)[X] :=
    J.submatrix id Fin.revPerm
  have hJ_rev_det : J_rev.det = ((Equiv.Perm.sign (Fin.revPerm (n := h + 1)) : ℤ) : (ZMod p)[X]) * J.det := by
    change (J.submatrix id Fin.revPerm).det = _
    rw [Matrix.det_permute']
  -- Upper-triangular unit-diagonal matrix `T k m = C (m.choose k) * (-X)^(m - k)` for `k ≤ m`:
  let T : Matrix (Fin (h + 1)) (Fin (h + 1)) (ZMod p)[X] := fun k m =>
    if k.val ≤ m.val then C ((m.val.choose k.val : ℕ) : ZMod p) * (-X) ^ (m.val - k.val) else 0
  have hT_upper : T.IsUpperTriangular := by
    intro i j hij
    dsimp [T]
    have hlt : j.val < i.val := hij
    simp [not_le.mpr hlt]
  have hT_det : T.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hT_upper]
    refine Finset.prod_eq_one fun i _ => ?_
    simp [T]
  -- Product `J_rev * T` equals `normWronskian N (fun j => liftPoly A w N (X^j))`:
  have hprod : J_rev * T =
      normWronskian N (fun j : Fin (h + 1) => liftPoly A w N (X ^ j.val)) := by
    ext i m : 1
    -- Evaluate RHS:
    have hrhs : normWronskian N (fun j : Fin (h + 1) => liftPoly A w N (X ^ j.val)) i m =
        ∑ u ∈ A, C (Lagrange.nodalWeight A id u * (w u : ZMod p) * u ^ m.val) *
          (X + C u) ^ (N - i.val) := by
      unfold normWronskian liftPoly
      have hni : (N.descFactorial i.val : ZMod p) ≠ 0 :=
        descFactorial_ne_zero_zmod hN_lt (by dsimp [N]; omega)
      rw [iterate_derivative_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [iterate_derivative_C_mul, iterate_derivative_X_add_pow, nsmul_eq_mul, ← C_eq_natCast,
        eval_pow, eval_X]
      calc C ((N.descFactorial i.val : ZMod p)⁻¹) *
              (C (Lagrange.nodalWeight A id u * (w u : ZMod p) * u ^ m.val) *
                (C (N.descFactorial i.val : ZMod p) * (X + C u) ^ (N - i.val)))
          = C (Lagrange.nodalWeight A id u * (w u : ZMod p) * u ^ m.val) *
              (C ((N.descFactorial i.val : ZMod p)⁻¹) * C (N.descFactorial i.val : ZMod p)) *
              (X + C u) ^ (N - i.val) := by ring
        _ = _ := by rw [← C_mul, inv_mul_cancel₀ hni, C_1, mul_one]
    rw [hrhs, Matrix.mul_apply]
    have hstep : ∀ k : Fin (h + 1),
        J_rev i k * T k m = ∑ u ∈ A,
          C (Lagrange.nodalWeight A id u * (w u : ZMod p)) * (X + C u) ^ (N - i.val) *
            (if k.val ≤ m.val then
              (X + C u) ^ k.val * (-X) ^ (m.val - k.val) * C ((m.val.choose k.val : ℕ) : ZMod p)
             else 0) := by
      intro k
      change J i k.rev * T k m = _
      rw [hJ_entry i k.rev, Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hexp : D - (i.val + k.rev.val) = (N - i.val) + k.val := by
        have hk : k.rev.val = h - k.val := by simp [Fin.val_rev]
        dsimp [N]; omega
      rw [hexp, pow_add]
      dsimp [T]
      split_ifs <;> ring
    calc ∑ k : Fin (h + 1), J_rev i k * T k m
        = ∑ k : Fin (h + 1), ∑ u ∈ A,
            C (Lagrange.nodalWeight A id u * (w u : ZMod p)) * (X + C u) ^ (N - i.val) *
              (if k.val ≤ m.val then
                (X + C u) ^ k.val * (-X) ^ (m.val - k.val) * C ((m.val.choose k.val : ℕ) : ZMod p)
               else 0) := Finset.sum_congr rfl fun k _ => hstep k
      _ = ∑ u ∈ A, ∑ k : Fin (h + 1),
            C (Lagrange.nodalWeight A id u * (w u : ZMod p)) * (X + C u) ^ (N - i.val) *
              (if k.val ≤ m.val then
                (X + C u) ^ k.val * (-X) ^ (m.val - k.val) * C ((m.val.choose k.val : ℕ) : ZMod p)
               else 0) := Finset.sum_comm
      _ = ∑ u ∈ A, C (Lagrange.nodalWeight A id u * (w u : ZMod p) * u ^ m.val) *
            (X + C u) ^ (N - i.val) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← Finset.mul_sum]
          have hbin : (∑ k : Fin (h + 1),
              if k.val ≤ m.val then
                (X + C u) ^ k.val * (-X) ^ (m.val - k.val) * C ((m.val.choose k.val : ℕ) : ZMod p)
              else 0) = C (u ^ m.val) := by
            have h1 : (∑ k : Fin (h + 1),
                if k.val ≤ m.val then
                  (X + C u) ^ k.val * (-X) ^ (m.val - k.val) * C ((m.val.choose k.val : ℕ) : ZMod p)
                else 0) =
                ∑ k ∈ range (m.val + 1),
                  (X + C u) ^ k * (-X) ^ (m.val - k) * ((m.val.choose k : ℕ) : (ZMod p)[X]) := by
              rw [Fin.sum_univ_eq_sum_range (fun k => if k ≤ m.val then
                (X + C u) ^ k * (-X) ^ (m.val - k) * C ((m.val.choose k : ℕ) : ZMod p) else 0) (h + 1)]
              rw [← Finset.sum_filter]
              have hfilt : (range (h + 1)).filter (fun k => k ≤ m.val) = range (m.val + 1) := by
                ext k; simp only [mem_filter, mem_range]; omega
              rw [hfilt]
              refine Finset.sum_congr rfl fun k _ => ?_
              simp
            rw [h1, ← add_pow, show (X + C u) + (-X) = C u by ring, ← map_pow]
          rw [hbin]
          calc C (Lagrange.nodalWeight A id u * (w u : ZMod p)) * (X + C u) ^ (N - i.val) * C (u ^ m.val)
              = (C (Lagrange.nodalWeight A id u * (w u : ZMod p)) * C (u ^ m.val)) *
                  (X + C u) ^ (N - i.val) := by ring
            _ = _ := by rw [← C_mul]
  refine ⟨((Equiv.Perm.sign (Fin.revPerm (n := h + 1)) : ℤ) : (ZMod p)[X]), ?_, ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm (n := h + 1))) with hs | hs <;>
      simp [hs]
  · rw [← hprod, Matrix.det_mul, hT_det, mul_one, hJ_rev_det]

/-- **Core Wronskian nonvanishing & sharp minority-corrected degree theorem**:
For arbitrary site signs `w u ∈ {±1}` on `A` (`2 ≤ |A| ≤ p/2 + 1`) and `2(h+1) ≤ |A|`:
`signedDet A w h ≠ 0` and `(signedDet A w h).natDegree ≤ D_{h+1}`. -/
theorem signedDet_ne_zero_and_natDegree_le (hp : p ≠ 2) (A : Finset (ZMod p)) (w : ZMod p → ℤ)
    (hw : ∀ u ∈ A, w u = 1 ∨ w u = -1)
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p / 2 + 1) {h : ℕ} (hh : 2 * (h + 1) ≤ A.card) :
    signedDet A w h ≠ 0 ∧
      (signedDet A w h).natDegree ≤ degreeBudget (p / 2) A.card (h + 1) (minorityCount A w) := by
  classical
  let d := p / 2
  let a := A.card
  let x := h + 1
  let D := d + (a - 2)
  let N := D - h
  let s := minorityCount A w
  obtain ⟨v, hv⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  have hd_eq : d = v := by dsimp [d]; omega
  have hD_lt : D < p := by dsimp [D, d, a]; omega
  have h2h_le : 2 * h ≤ D := by dsimp [D, d, a]; omega
  have hN_lo : a - 1 ≤ N := by dsimp [N, D, d, a]; omega
  have hN_hi : N < p := by dsimp [N]; omega
  have hN_eq : N = d + a - 1 - x := by dsimp [N, D, d, a, x]; omega
  obtain ⟨ε, hε, hdet_eq⟩ := det_signedHankel_eq_pm_wronskian A w h2h_le hD_lt
  -- Helper: transforming monomials by any invertible scalar matrix `M` multiplies `det` by `C M.det`.
  have htrans : ∀ (M : Matrix (Fin x) (Fin x) (ZMod p)),
      normWronskian N (fun j : Fin x => ∑ i : Fin x, C (M i j) * liftPoly A w N (X ^ i.val)) =
        normWronskian N (fun i : Fin x => liftPoly A w N (X ^ i.val)) * M.map C := by
    intro M
    ext i j : 1
    rw [Matrix.mul_apply]
    dsimp only [normWronskian, Matrix.map_apply]
    rw [iterate_derivative_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [iterate_derivative_C_mul]
    ring
  -- Linear independence of `i ↦ liftPoly A w N (X^i)`:
  have hli_mono : ∀ c : Fin x → ZMod p,
      (∑ i : Fin x, C (c i) * liftPoly A w N (X ^ i.val)) = 0 → c = 0 := by
    intro c hc
    let P : (ZMod p)[X] := ∑ i : Fin x, C (c i) * X ^ i.val
    have hP_deg : P.natDegree < a := by
      refine (natDegree_sum_le_of_forall_le (n := x - 1) univ _ fun i _ => ?_).trans_lt ?_
      · exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; exact Nat.le_pred_of_lt i.isLt)
      · dsimp [x, a]; omega
    have hliftP : liftPoly A w N P = ∑ i : Fin x, C (c i) * liftPoly A w N (X ^ i.val) := by
      unfold liftPoly
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp_rw [← mul_assoc, ← C_mul]
      rw [← Finset.sum_mul, ← map_sum]
      congr 2
      dsimp [P]
      rw [eval_finsetSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      ring
    have hP0 : P = 0 := liftPoly_injective hp A w hw hN_lo hN_hi hP_deg (hliftP.trans hc)
    funext i
    have hcoeff : P.coeff i.val = 0 := by rw [hP0, coeff_zero]
    rw [show P.coeff i.val = c i by
      dsimp [P]
      rw [finsetSum_coeff, Finset.sum_eq_single i]
      · simp
      · intro r _ hri
        rw [coeff_C_mul, coeff_X_pow]
        simp [show i.val ≠ r.val from fun h => hri (Fin.ext h.symm)]
      · intro h; exact absurd (mem_univ i) h] at hcoeff
    exact hcoeff
  -- Conclude via a helper: given any invertible `M` producing distinct degrees `l j ≤ N` with
  -- `2 * (∑ l j) - x*(x-1) ≤ 2 * B`, we get `signedDet ≠ 0` and `natDegree ≤ B`!
  have hconclude : ∀ (M : Matrix (Fin x) (Fin x) (ZMod p)) (B : ℕ), M.det ≠ 0 →
      (∀ j, (∑ i, C (M i j) * liftPoly A w N (X ^ i.val)) ≠ 0) →
      Function.Injective (fun j => (∑ i, C (M i j) * liftPoly A w N (X ^ i.val)).natDegree) →
      (∀ j, (∑ i, C (M i j) * liftPoly A w N (X ^ i.val)).natDegree ≤ N) →
      (∑ j, (∑ i, C (M i j) * liftPoly A w N (X ^ i.val)).natDegree) - x * (x - 1) / 2 ≤ B →
      signedDet A w h ≠ 0 ∧ (signedDet A w h).natDegree ≤ B := by
    intro M B hM_det hne hinj hle hB
    let g' : Fin x → (ZMod p)[X] := fun j => ∑ i, C (M i j) * liftPoly A w N (X ^ i.val)
    obtain ⟨hW_ne, hW_deg⟩ := normWronskian_det_ne_zero_and_deg N hN_hi (by omega) g' hne hle hinj
    have hdet_map : (M.map C).det = C M.det := (RingHom.map_det C M).symm
    have hdet_rel : (normWronskian N g').det = ε * C M.det * signedDet A w h := by
      change (normWronskian N g').det = ε * C M.det *
        (normalizedHankel (signedPowerSum A A w D) D h).det
      rw [htrans M, Matrix.det_mul, hdet_map, hdet_eq]
      ring
    have hε_ne : ε ≠ 0 := by rcases hε with rfl | rfl <;> simp
    have hC_ne : C M.det ≠ 0 := C_ne_zero.mpr hM_det
    have hsd_ne : signedDet A w h ≠ 0 := fun hz => hW_ne (by rw [hdet_rel, hz, mul_zero])
    have hε_deg : ε.natDegree = 0 := by rcases hε with rfl | rfl <;> simp
    have hdeg_eq : (normWronskian N g').det.natDegree = (signedDet A w h).natDegree := by
      rw [hdet_rel, natDegree_mul (mul_ne_zero hε_ne hC_ne) hsd_ne,
        natDegree_mul hε_ne hC_ne, hε_deg, natDegree_C, zero_add, zero_add]
    exact ⟨hsd_ne, hdeg_eq ▸ hW_deg ▸ hB⟩
  -- Case split on `x ≤ s` vs `s < x`:
  by_cases hxs : x ≤ s
  · -- `s ≥ x`: `(x - s) = 0`, so `degreeBudget = x * (d + a - 2*x)`.
    obtain ⟨M, hM_det, hne, hinj, hle, _⟩ :=
      exists_echelon_transform (fun i : Fin x => liftPoly A w N (X ^ i.val)) hli_mono N
        (fun i => liftPoly_natDegree_le A w N _) x le_rfl (fun _ _ h _ => by omega)
    refine hconclude M (degreeBudget d a x s) hM_det hne hinj hle ?_
    have hup := twice_sum_distinct_le _ hinj hle
    have hzero_sub : x - s = 0 := by omega
    unfold degreeBudget
    rw [hzero_sub, zero_mul, Nat.sub_zero]
    have hsum_even : 2 ∣ x * (x - 1) := by
      obtain ⟨t, ht⟩ := Nat.even_mul_pred_self x
      exact ⟨t, by omega⟩
    have hmul2 : x * (x - 1) / 2 * 2 = x * (x - 1) := Nat.div_mul_cancel hsum_even
    have hcalc : x * (N + 1 - x) = x * (d + a - 2 * x) := by congr 1; omega
    rw [← hcalc]
    have hmul_sub : x * (N + 1 - x) + x * (x - 1) = x * N := by
      rw [← Nat.mul_add]; congr 1; omega
    have h2N : 2 * x * N = 2 * (x * N) := by ring
    omega
  · -- `s < x`: pick minority sign `-σ` so `MinSet = {u ∈ A | w u = -σ}` has size `s`.
    have hs_lt : s < x := by omega
    have hpart : (A.filter fun u => w u = 1).card + (A.filter fun u => w u = -1).card = a := by
      have hdisj : Disjoint (A.filter fun u => w u = 1) (A.filter fun u => w u = -1) := by
        rw [Finset.disjoint_filter]; intro u _ h1 h2; omega
      have hunion : (A.filter fun u => w u = 1) ∪ (A.filter fun u => w u = -1) = A := by
        ext u; simp only [mem_union, mem_filter]
        exact ⟨fun h => h.elim And.left And.left, fun hu => (hw u hu).imp (And.intro hu) (And.intro hu)⟩
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hex_min : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧
        (A.filter fun u => w u = -σ).card = s := by
      by_cases hle : (A.filter fun u => w u = 1).card ≤ (A.filter fun u => w u = -1).card
      · exact ⟨-1, Or.inr rfl, by simp [s, minorityCount, min_eq_left hle]⟩
      · exact ⟨1, Or.inl rfl, by simp [s, minorityCount, min_eq_right (le_of_not_ge hle)]⟩
    obtain ⟨σ, hσ, hMin_card⟩ := hex_min
    let MinSet := A.filter fun u => w u = -σ
    let prodMin : (ZMod p)[X] := ∏ u ∈ MinSet, (X - C u)
    have hprodMin_monic : prodMin.Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
    have hprodMin_deg : prodMin.natDegree = s := by
      dsimp [prodMin]
      rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
      simpa using hMin_card
    -- Basis polynomials `Q j` of exact degree `j.val`, monic:
    let Q : Fin x → (ZMod p)[X] := fun j =>
      if j.val < s then X ^ j.val else X ^ (j.val - s) * prodMin
    have hQ_monic : ∀ j : Fin x, (Q j).Monic := fun j => by
      dsimp [Q]; split_ifs
      · exact monic_X_pow _
      · exact (monic_X_pow _).mul hprodMin_monic
    have hQ_deg : ∀ j : Fin x, (Q j).natDegree = j.val := fun j => by
      dsimp [Q]; split_ifs with hjs
      · exact natDegree_X_pow _
      · rw [Polynomial.Monic.natDegree_mul (monic_X_pow _) hprodMin_monic, natDegree_X_pow,
          hprodMin_deg]; omega
    -- Coefficient matrix `C_Q` is upper triangular with `1`s on diagonal (`det = 1`):
    let C_Q : Matrix (Fin x) (Fin x) (ZMod p) := Matrix.of fun i j => (Q j).coeff i.val
    have hCQ_upper : C_Q.IsUpperTriangular :=
      Matrix.matrixOfPolynomials_isUpperTriangular Q fun j => (hQ_deg j).le
    have hCQ_det : C_Q.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular hCQ_upper]
      refine Finset.prod_eq_one fun j _ => ?_
      change (Q j).coeff j.val = 1
      rw [← hQ_deg j]
      exact (hQ_monic j).leadingCoeff
    -- `g_Q j := liftPoly A w N (Q j) = ∑ i, C (C_Q i j) * liftPoly A w N (X^i)`:
    let g_Q : Fin x → (ZMod p)[X] := fun j => liftPoly A w N (Q j)
    have hgQ_eq : ∀ j : Fin x, g_Q j = ∑ i : Fin x, C (C_Q i j) * liftPoly A w N (X ^ i.val) := by
      intro j
      have hQ_sum : Q j = ∑ i : Fin x, C (C_Q i j) * X ^ i.val := by
        rw [Polynomial.as_sum_range' (Q j) x (by rw [hQ_deg j]; exact j.isLt),
          ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [C_Q, ← Polynomial.C_mul_X_pow_eq_monomial]
      dsimp [g_Q]
      unfold liftPoly
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp_rw [← mul_assoc, ← C_mul]
      rw [← Finset.sum_mul, ← map_sum]
      congr 2
      conv_lhs => rw [hQ_sum]
      rw [eval_finsetSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      ring
    -- Exact degree of `g_Q j` for `s ≤ j.val`: `N - (a - 1) + j.val`!
    have hgQ_suf_deg : ∀ j : Fin x, s ≤ j.val → (g_Q j).natDegree = N - (a - 1) + j.val := by
      intro j hjs
      have hQ_sign : ∀ u ∈ A, (w u : ZMod p) * (Q j).eval u = (σ : ZMod p) * (Q j).eval u := by
        intro u hu
        by_cases hm : u ∈ MinSet
        · have hev0 : prodMin.eval u = 0 := by
            dsimp [prodMin]
            rw [eval_prod]
            exact Finset.prod_eq_zero hm (by simp)
          have hQj0 : (Q j).eval u = 0 := by
            dsimp [Q]; simp only [not_lt.mpr hjs, ↓reduceIte, eval_mul, hev0, mul_zero]
          rw [hQj0, mul_zero, mul_zero]
        · have hwu : w u = σ := by
            simp only [MinSet, mem_filter, not_and] at hm
            rcases hw u hu with h1 | h1 <;> rcases hσ with rfl | rfl <;>
              first | exact h1 | exact absurd h1 (hm hu)
          rw [hwu]
      have hcoeff_val : ∀ r : ℕ, r ≤ N → N - (a - 1) + j.val ≤ r →
          (g_Q j).coeff r = if r = N - (a - 1) + j.val then
            (N.choose r : ZMod p) * (σ : ZMod p) else 0 := by
        intro r hrN hr_ge
        dsimp [g_Q]
        rw [liftPoly_coeff]
        have hP_eval : ∑ u ∈ A, Lagrange.nodalWeight A id u * (w u : ZMod p) *
              (Q j).eval u * u ^ (N - r) =
            (σ : ZMod p) * ∑ u ∈ A, Lagrange.nodalWeight A id u * (Q j * X ^ (N - r)).eval u := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u hu => ?_
          rw [eval_mul, eval_pow, eval_X]
          calc Lagrange.nodalWeight A id u * (w u : ZMod p) * (Q j).eval u * u ^ (N - r)
              = Lagrange.nodalWeight A id u * ((w u : ZMod p) * (Q j).eval u) * u ^ (N - r) := by ring
            _ = Lagrange.nodalWeight A id u * ((σ : ZMod p) * (Q j).eval u) * u ^ (N - r) := by
                  rw [hQ_sign u hu]
            _ = _ := by ring
        rw [hP_eval]
        have hmon : (Q j * X ^ (N - r)).Monic := (hQ_monic j).mul (monic_X_pow _)
        have hdeg_prod : (Q j * X ^ (N - r)).natDegree = j.val + (N - r) := by
          rw [Polynomial.Monic.natDegree_mul (hQ_monic j) (monic_X_pow _), hQ_deg j,
            natDegree_X_pow]
        have hlt_a : (Q j * X ^ (N - r)).natDegree < a := by rw [hdeg_prod]; omega
        rw [nodalWeight_eval_sum A _ hlt_a]
        split_ifs with heq
        · have hd_eq' : (Q j * X ^ (N - r)).natDegree = a - 1 := by rw [hdeg_prod]; omega
          rw [← hd_eq', ← leadingCoeff, hmon.leadingCoeff, mul_one]
        · have hlt' : (Q j * X ^ (N - r)).natDegree < a - 1 := by rw [hdeg_prod]; omega
          rw [coeff_eq_zero_of_natDegree_lt hlt', mul_zero, mul_zero]
      have htop_ne : (g_Q j).coeff (N - (a - 1) + j.val) ≠ 0 := by
        rw [hcoeff_val _ (by have := j.isLt; omega) le_rfl]; simp only [↓reduceIte]
        have hσ_ne : (σ : ZMod p) ≠ 0 := by rcases hσ with rfl | rfl <;> simp
        exact mul_ne_zero (choose_ne_zero_zmod hN_hi (by have := j.isLt; omega)) hσ_ne
      refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr ?_) htop_ne
      intro r hr
      by_cases hrN : r ≤ N
      · rw [hcoeff_val r hrN hr.le]; simp [ne_of_gt hr]
      · exact coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (liftPoly_natDegree_le A w N (Q j)) (by omega))
    -- Linear independence of `g_Q` follows from `C_Q.det = 1`:
    have hli_Q : ∀ c : Fin x → ZMod p, (∑ j : Fin x, C (c j) * g_Q j) = 0 → c = 0 := by
      intro c hc
      have hrew : ∑ j : Fin x, C (c j) * g_Q j =
          ∑ i : Fin x, C ((C_Q.mulVec c) i) * liftPoly A w N (X ^ i.val) := by
        simp_rw [hgQ_eq, Finset.mul_sum, ← mul_assoc, ← C_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul, ← map_sum]
        congr 2
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [hrew] at hc
      have hCc := hli_mono (C_Q.mulVec c) hc
      have hinv : C_Q⁻¹ * C_Q = 1 := Matrix.nonsing_inv_mul C_Q (by rw [hCQ_det]; exact isUnit_one)
      calc c = (1 : Matrix _ _ _).mulVec c := (Matrix.one_mulVec c).symm
        _ = (C_Q⁻¹ * C_Q).mulVec c := by rw [hinv]
        _ = C_Q⁻¹.mulVec (C_Q.mulVec c) := (Matrix.mulVec_mulVec _ _ _).symm
        _ = 0 := by rw [hCc, Matrix.mulVec_zero]
    -- Apply echelon reduction preserving the suffix `s ≤ j.val`!
    obtain ⟨E, hE_det, hE_ne, hE_inj, hE_le, hE_suf⟩ :=
      exists_echelon_transform g_Q hli_Q N (fun j => liftPoly_natDegree_le A w N (Q j))
        s hs_lt.le (fun j₁ j₂ h1 h2 heq => by
          rw [hgQ_suf_deg j₁ h1, hgQ_suf_deg j₂ h2] at heq
          exact Fin.ext (by omega))
    -- Composite transform `C_Q * E` transforms monomial lifts to the echelon basis!
    let M : Matrix (Fin x) (Fin x) (ZMod p) := C_Q * E
    have hM_det : M.det ≠ 0 := by rw [Matrix.det_mul, hCQ_det, one_mul]; exact hE_det
    have hM_comp : ∀ j : Fin x,
        (∑ i : Fin x, C (M i j) * liftPoly A w N (X ^ i.val)) = ∑ r : Fin x, C (E r j) * g_Q r := by
      intro j
      simp_rw [hgQ_eq, Finset.mul_sum, ← mul_assoc, ← C_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_mul, ← map_sum]
      congr 2
      dsimp [M]
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun r _ => mul_comm _ _
    refine hconclude M (degreeBudget d a x s) hM_det
      (fun j => by rw [hM_comp j]; exact hE_ne j)
      (fun j₁ j₂ h => by dsimp only at h; rw [hM_comp j₁, hM_comp j₂] at h; exact hE_inj h)
      (fun j => by rw [hM_comp j]; exact hE_le j) ?_
    -- Bound the sum of distinct degrees: prefix `< s` has `s` distinct values `≤ N`, suffix `≥ s` is exact!
    let l : Fin x → ℕ := fun j => (∑ i : Fin x, C (M i j) * liftPoly A w N (X ^ i.val)).natDegree
    have hl_inj : Function.Injective l := fun j₁ j₂ h => by
      dsimp [l] at h; rw [hM_comp j₁, hM_comp j₂] at h; exact hE_inj h
    have hl_le : ∀ j, l j ≤ N := fun j => by dsimp [l]; rw [hM_comp j]; exact hE_le j
    have hl_suf : ∀ j : Fin x, s ≤ j.val → l j = N - (a - 1) + j.val := fun j hj => by
      dsimp [l]; rw [hM_comp j, hE_suf j hj, hgQ_suf_deg j hj]
    -- Split `∑ j : Fin x, l j` into `j.val < s` and `s ≤ j.val`:
    let l_pre : Fin s → ℕ := fun j => l ⟨j.val, by omega⟩
    have hpre_inj : Function.Injective l_pre := fun i j hij =>
      Fin.ext (congrArg (Fin.val : Fin x → ℕ) (hl_inj hij))
    have hpre_bound := twice_sum_distinct_le l_pre hpre_inj fun j => hl_le _
    have hsplit : ∑ j : Fin x, l j =
        (∑ j : Fin s, l_pre j) + ∑ j ∈ (range x).filter (fun r => s ≤ r), (N - (a - 1) + j) := by
      have h0 : ∑ j : Fin x, l j = ∑ r ∈ range x, if hr : r < x then l ⟨r, hr⟩ else 0 := by
        rw [← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun j _ => by simp [j.isLt]
      rw [h0, ← Finset.sum_filter_add_sum_filter_not (range x) (fun r => r < s)]
      congr 1
      · have hfilt : (range x).filter (fun r => r < s) = range s := by
          ext r; simp only [mem_filter, mem_range]; omega
        rw [hfilt, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [l_pre, show j.val < x by omega, ↓reduceDIte]
      · have hfilt : (range x).filter (fun r => ¬ r < s) = (range x).filter (fun r => s ≤ r) := by
          ext r; simp only [mem_filter, not_lt]
        rw [hfilt]
        refine Finset.sum_congr rfl fun r hr => ?_
        obtain ⟨hrx, hrs⟩ := mem_filter.mp hr
        rw [mem_range] at hrx
        simp only [hrx, ↓reduceDIte]
        exact hl_suf ⟨r, hrx⟩ hrs
    -- Exact sum of `∑_{r = s}^{x-1} (N - (a - 1) + r)`:
    have hsuf_sum : 2 * (∑ r ∈ (range x).filter (fun r => s ≤ r), (N - (a - 1) + r)) =
        2 * (x - s) * (N - (a - 1)) + (x - s) * (s + x - 1) := by
      have hfilt : (range x).filter (fun r => s ≤ r) = (range (x - s)).map
          ⟨fun t => s + t, add_right_injective s⟩ := by
        ext r; simp only [mem_filter, mem_range, mem_map, Function.Embedding.coeFn_mk]
        exact ⟨fun ⟨h1, h2⟩ => ⟨r - s, by omega, by omega⟩, fun ⟨t, ht, h⟩ => by omega⟩
      rw [hfilt, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk]
      have hrew : ∑ t ∈ range (x - s), (N - (a - 1) + (s + t)) =
          ∑ t ∈ range (x - s), ((N - (a - 1) + s) + t) :=
        Finset.sum_congr rfl fun t _ => by omega
      rw [hrew, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
      have hid := sum_range_id_mul_two (x - s)
      have : 2 * ((x - s) * (N - (a - 1) + s) + ∑ t ∈ range (x - s), t) =
          2 * (x - s) * (N - (a - 1)) + (x - s) * (2 * s + (x - s - 1)) := by
        have hmul : 2 * ∑ t ∈ range (x - s), t = (x - s) * (x - s - 1) := by linarith
        nlinarith
      rw [this]
      congr 2; omega
    -- Now combine via `ℤ` arithmetic (avoids all `ℕ` subtraction headaches!):
    have hsum_even : 2 ∣ x * (x - 1) := by
      obtain ⟨t, ht⟩ := Nat.even_mul_pred_self x
      exact ⟨t, by omega⟩
    have hmul2 : x * (x - 1) / 2 * 2 = x * (x - 1) := Nat.div_mul_cancel hsum_even
    have hge_tri : x * (x - 1) ≤ 2 * ∑ j : Fin x, l j := twice_sum_distinct_ge l hl_inj
    have hbudget_le : (x - s) * (a - x - s) ≤ x * (d + a - 2 * x) := by
      have h1 : x - s ≤ x := Nat.sub_le _ _
      have h2 : a - x - s ≤ d + a - 2 * x := by omega
      exact Nat.mul_le_mul h1 h2
    -- Pass cleanly to `ℤ`!
    have hpreZ : 2 * (∑ j : Fin s, (l_pre j : ℤ)) + (s : ℤ) * ((s : ℤ) - 1) ≤ 2 * (s : ℤ) * (N : ℤ) := by
      rcases Nat.eq_zero_or_pos s with hs0 | hs_pos
      · have h0 : ∑ j : Fin s, (l_pre j : ℤ) = 0 :=
          Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
        rw [h0, hs0]; simp
      · have hcast : ((2 * ∑ j : Fin s, l_pre j + s * (s - 1) : ℕ) : ℤ) ≤ ((2 * s * N : ℕ) : ℤ) := by
          exact_mod_cast hpre_bound
        push_cast [Nat.cast_sub hs_pos] at hcast
        exact hcast
    have hsufZ : 2 * (∑ r ∈ (range x).filter (fun r => s ≤ r), ((N - (a - 1) + r : ℕ) : ℤ)) =
        2 * ((x : ℤ) - s) * ((N : ℤ) - ((a : ℤ) - 1)) + ((x : ℤ) - s) * ((s : ℤ) + x - 1) := by
      have hcast : ((2 * (∑ r ∈ (range x).filter (fun r => s ≤ r), (N - (a - 1) + r)) : ℕ) : ℤ) =
          ((2 * (x - s) * (N - (a - 1)) + (x - s) * (s + x - 1) : ℕ) : ℤ) := by
        exact_mod_cast hsuf_sum
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] at hcast
      rw [hcast]
      have h1 : ((x - s : ℕ) : ℤ) = (x : ℤ) - s := by omega
      have h2 : ((N - (a - 1) : ℕ) : ℤ) = (N : ℤ) - ((a : ℤ) - 1) := by omega
      have h3 : ((s + x - 1 : ℕ) : ℤ) = (s : ℤ) + x - 1 := by omega
      push_cast
      rw [h1, h2, h3]
    have hsplitZ : (∑ j : Fin x, (l j : ℤ)) = (∑ j : Fin s, (l_pre j : ℤ)) +
        ∑ r ∈ (range x).filter (fun r => s ≤ r), ((N - (a - 1) + r : ℕ) : ℤ) := by
      exact_mod_cast hsplit
    have hmul2Z : ((x * (x - 1) / 2 : ℕ) : ℤ) * 2 = (x : ℤ) * ((x : ℤ) - 1) := by
      have hcast : (((x * (x - 1) / 2 * 2 : ℕ) : ℤ)) = ((x * (x - 1) : ℕ) : ℤ) := by
        exact_mod_cast hmul2
      rw [Nat.cast_mul, Nat.cast_ofNat] at hcast
      rw [hcast, Nat.cast_mul, show ((x - 1 : ℕ) : ℤ) = (x : ℤ) - 1 by omega]
    have hNZ : (N : ℤ) = (d : ℤ) + (a : ℤ) - 1 - (x : ℤ) := by omega
    have hgoalZ : (((∑ j : Fin x, l j) - x * (x - 1) / 2 : ℕ) : ℤ) ≤
        (degreeBudget d a x s : ℤ) := by
      rw [Nat.cast_sub (by omega : x * (x - 1) / 2 ≤ ∑ j, l j), Nat.cast_sum]
      unfold degreeBudget
      rw [Nat.cast_sub hbudget_le, Nat.cast_mul, Nat.cast_mul,
        show ((d + a - 2 * x : ℕ) : ℤ) = (d : ℤ) + a - 2 * x by omega,
        show ((x - s : ℕ) : ℤ) = (x : ℤ) - s by omega,
        show ((a - x - s : ℕ) : ℤ) = (a : ℤ) - x - s by omega]
      nlinarith only [hpreZ, hsufZ, hsplitZ, hmul2Z, hNZ]
    exact_mod_cast hgoalZ

end WronskianDegree

end ProximityGap.PaleySignedHankelDegree

#print axioms ProximityGap.PaleySignedHankelDegree.signedDet_ne_zero_and_natDegree_le
