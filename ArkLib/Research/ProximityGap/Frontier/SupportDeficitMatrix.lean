/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SupportDeficitFourthMoment
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonRank
import Mathlib.Tactic

/-! # All-center list bounds from agreement-support deficit matrices

A fourth-trace estimate excludes a family of more than twice the block length at three
production error counts, for every injective evaluation grid. -/

namespace ProximityGap.SupportDeficitMatrix
open Matrix Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem trace_pow {D : Matrix ι ι ℝ} (hD : D.IsHermitian) (k : ℕ) :
    (D ^ k).trace = ∑ i, (hD.eigenvalues i) ^ k := by
  conv_lhs =>
    rw [hD.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

private theorem trace_squared_le_rank {D : Matrix ι ι ℝ} (hD : D.IsHermitian) :
    D.trace ^ 2 ≤ D.rank * (D ^ 2).trace := by
  let f := hD.eigenvalues
  let T := univ.filter (fun i => f i ≠ 0)
  have hz (k : ℕ) (hk : 0 < k) : ∑ i ∈ T, f i ^ k = ∑ i, f i ^ k := by
    apply sum_subset (subset_univ _)
    intro i _ hi
    have h : f i = 0 := by simpa [T] using hi
    simp [h, Nat.ne_of_gt hk]
  have hcount : T.card = D.rank := by
    rw [hD.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have h := sum_mul_sq_le_sq_mul_sq T (fun _ : ι => (1 : ℝ)) f
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, hcount] at h
  have h1 := hz 1 (by decide)
  simp only [pow_one] at h1
  rw [h1, hz 2 (by decide)] at h
  simpa [hD.trace_eq_sum_eigenvalues, trace_pow hD, f] using h

private theorem basis_squares {D : Matrix ι ι ℝ} (hD : D.IsHermitian) (i : ι) :
    ∑ j, (hD.eigenvectorBasis i j) ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix ι ι ℝ => M i i)
    (Unitary.coe_star_mul_self hD.eigenvectorUnitary)
  simpa [Matrix.mul_apply, Matrix.star_apply, hD.eigenvectorUnitary_apply, pow_two] using h

private theorem basis_coordinate_sum {D : Matrix ι ι ℝ} (hD : D.IsHermitian) :
    ∑ i, (∑ j, hD.eigenvectorBasis i j) ^ 2 = Fintype.card ι := by
  let U := (hD.eigenvectorUnitary : Matrix ι ι ℝ)
  have hr (i j : ι) : ∑ k, U i k * U j k = if i = j then 1 else 0 := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M i j)
      (Unitary.coe_mul_star_self hD.eigenvectorUnitary)
    simpa [U, Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] using h
  change (∑ i, (∑ j, U j i) ^ 2) = _
  calc
    _ = ∑ i, ∑ j, ∑ k, U j i * U k i := by simp only [pow_two, sum_mul_sum]
    _ = ∑ j, ∑ i, ∑ k, U j i * U k i := sum_comm
    _ = ∑ j, ∑ k, ∑ i, U j i * U k i := sum_congr rfl fun j _ => sum_comm
    _ = _ := by simp [hr]

/-- The real quadratic form of a matrix on coordinate vectors. -/
def form (D : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := ∑ i, ∑ j, x i * D i j * x j

omit [DecidableEq ι] in
private lemma abs_form_le {D : Matrix ι ι ℝ} (hD : ∀ i j, 0 ≤ D i j) (x : ι → ℝ) :
    |form D x| ≤ form D (fun i => |x i|) := by
  dsimp [form]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  simpa only [abs_mul, abs_of_nonneg (hD i _)] using
    (abs_sum_le_sum_abs (fun j : ι => x i * D i j * x j) univ)

omit [DecidableEq ι] in
private lemma sum_sq_cauchy (x : ι → ℝ) : (∑ i, x i) ^ 2 ≤ Fintype.card ι * ∑ i, (x i) ^ 2 := by
  simpa using sum_mul_sq_le_sq_mul_sq univ (fun _ : ι => (1 : ℝ)) x

private lemma form_of_eigenvector {D : Matrix ι ι ℝ} (hD : D.IsHermitian) (i : ι) :
    form D (hD.eigenvectorBasis i) = hD.eigenvalues i := by
  conv_rhs => rw [hD.eigenvalues_eq i]
  simp [form, dotProduct, Matrix.mulVec, mul_sum, mul_assoc]

omit [DecidableEq ι] in
private lemma spectral_weighted (e z : ι → ℝ) (eps L : ℝ)
    (heps : 0 ≤ eps) (hL : 1 ≤ L) (hz : ∀ i, 0 ≤ z i)
    (hsum : eps * ∑ i, z i = L - 1)
    (hrange : ∀ i, |e i| ≤ L) (hdiag : ∀ i, e i - 1 ≤ eps * z i)
    (hcubic : ∑ i, (1 - e i) * (1 + e i) ^ 2 ≤ 0) :
    ∑ i, (e i ^ 2 - 1) ^ 2 ≤ 2 * L * (L - 1) * (L + 1) ^ 2 := by
  have hterm (i : ι) : (e i ^ 2 - 1) ^ 2 ≤
      (L + 1) * ((1 - e i) * (1 + e i) ^ 2) + (eps * z i) * (2 * L * (L + 1) ^ 2) := by
    have h1 := (abs_le.mp (hrange i)).1
    have h2 := (abs_le.mp (hrange i)).2
    have hsq : (1 + e i) ^ 2 ≤ (L + 1) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) (show 0 ≤ L + e i + 2 by linarith)]
    have hnon : 0 ≤ (L + e i) * (1 + e i) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have hle : (L + e i) * (1 + e i) ^ 2 ≤ 2 * L * (L + 1) ^ 2 :=
      mul_le_mul (by linarith) hsq (sq_nonneg _) (by linarith)
    have h := (mul_le_mul_of_nonneg_right (hdiag i) hnon).trans
      (mul_le_mul_of_nonneg_left hle (mul_nonneg heps (hz i)))
    nlinarith only [h]
  have h := sum_le_sum (s := (univ : Finset ι)) fun i _ => hterm i
  simp only [sum_add_distrib, ← mul_sum, ← sum_mul] at h
  have hh := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ L + 1 by linarith) hcubic
  rw [hsum] at h
  nlinarith only [h, hh]

private lemma trace_two {D : Matrix ι ι ℝ} (hD : ∀ i j, D i j = D j i) :
    (D ^ 2).trace = ∑ i, ∑ j, D i j ^ 2 := by
  simp only [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hD j i]

private lemma trace_four {D : Matrix ι ι ℝ} (hD : ∀ i j, D i j = D j i) :
    (D ^ 4).trace = ∑ i, ∑ j, (∑ k, D i k * D j k) ^ 2 := by
  have hM (i j : ι) : (D ^ 2) i j = ∑ k, D i k * D j k := by
    simp only [pow_two, Matrix.mul_apply]
    exact sum_congr rfl fun k _ => by rw [hD k j]
  have hsym (i j : ι) : (D ^ 2) i j = (D ^ 2) j i := by
    simp only [hM]; exact sum_congr rfl fun k _ => mul_comm ..
  rw [show 4 = 2 * 2 by decide, pow_mul, trace_two hsym]
  simp only [hM]

/-- A symmetric nonnegative matrix whose quadratic form is dominated by the identity
plus a rank-one error satisfies this fourth-moment bound when its shift has rank at
most half the matrix size. -/
theorem fourth_matrix_bound (D : Matrix ι ι ℝ) (eps cap : ℝ)
    (heps : 0 ≤ eps) (hcap : 0 ≤ cap) (hlecap : cap ≤ 1)
    (hn : 0 < Fintype.card ι)
    (hsym : ∀ i j, D i j = D j i) (hdiag : ∀ i, D i i = 0)
    (hpos : ∀ i j, 0 ≤ D i j) (hentry : ∀ i j, D i j ≤ cap)
    (hrank : 2 * (1 - D).rank ≤ Fintype.card ι)
    (hform : ∀ x, form D x ≤ (∑ i, x i ^ 2) + eps * (∑ i, x i) ^ 2) :
    let m : ℝ := Fintype.card ι
    let L := 1 + m * eps
    m * (1 - cap ^ 2) ≤ 2 * L * (L - 1) * (L + 1) ^ 2 := by
  let m : ℝ := Fintype.card ι
  let L := 1 + m * eps
  change m * (1 - cap ^ 2) ≤ 2 * L * (L - 1) * (L + 1) ^ 2
  have hm : 0 < m := by dsimp [m]; exact_mod_cast hn
  have hL : 1 ≤ L := by dsimp [L]; linarith [mul_nonneg hm.le heps]
  have hherm : D.IsHermitian := Matrix.IsHermitian.ext (fun i j => by simpa using hsym j i)
  have hself : (1 - D).IsHermitian := Matrix.isHermitian_one.sub hherm
  have htrace : D.trace = 0 := by simp [Matrix.trace, Matrix.diag, hdiag]
  have hsecond0 : 0 ≤ (D ^ 2).trace := by rw [trace_two hsym]; positivity
  have htraceI : (1 - D).trace = m := by simp [htrace, m]
  have htraceI2 : ((1 - D) ^ 2).trace = m + (D ^ 2).trace := by
    rw [show (1 - D) ^ 2 = 1 - (D + D) + D ^ 2 by noncomm_ring]
    simp [Matrix.trace_add, Matrix.trace_sub, htrace, m]
  have hsecond : m ≤ (D ^ 2).trace := by
    have hr : 2 * ((1 - D).rank : ℝ) ≤ m := by dsimp [m]; exact_mod_cast hrank
    have h := trace_squared_le_rank hself
    rw [htraceI, htraceI2] at h
    have h' := mul_le_mul_of_nonneg_right hr (show 0 ≤ m + (D ^ 2).trace by linarith)
    nlinarith [show 0 < m by exact hm]
  have hcub : 0 ≤ (D ^ 3).trace := by
    rw [show D ^ 3 = D * D * D by noncomm_ring]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact sum_nonneg fun i _ => sum_nonneg fun j _ =>
      mul_nonneg (sum_nonneg fun k _ => mul_nonneg (hpos _ _) (hpos _ _)) (hpos _ _)
  have hwall : ∀ x : ι → ℝ, form D x ≤ L * ∑ i, x i ^ 2 := by
    intro x
    have hw := hform x
    have hc := mul_le_mul_of_nonneg_left (sum_sq_cauchy x) heps
    dsimp [L, m]; nlinarith only [hw, hc]
  let e := hherm.eigenvalues
  let z := fun i => (∑ j, hherm.eigenvectorBasis i j) ^ 2
  have heig (i : ι) : |e i| ≤ L := by
    have h := (abs_form_le hpos (hherm.eigenvectorBasis i)).trans
      (hwall (fun j => |hherm.eigenvectorBasis i j|))
    simpa only [sq_abs, basis_squares, form_of_eigenvector, mul_one] using h
  have hbound (i : ι) : e i - 1 ≤ eps * z i := by
    have h := hform (hherm.eigenvectorBasis i)
    rw [form_of_eigenvector, basis_squares] at h
    dsimp [e, z]; linarith
  have hpoly : (∑ i, (1 - e i) * (1 + e i) ^ 2) =
      m + D.trace - (D ^ 2).trace - (D ^ 3).trace := by
    rw [trace_pow hherm 2, trace_pow hherm 3, hherm.trace_eq_sum_eigenvalues]
    calc
      _ = ∑ i, (1 + e i - (e i) ^ 2 - (e i) ^ 3) := sum_congr rfl fun i _ => by ring
      _ = _ := by simp [sum_add_distrib, sum_sub_distrib, m, e]
  have hsu : (∑ i, z i) = m := basis_coordinate_sum hherm
  -- Bound the fourth trace in the eigenbasis.
  have hupper := spectral_weighted e z eps L heps hL (fun i => sq_nonneg _)
    (by rw [hsu]; dsimp [L]; ring) heig hbound (by rw [hpoly, htrace]; linarith)
  have hep : (∑ i, (e i ^ 2 - 1) ^ 2) = (D ^ 4).trace - 2 * (D ^ 2).trace + m := by
    rw [trace_pow hherm 2, trace_pow hherm 4]
    calc
      _ = ∑ i, ((e i) ^ 4 - 2 * (e i) ^ 2 + 1) := sum_congr rfl fun i _ => by ring
      _ = _ := by simp [sum_add_distrib, sum_sub_distrib, ← mul_sum, m, e]
  rw [hep] at hupper
  -- Bound the same trace from below in the support basis.
  let r := fun i => ∑ j, D i j ^ 2
  have hr : (∑ i, r i) = (D ^ 2).trace := (trace_two hsym).symm
  have hr2 := sum_sq_cauchy r
  rw [hr] at hr2
  change (D ^ 2).trace ^ 2 ≤ m * ∑ i, r i ^ 2 at hr2
  have hfour := SupportDeficitFourthMoment.entryFourthLower D hsym hpos
  rw [← trace_four hsym] at hfour
  have hentries : (∑ i, ∑ j, D i j ^ 4) ≤ cap ^ 2 * (D ^ 2).trace := by
    rw [← hr]; simp only [r, mul_sum]
    apply sum_le_sum; intro i _; apply sum_le_sum; intro j _
    have hh : (D i j) ^ 2 ≤ cap ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hentry i j))
        (show 0 ≤ cap + D i j by linarith [hpos i j])]
    simpa only [show 4 = 2 + 2 by decide, pow_add] using mul_le_mul_of_nonneg_right hh (sq_nonneg _)
  change 2 * (∑ i, r i ^ 2) - _ ≤ _ at hfour
  have hfirst : m * (1 - cap ^ 2) ≤ (D ^ 4).trace - 2 * (D ^ 2).trace + m := by
    have hcap2 : cap ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hlecap) (show 0 ≤ 1 + cap by linarith)]
    have hterm := mul_nonneg (sub_nonneg.mpr hsecond)
      (show 0 ≤ 2 * (D ^ 2).trace - cap ^ 2 * m by
        nlinarith [mul_le_mul_of_nonneg_right hcap2 hm.le])
    have hm1 := mul_le_mul_of_nonneg_left hfour hm.le
    have hm2 := mul_le_mul_of_nonneg_left hentries hm.le
    apply (le_of_mul_le_mul_left ?_ hm)
    nlinarith only [hr2, hterm, hm1, hm2]
  exact hfirst.trans hupper

variable {α : Type*} [Fintype α]

private def overlap (U : Matrix ι α ℝ) (i j : ι) := ∑ z, U i z * U j z

private noncomputable def shifted (U : Matrix ι α ℝ) (a s : ℝ) : Matrix ι ι ℝ :=
  1 + Matrix.of fun i j => (s - overlap U i j) / a

private lemma shifted_rank (U : Matrix ι α ℝ) (t a s : ℝ) (ht : t ≠ 0)
    (hrow : ∀ i, ∑ z, U i z = t) : (1 - shifted U a s).rank ≤ Fintype.card α := by
  let V : Matrix α ι ℝ := Matrix.of fun z j => (U j z - s / t) / a
  have hv : 1 - shifted U a s = U * V := by
    ext i j
    simp only [shifted, Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply, Matrix.mul_apply, V,
      overlap, ← mul_div_assoc, mul_sub, sum_sub_distrib, ← sum_div, ← sum_mul, hrow i]
    field_simp; ring
  rw [hv]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width U)

omit [DecidableEq ι] in
private lemma aggregate (U : Matrix ι α ℝ) (x : ι → ℝ) :
    (∑ i, ∑ j, x i * overlap U i j * x j) =
      ∑ z, (∑ i, x i * U i z) ^ 2 := by
  calc
    _ = ∑ i, ∑ j, ∑ z, (x i * U i z) * (x j * U j z) := by
      simp only [overlap, mul_sum, sum_mul]
      apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
      exact sum_congr rfl fun z _ => by ring
    _ = ∑ i, ∑ z, ∑ j, (x i * U i z) * (x j * U j z) :=
      sum_congr rfl fun i _ => sum_comm
    _ = ∑ z, ∑ i, ∑ j, (x i * U i z) * (x j * U j z) := sum_comm
    _ = _ := by simp only [pow_two, sum_mul_sum]

private lemma shifted_form (U : Matrix ι α ℝ) (t a s : ℝ) (ha : 0 < a)
    (hn : 0 < Fintype.card α) (hrow : ∀ i, ∑ z, U i z = t) (x : ι → ℝ) :
    form (shifted U a s) x ≤ (∑ i, x i ^ 2) +
      (((Fintype.card α : ℝ) * s - t ^ 2) / ((Fintype.card α : ℝ) * a)) * (∑ i, x i) ^ 2 := by
  let y := fun (z : α) => ∑ i, x i * U i z
  have hs : (∑ z, y z) = t * ∑ i, x i := by
    dsimp [y]
    rw [sum_comm]; simp only [← mul_sum, hrow, ← sum_mul, mul_comm t]
  have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset α) (fun _ => (1 : ℝ)) y
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, hs] at hc
  have hform :
      form (shifted U a s) x =
        (∑ i, x i ^ 2) + (s * (∑ i, x i) ^ 2 - (∑ z, (y z) ^ 2)) / a := by
    have elem (i j : ι) :
        x i * (shifted U a s) i j * x j =
          (if i = j then x i ^ 2 else 0) +
          (s * (x i * x j) - x i * overlap U i j * x j) / a := by
      by_cases hij : i = j
      · subst j; simp [shifted]; ring
      · simp [shifted, hij]; ring
    dsimp [form]; simp only [elem, sum_add_distrib, sum_ite_eq, mem_univ, ite_true,
      ← sum_div, sum_sub_distrib, ← mul_sum, ← sum_mul, ← sq, aggregate, y]
  rw [hform]
  have hn' : (0 : ℝ) < Fintype.card α := by exact_mod_cast hn
  apply (add_le_add_iff_left _).2
  field_simp [ha.ne', hn'.ne']
  nlinarith only [hc]

variable [DecidableEq α]
private def indicators (T : ι → Finset α) : Matrix ι α ℝ :=
  Matrix.of fun i z => if z ∈ T i then 1 else 0

omit [Fintype ι] [DecidableEq ι] in
private lemma indicator_row (T : ι → Finset α) (i : ι) :
    (∑ z, indicators T i z) = (T i).card := by
  simp [indicators]

omit [Fintype ι] [DecidableEq ι] in
private lemma indicator_overlap (T : ι → Finset α) (i j : ι) :
    overlap (indicators T) i j = (T i ∩ T j).card := by
  classical
  unfold overlap
  calc
    _ = ∑ z, (if z ∈ T i ∩ T j then (1 : ℝ) else 0) := by
      apply sum_congr rfl; intro z _
      by_cases hi : z ∈ T i <;> by_cases hj : z ∈ T j <;> simp [indicators, hi, hj]
    _ = _ := by rw [sum_boole]; simp only [filter_mem_eq_inter, univ_inter]

omit [DecidableEq ι] in
/-- Constant-weight supports, with off-diagonal intersections between the supplied
lower and upper bounds, obey the spectral inequality on a board of at most half
the family size. -/
theorem block_bound (S : ι → Finset α) (t s l : ℕ) (hn : 0 < Fintype.card α)
    (ht : s < t) (hl : l ≤ s) (hcap : s + s ≤ t + l)
    (hgrid : t ^ 2 ≤ Fintype.card α * s) (hm : 2 * Fintype.card α ≤ Fintype.card ι)
    (hsize : ∀ i, (S i).card = t)
    (hpair : ∀ i j, i ≠ j → l ≤ (S i ∩ S j).card ∧ (S i ∩ S j).card ≤ s) :
    let a := (t : ℝ) - s
    let eps := ((Fintype.card α : ℝ) * s - t ^ 2) / ((Fintype.card α : ℝ) * a)
    let L := 1 + (Fintype.card ι : ℝ) * eps
    (Fintype.card ι : ℝ) * (1 - (((s : ℝ) - l) / a) ^ 2) ≤ 2 * L * (L - 1) * (L + 1) ^ 2 := by
  classical
  let U := indicators S
  let a := (t : ℝ) - s
  let eps := ((Fintype.card α : ℝ) * s - t ^ 2) / ((Fintype.card α : ℝ) * a)
  let cap := ((s : ℝ) - l) / a
  let D := shifted U a s
  have ha : 0 < a := sub_pos.mpr (by exact_mod_cast ht)
  have ht' : (t : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < t by omega))
  have hn' : (0 : ℝ) < Fintype.card α := by exact_mod_cast hn
  have heps : 0 ≤ eps := by
    apply div_nonneg _ (mul_pos hn' ha).le
    exact sub_nonneg.mpr (by exact_mod_cast hgrid)
  have hnon : 0 ≤ cap := div_nonneg (sub_nonneg.mpr (by exact_mod_cast hl)) ha.le
  have hle : cap ≤ 1 := by
    apply (div_le_iff₀ ha).2
    dsimp [a]; simp only [one_mul]
    have hnat : (s : ℝ) + s ≤ (t : ℝ) + l := by exact_mod_cast hcap
    linarith
  have hu (i : ι) : ∑ z, U i z = t := by rw [indicator_row, hsize]
  have hsum (i j : ι) : D i j =
      (if i = j then 1 else 0) + ((s : ℝ) - (S i ∩ S j).card) / a := by
    simp only [D, shifted, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply,
      U, indicator_overlap]
  have hd (i : ι) : D i i = 0 := by
    rw [hsum, ite_eq_left rfl, inter_self, hsize]
    rw [show (s : ℝ) - t = -a by dsimp [a]; ring, neg_div, div_self ha.ne']; ring
  have hsy (i j : ι) : D i j = D j i := by
    rw [hsum, hsum, inter_comm]; by_cases h : i = j <;> simp_all [eq_comm]
  have he (i j : ι) : 0 ≤ D i j ∧ D i j ≤ cap := by
    by_cases hij : i = j
    · subst j; simp [hd, hnon]
    rw [hsum, ite_eq_right hij, zero_add]
    have h := hpair i j hij
    constructor
    · exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast h.2)) ha.le
    · exact div_le_div_of_nonneg_right (sub_le_sub_left (by exact_mod_cast h.1) _) ha.le
  have hr := shifted_rank U (t : ℝ) a s ht' hu
  apply fourth_matrix_bound D eps cap heps hnon hle (by omega) hsy hd
    (fun i j => (he i j).1) (fun i j => (he i j).2)
    (by change 2 * (1 - shifted U a s).rank ≤ _; omega)
    (shifted_form U (t : ℝ) a s ha hn hu)

/-- A failed fourth-moment comparison excludes a list exceeding twice the block length. -/
theorem interleaved_at_errors {F : Type*} [Field F] (D : Fin 1073741824 ↪ F)
    (arity k e t s l : ℕ) (hs : s = k - 1) (he : e + t = 1073741824)
    (ht : s < t) (hl : l ≤ s) (hcap : s + s ≤ t + l)
    (hgrid : t ^ 2 ≤ 1073741824 * s)
    (hfloor : l = 0 ∨ 1073741824 + l ≤ t + t)
    (hstrict : let a := (t : ℝ) - s
               let L := 1 + (2147483649 : ℝ) *
                 ((1073741824 : ℝ) * s - t ^ 2) / (1073741824 * a)
               2 * L * (L - 1) * (L + 1) ^ 2 < 2147483649 * (1 - (((s : ℝ) - l) / a) ^ 2)) :
    InterleavedListJohnsonRank.AtErrors D arity k e 2147483648 := by
  classical
  refine InterleavedListJohnsonRank.interleaved_lambda_le_of_block_bound D k t arity _ _ ?_ ?_
  · simp only [Fintype.card_fin, Nat.cast_ofNat]
    have hsum : (e : ℝ) + t = 1073741824 := by exact_mod_cast he
    linarith
  intro m S hsize hpair
  by_contra! h
  let emb : Fin 2147483649 ↪ Fin m := Fin.castLEEmb (by omega)
  let T := S ∘ emb
  have pair (i j : Fin 2147483649) (hij : i ≠ j) :
      l ≤ (T i ∩ T j).card ∧ (T i ∩ T j).card ≤ s := by
    constructor
    · rcases hfloor with hz | low
      · omega
      have hu := card_le_univ (T i ∪ T j)
      have hi := card_union_add_card_inter (T i) (T j)
      change _ = (S (emb i)).card + (S (emb j)).card at hi
      rw [hsize, hsize] at hi
      simp only [Fintype.card_fin] at hu
      omega
    · rw [hs]
      exact hpair (emb.injective.ne hij)
  have bound := block_bound T t s l (by simp) ht hl hcap (by simpa using hgrid)
    (by simp) (fun i => hsize _) pair
  simp only [Fintype.card_fin, Nat.cast_ofNat] at bound
  dsimp at hstrict
  rw [mul_div_assoc] at hstrict
  exact (not_le_of_gt hstrict) bound

/-- The half-, eighth- and sixteenth-rate budgets hold at their improved production radii. -/
theorem production_at_errors {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (arity : ℕ) :
    InterleavedListJohnsonRank.AtErrors D arity 536870912 314491712 2147483648 ∧
    InterleavedListJohnsonRank.AtErrors D arity 134217728 694116789 2147483648 ∧
    InterleavedListJohnsonRank.AtErrors D arity 67108864 805306402 2147483648 := by
  refine ⟨interleaved_at_errors D arity _ _ 759250112 536870911 444758400 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,
    interleaved_at_errors D arity _ _ 379625035 134217727 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,
    interleaved_at_errors D arity _ _ 268435422 67108863 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;> norm_num

end ProximityGap.SupportDeficitMatrix

#print axioms ProximityGap.SupportDeficitMatrix.production_at_errors
