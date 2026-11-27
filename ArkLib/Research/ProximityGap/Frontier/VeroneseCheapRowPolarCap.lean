/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PlanePolarCap
import ArkLib.Research.ProximityGap.Frontier.TangentVeronesePacking
import ArkLib.Research.ProximityGap.Frontier.EighthCollinearOutlier

/-! # Veronese cheap-row polar caps, fixed rich-head rows, transverse cap, and conic 5-column cap

Completes Worker Packet L2d by wiring L2a–c (`PlanePolarCap`) into `TangentVeronesePacking` and
`EighthCollinearOutlier`:

1. **Exact combinatorial identities** on `TangentVeronesePacking.monomials s`:
   - `card_monomials`: `(monomials s).card = (s + 2).choose 2`
   - `sum_weight_monomials`: `∑ ij ∈ monomials s, (ij.1 + ij.2) = s * (s + 1) * (s + 2) / 3`
   - `sum_sub_weight_monomials`: `∑ ij ∈ monomials s, (a - (ij.1 + ij.2)) = (a + 2).choose 3` (`a ≤ s`)
2. **Fixed rich-head linear independence** (`fixed_rows_linearIndependent`):
   any `p ≤ s + 1` distinct affine points in `K × K` (even collinear!) have linearly independent
   degree-`s` Veronese rows.
3. **Vanishing-minor dual curve extraction** (`exists_dual_curve_of_vanishing_minors`):
   for any subset `B ⊆ monomials s`, `p` linearly independent fixed rows, and a family of candidate
   rows such that every `B.card × B.card` minor combining the `p` fixed rows with `B.card - p`
   candidate rows vanishes, there exists a nonzero homogeneous degree-`s` polynomial `Q(H, R, V)`
   supported on `B` vanishing on every candidate row.
4. **Main campaign theorems**:
   - `veronese_polar_cap`: unified bound for `0 ≤ p ≤ s + 1` fixed rows (covers `TangentPolarWindows`,
     `HalfCoreWeightedJets`, `QuarterCommonFactorDegrees`, `HalfSparseGaussWindow`).
   - `transverse_polar_cap`: `s = 1` polar cap + `EighthCollinearOutlier.rational_tangent_population`
     (covers `QuarterTransverseTangentBudget`).
   - `conic_five_column_cap`: 5 downward-closed columns of `monomials 2` + `conic_five_column_polar_cap`
     (covers `TangentPolarWindows.beyond_johnson` at `m = 2`).
-/

set_option autoImplicit false
noncomputable section

open Polynomial MvPolynomial Finset Module Matrix
open ArkLib.ProximityGap.Frontier.GeometricIrreducibilitySmoothPoint
open ArkLib.ProximityGap.Frontier.PlaneBezoutWithMultiplicity
open ArkLib.ProximityGap.Frontier.PlaneCurveReflexivity
open ArkLib.ProximityGap.Frontier.PlanePolarCap
open ArkLib.ProximityGap.Frontier.TangentVeronesePacking
open ArkLib.ProximityGap.Frontier.EighthCollinearOutlier

namespace ArkLib.ProximityGap.Frontier.VeroneseCheapRowPolarCap

section Combinatorics

/-- Membership characterization for `TangentVeronesePacking.monomials`. -/
theorem mem_monomials_iff (s : ℕ) (ij : ℕ × ℕ) :
    ij ∈ monomials s ↔ ij.1 + ij.2 ≤ s := by
  simp only [monomials, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- Shell decomposition: `monomials (s + 1)` is the disjoint union of `monomials s` and the
degree-`(s + 1)` shell `{(i, s + 1 - i) | i ∈ range (s + 2)}`. -/
private def shell (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (k + 1)).image fun i => (i, k - i)

private theorem mem_shell_iff (k : ℕ) (ij : ℕ × ℕ) :
    ij ∈ shell k ↔ ij.1 + ij.2 = k := by
  simp only [shell, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨ij.1, by omega, Prod.ext rfl (by omega)⟩

private theorem card_shell (k : ℕ) : (shell k).card = k + 1 := by
  rw [shell, Finset.card_image_of_injOn]
  · exact Finset.card_range (k + 1)
  · intro a _ b _ hab
    exact congrArg Prod.fst hab

private theorem monomials_succ (s : ℕ) :
    monomials (s + 1) = monomials s ∪ shell (s + 1) := by
  ext ij
  simp only [Finset.mem_union, mem_monomials_iff, mem_shell_iff]
  omega

private theorem disjoint_monomials_shell (s : ℕ) :
    Disjoint (monomials s) (shell (s + 1)) := by
  rw [Finset.disjoint_left]
  intro ij hij hsh
  rw [mem_monomials_iff] at hij
  rw [mem_shell_iff] at hsh
  omega

/-- The degree-`s` bivariate monomial basis has cardinality `C(s + 2, 2)`. -/
theorem card_monomials (s : ℕ) : (monomials s).card = (s + 2).choose 2 := by
  induction s with
  | zero => decide
  | succ s ih =>
    rw [monomials_succ, Finset.card_union_of_disjoint (disjoint_monomials_shell s), ih, card_shell]
    have h1 : (s + 1 + 2).choose 2 = (s + 2).choose 2 + (s + 2).choose 1 := by
      rw [show s + 1 + 2 = (s + 2) + 1 by omega, Nat.choose_succ_succ, add_comm]
    rw [h1, Nat.choose_one_right]

/-- Sum of weights `i + j` over `monomials s` equals `s * (s + 1) * (s + 2) / 3`. -/
theorem sum_weight_monomials (s : ℕ) :
    ∑ ij ∈ monomials s, (ij.1 + ij.2) = s * (s + 1) * (s + 2) / 3 := by
  have h3 : 3 * ∑ ij ∈ monomials s, (ij.1 + ij.2) = s * (s + 1) * (s + 2) := by
    induction s with
    | zero => decide
    | succ s ih =>
      rw [monomials_succ, Finset.sum_union (disjoint_monomials_shell s), Nat.mul_add, ih]
      have hsh : ∑ ij ∈ shell (s + 1), (ij.1 + ij.2) = (s + 2) * (s + 1) := by
        calc ∑ ij ∈ shell (s + 1), (ij.1 + ij.2)
            = ∑ _ij ∈ shell (s + 1), (s + 1) :=
              Finset.sum_congr rfl fun ij hij => (mem_shell_iff (s + 1) ij).mp hij
          _ = (shell (s + 1)).card * (s + 1) := by simp
          _ = (s + 2) * (s + 1) := by rw [card_shell]
      rw [hsh]; ring
  omega

/-- Truncated weight deficit sum `∑ (a - (i + j))` over `monomials s` equals `C(a + 2, 3)` for `a ≤ s`. -/
theorem sum_sub_weight_monomials (s a : ℕ) (has : a ≤ s) :
    ∑ ij ∈ monomials s, (a - (ij.1 + ij.2)) = (a + 2).choose 3 := by
  have hsub : monomials a ⊆ monomials s := fun ij hij => by
    rw [mem_monomials_iff] at hij ⊢; omega
  have hred : ∑ ij ∈ monomials s, (a - (ij.1 + ij.2)) = ∑ ij ∈ monomials a, (a - (ij.1 + ij.2)) := by
    symm
    refine Finset.sum_subset hsub fun ij _ hnot => ?_
    rw [mem_monomials_iff] at hnot
    omega
  rw [hred]
  clear has hsub hred s
  induction a with
  | zero => decide
  | succ a ih =>
    rw [monomials_succ, Finset.sum_union (disjoint_monomials_shell a)]
    have hsh0 : ∑ ij ∈ shell (a + 1), (a + 1 - (ij.1 + ij.2)) = 0 := by
      apply Finset.sum_eq_zero
      intro ij hij
      rw [mem_shell_iff] at hij; omega
    have hinc : ∑ ij ∈ monomials a, (a + 1 - (ij.1 + ij.2)) =
        (∑ ij ∈ monomials a, (a - (ij.1 + ij.2))) + (monomials a).card := by
      have hcard : (monomials a).card = ∑ _ij ∈ monomials a, 1 := by simp
      rw [hcard, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ij hij => ?_
      rw [mem_monomials_iff] at hij
      omega
    rw [hsh0, add_zero, hinc, ih, card_monomials]
    have hc : (a + 1 + 2).choose 3 = (a + 2).choose 2 + (a + 2).choose 3 := by
      rw [show a + 1 + 2 = (a + 2) + 1 by omega, Nat.choose_succ_succ]
    omega

/-- Any 5-element subset `B = (monomials 2).erase e₀` obtained by omitting a degree-2 monomial
`e₀` (`e₀.1 + e₀.2 = 2`) is downward-closed and satisfies the exact conic parameters
`card = 5`, `∑ (i + j) = 6`, `∑ (1 - (i + j)) = 1`. -/
theorem conic_five_columns_props {e₀ : ℕ × ℕ} (he₀ : e₀.1 + e₀.2 = 2) :
    let B := (monomials 2).erase e₀
    B.card = 5 ∧
    (∀ ab ∈ B, ∀ ij : ℕ × ℕ, ij.1 ≤ ab.1 → ij.2 ≤ ab.2 → ij ∈ B) ∧
    (∑ ij ∈ B, (ij.1 + ij.2)) = 6 ∧
    (∑ ij ∈ B, (1 - (ij.1 + ij.2))) = 1 := by
  intro B
  have hmem : e₀ ∈ monomials 2 := (mem_monomials_iff 2 e₀).mpr (le_of_eq he₀)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem hmem, card_monomials]; decide
  · intro ab hab ij h1 h2
    have hab_m := (mem_monomials_iff 2 ab).mp (Finset.mem_of_mem_erase hab)
    have hab_ne : ab ≠ e₀ := Finset.ne_of_mem_erase hab
    refine Finset.mem_erase.mpr ⟨?_, (mem_monomials_iff 2 ij).mpr (by omega)⟩
    intro hij
    apply hab_ne
    subst hij
    exact Prod.ext (by omega) (by omega)
  · have hsum := Finset.add_sum_erase (monomials 2) (fun ij : ℕ × ℕ => ij.1 + ij.2) hmem
    have htot := sum_weight_monomials 2
    dsimp only [B]; omega
  · have hsum := Finset.add_sum_erase (monomials 2) (fun ij : ℕ × ℕ => 1 - (ij.1 + ij.2)) hmem
    have htot := sum_sub_weight_monomials 2 1 (by omega)
    have hchoose : (1 + 2).choose 3 = 1 := by decide
    rw [hchoose] at htot
    dsimp only [B]; omega

end Combinatorics

section LinearAlgebra

variable {K : Type*} [Field K]

/-- Exponent vector in `Fin 3 →₀ ℕ` corresponding to `(i, j) ∈ monomials s` in homogeneous
coordinates `(H, R, V) = (X 0, X 1, X 2)`: `H^(s - (i + j)) * R^i * V^j`. -/
def veroneseExp (s : ℕ) (ij : ℕ × ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 (s - (ij.1 + ij.2)) + Finsupp.single 1 ij.1 + Finsupp.single 2 ij.2

theorem veroneseExp_injOn (s : ℕ) : Set.InjOn (veroneseExp s) (monomials s : Set (ℕ × ℕ)) := by
  intro a _ b _ hab
  have h1 := congrArg (fun f : Fin 3 →₀ ℕ => f 1) hab
  have h2 := congrArg (fun f : Fin 3 →₀ ℕ => f 2) hab
  simp [veroneseExp] at h1 h2
  exact Prod.ext h1 h2

/-- Convert a coefficient vector `v : ↥B → K` (on any subset `B ⊆ monomials s`) into a
homogeneous degree-`s` polynomial `Q : MvPolynomial (Fin 3) K`. -/
def dualPolyOfVec {s : ℕ} {B : Finset (ℕ × ℕ)} (v : ↥B → K) : MvPolynomial (Fin 3) K :=
  ∑ j : ↥B, MvPolynomial.monomial (veroneseExp s j.val) (v j)

theorem dualPolyOfVec_isHomogeneous {s : ℕ} {B : Finset (ℕ × ℕ)}
    (hB : B ⊆ monomials s) (v : ↥B → K) :
    (dualPolyOfVec (s := s) v).IsHomogeneous s := by
  unfold dualPolyOfVec
  rw [← mem_homogeneousSubmodule]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [mem_homogeneousSubmodule]
  have hj := (mem_monomials_iff s j.val).mp (hB j.property)
  refine isHomogeneous_monomial_of_sum _ _ _ ?_
  rw [m3_sum]
  simp [veroneseExp]
  omega

theorem dualPolyOfVec_coeff {s : ℕ} {B : Finset (ℕ × ℕ)} (hB : B ⊆ monomials s)
    (v : ↥B → K) (ij : ℕ × ℕ) (hij : ij ∈ monomials s) :
    (dualPolyOfVec (s := s) v).coeff (veroneseExp s ij) =
      if h : ij ∈ B then v ⟨ij, h⟩ else 0 := by
  classical
  unfold dualPolyOfVec
  rw [MvPolynomial.coeff_sum]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨ij, h⟩]
    · simp
    · intro j _ hj
      rw [MvPolynomial.coeff_monomial]
      split_ifs with heq
      · exfalso; exact hj (Subtype.ext (veroneseExp_injOn s (hB j.property) hij heq))
      · rfl
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  · apply Finset.sum_eq_zero
    intro j _
    rw [MvPolynomial.coeff_monomial]
    split_ifs with heq
    · exfalso
      have := veroneseExp_injOn s (hB j.property) hij heq
      exact h (this ▸ j.property)
    · rfl

theorem dualPolyOfVec_ne_zero {s : ℕ} {B : Finset (ℕ × ℕ)} (hB : B ⊆ monomials s)
    {v : ↥B → K} (hv : v ≠ 0) :
    dualPolyOfVec (s := s) v ≠ 0 := by
  intro h0
  apply hv; ext j
  have hc := congrArg (fun p : MvPolynomial (Fin 3) K => p.coeff (veroneseExp s j.val)) h0
  simp [dualPolyOfVec_coeff hB v j.val (hB j.property), j.property] at hc
  exact hc

theorem eval_dualPolyOfVec {s : ℕ} {B : Finset (ℕ × ℕ)} (v : ↥B → K) (H R V : K) :
    MvPolynomial.eval ![H, R, V] (dualPolyOfVec (s := s) v) =
      ∑ j : ↥B, v j * TangentVeronesePacking.monomial s j.val H R V := by
  unfold dualPolyOfVec
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
  simp [veroneseExp, TangentVeronesePacking.monomial]

/-- **Fixed rich-head linear independence**: any `p ≤ s + 1` distinct affine points in `K × K`
(even if collinear!) have `K`-linearly independent degree-`s` Veronese rows (and remain linearly
independent under nonzero homogeneous scaling of each point). -/
theorem fixed_rows_linearIndependent {p s : ℕ} (hps : p ≤ s + 1)
    (H R V : Fin p → K) (hH : ∀ r, H r ≠ 0)
    (hinj : Function.Injective fun r : Fin p => (R r / H r, V r / H r)) :
    LinearIndependent K (fun (r : Fin p) (j : ↥(monomials s)) =>
      monomial s j.val (H r) (R r) (V r)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc r₀
  let pt : Fin p → K × K := fun r => (R r / H r, V r / H r)
  -- For each `r ≠ r₀`, choose an affine linear form `L r` vanishing at `pt r` and nonzero at `pt r₀`.
  let L : Fin p → MvPolynomial (Fin 2) K := fun r =>
    if (pt r).1 ≠ (pt r₀).1 then MvPolynomial.X 0 - MvPolynomial.C (pt r).1
    else MvPolynomial.X 1 - MvPolynomial.C (pt r).2
  have hL_deg (r : Fin p) : (L r).totalDegree ≤ 1 := by
    dsimp only [L]
    split_ifs
    · exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) (by simp))
    · exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) (by simp))
  have hL_zero (r : Fin p) : MvPolynomial.eval ![(pt r).1, (pt r).2] (L r) = 0 := by
    dsimp only [L]; split_ifs <;> simp
  have hL_ne (r : Fin p) (hr : r ≠ r₀) : MvPolynomial.eval ![(pt r₀).1, (pt r₀).2] (L r) ≠ 0 := by
    dsimp only [L]
    split_ifs with h1
    · simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.cons_val_zero]
      exact sub_ne_zero.mpr (Ne.symm h1)
    · push Not at h1
      have h2 : (pt r).2 ≠ (pt r₀).2 := by
        intro h2; exact hr (hinj (Prod.ext h1 h2))
      simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      exact sub_ne_zero.mpr (Ne.symm h2)
  let g : MvPolynomial (Fin 2) K := ∏ r ∈ Finset.univ.erase r₀, L r
  have hg_deg : g.totalDegree ≤ s := by
    have h1 : g.totalDegree ≤ ∑ r ∈ Finset.univ.erase r₀, (L r).totalDegree :=
      MvPolynomial.totalDegree_finsetProd (Finset.univ.erase r₀) L
    have h2 : ∑ r ∈ Finset.univ.erase r₀, (L r).totalDegree ≤ (Finset.univ.erase r₀).card := by
      calc ∑ r ∈ Finset.univ.erase r₀, (L r).totalDegree
          ≤ ∑ _r ∈ Finset.univ.erase r₀, 1 := Finset.sum_le_sum fun r _ => hL_deg r
        _ = (Finset.univ.erase r₀).card := by simp
    have hcard : (Finset.univ.erase r₀).card = p - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ r₀), Finset.card_univ, Fintype.card_fin]
    omega
  have hg_eval_sum (r : Fin p) :
      (H r) ^ s * MvPolynomial.eval ![(pt r).1, (pt r).2] g =
        ∑ j : ↥(monomials s),
          g.coeff (Finsupp.single 0 j.val.1 + Finsupp.single 1 j.val.2) *
            TangentVeronesePacking.monomial s j.val (H r) (R r) (V r) := by
    rw [MvPolynomial.eval_eq', Finset.mul_sum]
    have hsub : g.support ⊆ (monomials s).image (fun ij => Finsupp.single 0 ij.1 + Finsupp.single 1 ij.2) := by
      intro e he
      have hedeg : e 0 + e 1 ≤ s := by
        have := (Finset.le_sup (f := fun t : Fin 2 →₀ ℕ => t.sum fun _ v => v) he).trans hg_deg
        rwa [m2_sum] at this
      refine Finset.mem_image.mpr ⟨(e 0, e 1), (mem_monomials_iff s (e 0, e 1)).mpr hedeg, ?_⟩
      ext k; fin_cases k <;> simp
    rw [Finset.sum_subset hsub (fun e _ hnot => by rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul, mul_zero])]
    rw [Finset.sum_image]
    · rw [← (monomials s).sum_coe_sort]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj := (mem_monomials_iff s j.val).mp j.property
      rw [Fin.prod_univ_two]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
        add_zero, zero_add, Matrix.cons_val_zero, Matrix.cons_val_one,
        pt, TangentVeronesePacking.monomial, div_pow]
      have hHpow : H r ^ s = H r ^ (s - (j.val.1 + j.val.2)) * H r ^ j.val.1 * H r ^ j.val.2 := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [hHpow]
      have h1 : H r ^ j.val.1 ≠ 0 := pow_ne_zero _ (hH r)
      have h2 : H r ^ j.val.2 ≠ 0 := pow_ne_zero _ (hH r)
      rw [div_mul_div_comm, ← mul_div_assoc, ← mul_div_assoc, div_eq_iff (mul_ne_zero h1 h2)]
      ring
    · intro a _ b _ hab
      have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hab
      have h2 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hab
      simp only [Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
        add_zero, zero_add] at h1 h2
      exact Prod.ext h1 h2
  have hsum0 : ∑ r : Fin p, c r * ((H r) ^ s * MvPolynomial.eval ![(pt r).1, (pt r).2] g) = 0 := by
    simp_rw [hg_eval_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    have hcj := congrFun hc j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcj
    calc ∑ r : Fin p, c r * (g.coeff (Finsupp.single 0 j.val.1 + Finsupp.single 1 j.val.2) *
            monomial s j.val (H r) (R r) (V r))
        = g.coeff (Finsupp.single 0 j.val.1 + Finsupp.single 1 j.val.2) *
            ∑ r : Fin p, c r * monomial s j.val (H r) (R r) (V r) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => by ring
      _ = 0 := by rw [hcj, mul_zero]
  rw [Finset.sum_eq_single r₀] at hsum0
  · have hg_r₀ : MvPolynomial.eval ![(pt r₀).1, (pt r₀).2] g ≠ 0 := by
      dsimp only [g]; rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr fun r hr => hL_ne r (Finset.ne_of_mem_erase hr)
    exact (mul_eq_zero.mp hsum0).resolve_right (mul_ne_zero (pow_ne_zero s (hH r₀)) hg_r₀)
  · intro r _ hrr₀
    have hgr : MvPolynomial.eval ![(pt r).1, (pt r).2] g = 0 := by
      dsimp only [g]; rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hrr₀, Finset.mem_univ r⟩) (hL_zero r)
    rw [hgr, mul_zero, mul_zero]
  · intro hnot; exact absurd (Finset.mem_univ r₀) hnot

/-- Canonical equivalence `↥B ≃ Fin B.card` for a finite set `B`. -/
def finEquiv {α : Type*} (B : Finset α) : ↥B ≃ Fin B.card :=
  Fintype.equivFinOfCardEq (Fintype.card_coe B)

/-- Helper: stacking `p` fixed rows and `k` candidate rows of length `B.card`. -/
def stackRows {β : Type*} {p k : ℕ} (fixed : Fin p → β) (cand : Fin k → β) :
    Fin (p + k) → β :=
  Fin.append fixed cand

/-- **Vanishing-minor dual curve extraction**:
Given `B ⊆ monomials s`, `p ≤ B.card` linearly independent fixed rows, and a finite set `T` of
candidate rows `(H i, R i, V i)` such that EVERY `B.card × B.card` matrix formed by stacking the
`p` fixed rows and `B.card - p` rows from `T` has determinant `0`, there exists a nonzero
homogeneous degree-`s` polynomial `Q : MvPolynomial (Fin 3) K` supported on `B` vanishing at
`(H i, R i, V i)` for every `i ∈ T`. -/
theorem exists_dual_curve_of_vanishing_minors {ι : Type*} {s p : ℕ}
    (B : Finset (ℕ × ℕ)) (hB : B ⊆ monomials s) (hp : p ≤ B.card)
    (fixed : Fin p → ↥B → K) (hfixed : LinearIndependent K fixed)
    (T : Finset ι) (H R V : ι → K)
    (hdet : ∀ f : Fin (B.card - p) → ι, (∀ k, f k ∈ T) →
      (Matrix.of (fun (row : Fin B.card) (col : Fin B.card) =>
        stackRows fixed (fun k j => TangentVeronesePacking.monomial s j.val (H (f k)) (R (f k)) (V (f k)))
          (Fin.cast (Nat.add_sub_of_le hp).symm row)
          ((finEquiv B).symm col))).det = 0) :
    ∃ Q : MvPolynomial (Fin 3) K, Q.IsHomogeneous s ∧ Q ≠ 0 ∧
      (∀ ij ∈ monomials s, ij ∉ B → Q.coeff (veroneseExp s ij) = 0) ∧
      (∀ i ∈ T, MvPolynomial.eval ![H i, R i, V i] Q = 0) := by
  classical
  let h := B.card
  let cand : ι → (↥B → K) := fun i j => monomial s j.val (H i) (R i) (V i)
  let W : Submodule K (↥B → K) := Submodule.span K (Set.range fixed ∪ cand '' (T : Set ι))
  have hdim_lt : Module.finrank K W < h := by
    by_contra hge
    have hdim_top : Module.finrank K W = h := by
      apply le_antisymm
      · exact (Submodule.finrank_le W).trans (by simp [h])
      · omega
    -- By induction on `k ≤ h - p`, pick `k` rows from `T` extending `fixed` linearly independently.
    have hext : ∀ k : ℕ, k ≤ h - p →
        ∃ f : Fin k → ι, (∀ t, f t ∈ T) ∧ LinearIndependent K (stackRows fixed (cand ∘ f)) := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨Fin.elim0, fun t => Fin.elim0 t, ?_⟩
        rw [Fintype.linearIndependent_iff]
        intro c hc i
        have hi : i.val < p := by omega
        have hli := Fintype.linearIndependent_iff.mp hfixed (fun r => c (Fin.castAdd 0 r))
        have hsum : ∑ r : Fin p, c (Fin.castAdd 0 r) • fixed r = 0 := by
          rw [← hc]
          exact Fintype.sum_equiv (finCongr (Nat.add_zero p)).symm
            (fun r => c (Fin.castAdd 0 r) • fixed r)
            (fun i => c i • stackRows fixed (cand ∘ Fin.elim0) i) fun r => by
              have hr : (finCongr (Nat.add_zero p)).symm r = Fin.castAdd 0 r := Fin.ext rfl
              rw [hr]; simp only [stackRows, Fin.append_left]
        have := hli hsum ⟨i.val, hi⟩
        simpa [Fin.ext_iff] using this
      | succ k ih =>
        intro hk
        obtain ⟨f, hfT, hfli⟩ := ih (by omega)
        let U : Submodule K (↥B → K) := Submodule.span K (Set.range (stackRows fixed (cand ∘ f)))
        have hU_dim : Module.finrank K U ≤ p + k := by
          have h1 := finrank_span_le_card (R := K) (Set.range (stackRows fixed (cand ∘ f)))
          rw [Set.toFinset_card] at h1
          have h2 : Fintype.card (Set.range (stackRows fixed (cand ∘ f))) ≤ p + k := by
            simpa [Fintype.card_fin] using Fintype.card_range_le (stackRows fixed (cand ∘ f))
          exact h1.trans h2
        have hnot_le : ¬ W ≤ U := by
          intro hle
          have h1 := Submodule.finrank_mono hle
          omega
        have hex_i : ∃ i ∈ T, cand i ∉ U := by
          by_contra hall; push Not at hall
          apply hnot_le
          rw [Submodule.span_le]
          rintro x (⟨r, rfl⟩ | ⟨i, hiT, rfl⟩)
          · exact Submodule.subset_span ⟨Fin.castAdd k r, by simp [stackRows]⟩
          · exact hall i hiT
        obtain ⟨i₀, hi₀T, hi₀U⟩ := hex_i
        let f' : Fin (k + 1) → ι := Fin.snoc f i₀
        refine ⟨f', fun t => ?_, ?_⟩
        · refine Fin.lastCases ?_ ?_ t
          · simpa [f'] using hi₀T
          · intro j; simpa [f'] using hfT j
        · rw [Fintype.linearIndependent_iff]
          intro c hc
          have hlast_eq : stackRows fixed (cand ∘ f') (Fin.last (p + k)) = cand i₀ := by
            dsimp only [stackRows, f']
            have h1 : Fin.last (p + k) = Fin.natAdd p (Fin.last k) := by
              ext; simp [Fin.last, Fin.natAdd]
            rw [h1, Fin.append_right]
            simp [Function.comp]
          have hinit_eq (t : Fin (p + k)) :
              stackRows fixed (cand ∘ f') t.castSucc = stackRows fixed (cand ∘ f) t := by
            dsimp only [stackRows, f']
            by_cases ht : t.val < p
            · have h1 : t = Fin.castAdd k ⟨t.val, ht⟩ := Fin.ext rfl
              have h2 : t.castSucc = Fin.castAdd (k + 1) ⟨t.val, ht⟩ := Fin.ext rfl
              conv_lhs => rw [h2]
              conv_rhs => rw [h1]
              rw [Fin.append_left, Fin.append_left]
            · have ht1 : t.val - p < k := by have := t.isLt; omega
              have ht2 : t.val - p < k + 1 := by omega
              have h1 : t = Fin.natAdd p ⟨t.val - p, ht1⟩ := Fin.ext (by simp; omega)
              have h2 : t.castSucc = Fin.natAdd p ⟨t.val - p, ht2⟩ := Fin.ext (by simp; omega)
              conv_lhs => rw [h2]
              conv_rhs => rw [h1]
              rw [Fin.append_right, Fin.append_right]
              simp only [Function.comp_apply]
              have h3 : (⟨t.val - p, ht2⟩ : Fin (k + 1)) = (⟨t.val - p, ht1⟩ : Fin k).castSucc := rfl
              rw [h3, Fin.snoc_castSucc]
          change ∑ i : Fin ((p + k) + 1), c i • stackRows fixed (cand ∘ f') i = 0 at hc
          rw [Fin.sum_univ_castSucc, hlast_eq] at hc
          have hclast : c (Fin.last (p + k)) = 0 := by
            by_contra hne
            apply hi₀U
            have hmem : -(c (Fin.last (p + k)))⁻¹ •
                (∑ t : Fin (p + k), c t.castSucc • stackRows fixed (cand ∘ f) t) ∈ U :=
              Submodule.smul_mem U _ (Submodule.sum_mem U fun t _ =>
                Submodule.smul_mem U _ (Submodule.subset_span ⟨t, rfl⟩))
            have heq : cand i₀ = -(c (Fin.last (p + k)))⁻¹ •
                (∑ t : Fin (p + k), c t.castSucc • stackRows fixed (cand ∘ f) t) := by
              have hsub : c (Fin.last (p + k)) • cand i₀ =
                  -(∑ t : Fin (p + k), c t.castSucc • stackRows fixed (cand ∘ f) t) := by
                have hhc : (∑ t : Fin (p + k), c t.castSucc • stackRows fixed (cand ∘ f) t) +
                    c (Fin.last (p + k)) • cand i₀ = 0 := by
                  simpa [hinit_eq] using hc
                exact eq_neg_of_add_eq_zero_right hhc
              calc cand i₀ = (c (Fin.last (p + k)))⁻¹ • (c (Fin.last (p + k)) • cand i₀) := by
                    rw [inv_smul_smul₀ hne]
                _ = (c (Fin.last (p + k)))⁻¹ •
                      -(∑ t : Fin (p + k), c t.castSucc • stackRows fixed (cand ∘ f) t) := by
                    rw [hsub]
                _ = -(c (Fin.last (p + k)))⁻¹ •
                      (∑ t : Fin (p + k), c t.castSucc • stackRows fixed (cand ∘ f) t) := by
                    rw [smul_neg, neg_smul]
            exact heq ▸ hmem
          have hsum0 : ∑ t : Fin (p + k), c t.castSucc • stackRows fixed (cand ∘ f) t = 0 := by
            simpa [hclast, hinit_eq] using hc
          have hcinit := Fintype.linearIndependent_iff.mp hfli (fun t => c t.castSucc) hsum0
          intro t
          refine Fin.lastCases ?_ ?_ t
          · exact hclast
          · exact hcinit
    obtain ⟨f, hfT, hfli⟩ := hext (h - p) le_rfl
    let M : Matrix (Fin h) (Fin h) K := Matrix.of fun row col =>
      stackRows fixed (cand ∘ f) (Fin.cast (Nat.add_sub_of_le hp).symm row)
        ((finEquiv B).symm col)
    have hM_det0 : M.det = 0 := hdet f hfT
    have hMT_det0 : M.transpose.det = 0 := by rw [Matrix.det_transpose, hM_det0]
    obtain ⟨w, hw_ne, hw_mul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hMT_det0
    -- `Mᵀ.mulVec w = 0` means `∑ row, w row • stackRows ... = 0`, contradicting `hfli`!
    let c : Fin (p + (h - p)) → K := fun r => w (Fin.cast (Nat.add_sub_of_le hp) r)
    have hc_sum : ∑ r : Fin (p + (h - p)), c r • stackRows fixed (cand ∘ f) r = 0 := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hj := congrFun hw_mul (finEquiv B j)
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, M, Matrix.of_apply,
        Equiv.symm_apply_apply, Pi.zero_apply] at hj
      rw [← hj]
      refine Fintype.sum_equiv (finCongr (Nat.add_sub_of_le hp)) _ _ fun r => ?_
      simp [c, mul_comm]
    have hc0 := Fintype.linearIndependent_iff.mp hfli c hc_sum
    apply hw_ne; ext row
    have := hc0 (Fin.cast (Nat.add_sub_of_le hp).symm row)
    simpa [c] using this
  -- Since `finrank K W < h = finrank K (↥B → K)`, pick a basis of `W` and find a nonzero `v`
  -- in the kernel of evaluation against that basis.
  let bW := Module.finBasis K W
  let ev : (↥B → K) →ₗ[K] (Fin (Module.finrank K W) → K) :=
    { toFun := fun v r => ∑ j : ↥B, v j * (bW r).val j
      map_add' := fun u v => by ext r; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun a v => by ext r; simp [mul_assoc, Finset.mul_sum] }
  have hker_ne : LinearMap.ker ev ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective ev := LinearMap.ker_eq_bot.mp hbot
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hdom : Module.finrank K (↥B → K) = h := by simp [h]
    have hcod : Module.finrank K (Fin (Module.finrank K W) → K) = Module.finrank K W := by simp
    omega
  obtain ⟨v, hv_ker, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  have hv_orth_W : ∀ w : W, ∑ j : ↥B, v j * w.val j = 0 := by
    intro w
    have hlin : ∑ j : ↥B, v j * w.val j =
        ∑ r : Fin (Module.finrank K W), bW.repr w r * ∑ j : ↥B, v j * (bW r).val j := by
      have hw : w.val = ∑ r : Fin (Module.finrank K W), bW.repr w r • (bW r).val := by
        have h1 : w = ∑ r : Fin (Module.finrank K W), bW.repr w r • bW r := (bW.sum_repr w).symm
        have h2 := congrArg Subtype.val h1
        rw [AddSubmonoidClass.coe_finsetSum] at h2
        simpa only [SetLike.val_smul] using h2
      conv_lhs => rw [hw]
      simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hlin]
    apply Finset.sum_eq_zero
    intro r _
    have hr : ev v r = 0 := congrFun (LinearMap.mem_ker.mp hv_ker) r
    change ∑ j : ↥B, v j * (bW r).val j = 0 at hr
    rw [hr, mul_zero]
  refine ⟨dualPolyOfVec (s := s) v, dualPolyOfVec_isHomogeneous hB v,
    dualPolyOfVec_ne_zero hB hv_ne, ?_, ?_⟩
  · intro ij hij hnot
    simp [dualPolyOfVec_coeff hB v ij hij, hnot]
  · intro i hiT
    rw [eval_dualPolyOfVec]
    have hmem : cand i ∈ W := Submodule.subset_span (Or.inr ⟨i, hiT, rfl⟩)
    exact hv_orth_W ⟨cand i, hmem⟩

end LinearAlgebra

section DownwardClosedPacking

variable {K I : Type*} [Field K] [Fintype I]

/-- Translation coefficient matching `TangentVeronesePacking.translate_row`. -/
private def transCoeff {R : Type*} [CommRing R] (u v : R) (ab ij : ℕ × ℕ) : R :=
  if ij.1 ≤ ab.1 ∧ ij.2 ≤ ab.2 then
    u ^ (ab.1 - ij.1) * v ^ (ab.2 - ij.2) * (ab.1.choose ij.1) * (ab.2.choose ij.2)
  else 0

/-- Row translation identity over ANY downward-closed subset `B ⊆ monomials s`. -/
private theorem translate_row_subset {R : Type*} [CommRing R] {s : ℕ}
    (B : Finset (ℕ × ℕ)) (hB : B ⊆ monomials s)
    (hdown : ∀ ab ∈ B, ∀ ij : ℕ × ℕ, ij.1 ≤ ab.1 → ij.2 ≤ ab.2 → ij ∈ B)
    (ab : ℕ × ℕ) (hab : ab ∈ B) (h x y u v : R) :
    monomial s ab h x y =
      ∑ ij ∈ B, monomial s ij h (x - u * h) (y - v * h) * transCoeff u v ab ij := by
  classical
  have hab_deg : ab.1 + ab.2 ≤ s := (mem_monomials_iff s ab).mp (hB hab)
  let T := Finset.range (ab.1 + 1) ×ˢ Finset.range (ab.2 + 1)
  have hsub : T ⊆ B := by
    rintro ⟨i, j⟩ hij
    simp only [T, Finset.mem_product, Finset.mem_range] at hij
    exact hdown ab hab (i, j) (by omega) (by omega)
  rw [← Finset.sum_subset hsub (fun ij _ hn => by
    rcases ij with ⟨i, j⟩
    simp only [T, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hn
    simp [transCoeff, hn])]
  rw [Finset.sum_product]
  calc TangentVeronesePacking.monomial s ab h x y
      = h ^ (s - (ab.1 + ab.2)) * ((x - u * h) + u * h) ^ ab.1 *
          ((y - v * h) + v * h) ^ ab.2 := by simp [TangentVeronesePacking.monomial]
    _ = ∑ i ∈ Finset.range (ab.1 + 1), ∑ j ∈ Finset.range (ab.2 + 1),
          TangentVeronesePacking.monomial s (i, j) h (x - u * h) (y - v * h) * transCoeff u v ab (i, j) := by
        rw [add_pow, add_pow, Finset.mul_sum (Finset.range (ab.1 + 1)), Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have ha : i ≤ ab.1 := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
        have hb : j ≤ ab.2 := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
        have powH : h ^ (s - (i + j)) = h ^ (s - (ab.1 + ab.2)) * h ^ (ab.1 - i) * h ^ (ab.2 - j) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        simp only [TangentVeronesePacking.monomial, transCoeff, ha, hb, and_self, ite_true, mul_pow]
        rw [powH]; ring

/-- Determinant incidence bound over any downward-closed column subset `B ⊆ monomials s`,
indexed by `Fin B.card` for direct composition with `exists_dual_curve_of_vanishing_minors`. -/
theorem downward_closed_incidence {s d a : ℕ}
    (B : Finset (ℕ × ℕ)) (hB : B ⊆ monomials s)
    (hdown : ∀ ab ∈ B, ∀ ij : ℕ × ℕ, ij.1 ≤ ab.1 → ij.2 ≤ ab.2 → ij ∈ B)
    (dom : I ↪ K) (u v : I → K)
    (H R V : Fin B.card → K[X]) (c : Fin B.card → ℕ)
    (hd : ∀ i, (H i).natDegree ≤ c i ∧ (R i).natDegree ≤ d + c i ∧ (V i).natDegree ≤ d + c i)
    (hn : (Matrix.of (fun row col : Fin B.card =>
      TangentVeronesePacking.monomial s ((finEquiv B).symm col).val (H row) (R row) (V row))).det ≠ 0)
    (S : Fin B.card → Finset I)
    (hs : ∀ i, ∀ z ∈ S i, (R i).eval (dom z) = u z * (H i).eval (dom z) ∧
      (V i).eval (dom z) = v z * (H i).eval (dom z)) :
    a * (∑ i : Fin B.card, (S i).card) ≤
      Fintype.card I * (∑ ij ∈ B, (a - (ij.1 + ij.2))) +
        (∑ i : Fin B.card, s * c i) + (∑ ij ∈ B, (ij.1 + ij.2)) * d := by
  classical
  let eB : ↥B ≃ Fin B.card := finEquiv B
  let colOf : Fin B.card → ℕ × ℕ := fun col => (eB.symm col).val
  let M : Matrix (Fin B.card) (Fin B.card) K[X] :=
    Matrix.of fun i j => TangentVeronesePacking.monomial s (colOf j) (H i) (R i) (V i)
  let L : I → Matrix (Fin B.card) (Fin B.card) K[X] := fun z =>
    Matrix.of fun i j => TangentVeronesePacking.monomial s (colOf j) (H i) (R i - Polynomial.C (u z) * H i)
      (V i - Polynomial.C (v z) * H i)
  let Bm : I → Matrix (Fin B.card) (Fin B.card) K[X] := fun z =>
    Matrix.of fun i j => transCoeff (Polynomial.C (u z)) (Polynomial.C (v z)) (colOf j) (colOf i)
  let Ssite : I → Finset (Fin B.card) := fun z => Finset.univ.filter fun i => z ∈ S i
  have hswap : ∑ z : I, (Ssite z).card = ∑ i : Fin B.card, (S i).card := by
    simp only [Ssite, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have hinc := TangentVeronesePacking.incidence dom M hn
    (fun j => (colOf j).1 + (colOf j).2) (fun i => s * c i) d a
    (by
      intro i j
      have hj := (mem_monomials_iff s (colOf j)).mp (hB (eB.symm j).property)
      have hhi := (hd i).1
      have hri := (hd i).2.1
      have hvi := (hd i).2.2
      change (TangentVeronesePacking.monomial s (colOf j) (H i) (R i) (V i)).natDegree ≤ _
      unfold TangentVeronesePacking.monomial
      have h1 := Polynomial.natDegree_mul_le (p := H i ^ (s - ((colOf j).1 + (colOf j).2)) * R i ^ (colOf j).1)
        (q := V i ^ (colOf j).2)
      have h2 := Polynomial.natDegree_mul_le (p := H i ^ (s - ((colOf j).1 + (colOf j).2)))
        (q := R i ^ (colOf j).1)
      have hp1 := (Polynomial.natDegree_pow_le (p := H i) (n := s - ((colOf j).1 + (colOf j).2))).trans
        (Nat.mul_le_mul_left _ hhi)
      have hp2 := (Polynomial.natDegree_pow_le (p := R i) (n := (colOf j).1)).trans
        (Nat.mul_le_mul_left _ hri)
      have hp3 := (Polynomial.natDegree_pow_le (p := V i) (n := (colOf j).2)).trans
        (Nat.mul_le_mul_left _ hvi)
      have hlin : (s - ((colOf j).1 + (colOf j).2)) * c i +
          (colOf j).1 * (d + c i) + (colOf j).2 * (d + c i) =
          s * c i + ((colOf j).1 + (colOf j).2) * d := by
        have hsub : (s - ((colOf j).1 + (colOf j).2)) * c i + ((colOf j).1 + (colOf j).2) * c i = s * c i := by
          rw [← add_mul, Nat.sub_add_cancel hj]
        linarith
      omega)
    Ssite L Bm
    (by
      intro z
      apply Matrix.ext; intro i j
      change TangentVeronesePacking.monomial s (colOf j) (H i) (R i) (V i) = (L z * Bm z) i j
      rw [Matrix.mul_apply]
      rw [translate_row_subset B hB hdown (colOf j) (eB.symm j).property
        (H i) (R i) (V i) (Polynomial.C (u z)) (Polynomial.C (v z))]
      rw [← B.sum_coe_sort]
      exact Fintype.sum_equiv eB _ _ fun x => by simp [L, Bm, colOf])
    (by
      intro z i hi j
      have hzi : z ∈ S i := (Finset.mem_filter.mp hi).2
      obtain ⟨hR0, hV0⟩ := hs i z hzi
      have hdR : (Polynomial.X - Polynomial.C (dom z)) ∣ (R i - Polynomial.C (u z) * H i) :=
        Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot, hR0])
      have hdV : (Polynomial.X - Polynomial.C (dom z)) ∣ (V i - Polynomial.C (v z) * H i) :=
        Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot, hV0])
      change (Polynomial.X - Polynomial.C (dom z)) ^ ((colOf j).1 + (colOf j).2) ∣
        H i ^ (s - ((colOf j).1 + (colOf j).2)) *
          (R i - Polynomial.C (u z) * H i) ^ (colOf j).1 *
          (V i - Polynomial.C (v z) * H i) ^ (colOf j).2
      rw [pow_add, mul_assoc]
      exact dvd_mul_of_dvd_right (mul_dvd_mul (pow_dvd_pow_of_dvd hdR _) (pow_dvd_pow_of_dvd hdV _)) _)
  have hsum1 : ∑ j : Fin B.card, (a - ((colOf j).1 + (colOf j).2)) =
      ∑ ij ∈ B, (a - (ij.1 + ij.2)) := by
    rw [← B.sum_coe_sort]
    exact (Fintype.sum_equiv eB _ _ fun x => by simp [colOf]).symm
  have hsum2 : ∑ j : Fin B.card, ((colOf j).1 + (colOf j).2) = ∑ ij ∈ B, (ij.1 + ij.2) := by
    rw [← B.sum_coe_sort]
    exact (Fintype.sum_equiv eB _ _ fun x => by simp [colOf]).symm
  rw [hswap, hsum1, hsum2] at hinc
  exact hinc

/-- Elementary Markov count for expensive rows. -/
private theorem markov_expensive_card_le {α : Type*} (T : Finset α) (cost : α → ℕ)
    {k D' budget : ℕ} (hD' : 0 < D') (hbud : ∑ i ∈ T, cost i ≤ budget) :
    (T.filter fun i => D' ≤ k * cost i).card ≤ k * budget / D' := by
  classical
  let Texp := T.filter fun i => D' ≤ k * cost i
  have h1 : Texp.card * D' ≤ ∑ i ∈ Texp, k * cost i := by
    calc Texp.card * D' = ∑ _i ∈ Texp, D' := by simp
      _ ≤ ∑ i ∈ Texp, k * cost i := Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2
  have h2 : ∑ i ∈ Texp, k * cost i ≤ k * budget := by
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left k ((Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hbud)
  exact (Nat.le_div_iff_mul_le hD').mpr (h1.trans h2)

end DownwardClosedPacking

section MainPolarCaps

/-- **Unified Veronese Polar Cap with `0 ≤ p ≤ s + 1` Fixed Rich-Head Rows (L2d)**:
Combines Markov expensive-row discarding, `TangentVeronesePacking` determinant incidence,
`fixed_rows_linearIndependent`, `exists_dual_curve_of_vanishing_minors`, and L2a–c
(`PlanePolarCap.polar_affine_card_le`) over `L = FractionRing K[X]`.

Covers `TangentPolarWindows` (`p = 0`), `HalfCoreWeightedJets` (`p ≤ s + 1`),
`QuarterCommonFactorDegrees`, and `HalfSparseGaussWindow`. -/
theorem veronese_polar_cap {K I α : Type*} [Field K] [Fintype I]
    {s a p m b d t D' C₀ R₀ : ℕ}
    (has : a ≤ s) (hps : p ≤ s + 1) (hp_lt : p < (s + 2).choose 2)
    (hm : 2 ≤ m) (hbm : b ≤ m) (hms : s * (s - 1) < m)
    (hchar : ∀ k : ℕ, 0 < k → k ≤ m * (m - 1) → (k : K) ≠ 0)
    (dom : I ↪ K) (u v : I → K)
    -- `p` fixed rich-head rows
    (H_fix R_fix V_fix : Fin p → K[X]) (c_fix loss_fix : Fin p → ℕ) (S_fix : Fin p → Finset I)
    (hH_fix_ne : ∀ r, H_fix r ≠ 0)
    (hfix_inj : Function.Injective fun r : Fin p =>
      (algebraMap K[X] (FractionRing K[X]) (R_fix r) / algebraMap K[X] (FractionRing K[X]) (H_fix r),
       algebraMap K[X] (FractionRing K[X]) (V_fix r) / algebraMap K[X] (FractionRing K[X]) (H_fix r)))
    (hfix_deg : ∀ r, (H_fix r).natDegree ≤ c_fix r ∧
      (R_fix r).natDegree ≤ d + c_fix r ∧ (V_fix r).natDegree ≤ d + c_fix r)
    (hfix_ag : ∀ r, ∀ z ∈ S_fix r,
      (R_fix r).eval (dom z) = u z * (H_fix r).eval (dom z) ∧
      (V_fix r).eval (dom z) = v z * (H_fix r).eval (dom z))
    (hfix_enough : ∀ r, t ≤ (S_fix r).card + loss_fix r)
    -- Geometrically irreducible curve `f` over `L = FractionRing K[X]`
    (f : (FractionRing K[X])[X][X])
    (hm_eq : (mv2EquivBiv.symm f).totalDegree = m)
    (hb : f.natDegree ≤ b)
    (hf_geom : Irreducible (mapBiv (algebraMap (FractionRing K[X]) (AlgebraicClosure (FractionRing K[X]))) f))
    -- Candidate tangent family `T` on `f = 0`
    (T : Finset α) (pt : α → FractionRing K[X] × FractionRing K[X])
    (hpt_inj : Set.InjOn pt (T : Set α))
    (hpt_on : ∀ i ∈ T, (f.map (evalRingHom (pt i).1)).eval (pt i).2 = 0)
    (H R V : α → K[X]) (c loss : α → ℕ) (S : α → Finset I)
    (hH_ne : ∀ i ∈ T, H i ≠ 0)
    (hdeg : ∀ i ∈ T, (H i).natDegree ≤ c i ∧ (R i).natDegree ≤ d + c i ∧ (V i).natDegree ≤ d + c i)
    (hag : ∀ i ∈ T, ∀ z ∈ S i,
      (R i).eval (dom z) = u z * (H i).eval (dom z) ∧
      (V i).eval (dom z) = v z * (H i).eval (dom z))
    (henough : ∀ i ∈ T, t ≤ (S i).card + loss i)
    (htan : ∀ i ∈ T,
      algebraMap K[X] (FractionRing K[X]) (H i) *
        MvPolynomial.eval ![(pt i).1, (pt i).2] (pderiv 0 (mv2EquivBiv.symm f)) +
      algebraMap K[X] (FractionRing K[X]) (V i) *
        MvPolynomial.eval ![(pt i).1, (pt i).2] (pderiv 1 (mv2EquivBiv.symm f)) = 0)
    (hR_eq : ∀ i ∈ T,
      algebraMap K[X] (FractionRing K[X]) (R i) =
        (pt i).2 * algebraMap K[X] (FractionRing K[X]) (H i) -
        (pt i).1 * algebraMap K[X] (FractionRing K[X]) (V i))
    (hC₀ : ∑ i ∈ T, c i ≤ C₀)
    (hR₀ : ∑ i ∈ T, loss i ≤ R₀)
    (hD'_pos : 0 < D')
    (hgap : (a + 2).choose 3 * Fintype.card I + (s * (s + 1) * (s + 2) / 3) * d +
      a * (∑ r : Fin p, loss_fix r) + s * (∑ r : Fin p, c_fix r) + D' ≤
      a * (s + 2).choose 2 * t) :
    T.card ≤ s * (m * (m - 1) - (m - b) * (m - b - 1)) +
      ((s + 2).choose 2 - p) * (a * R₀ + s * C₀) / D' := by
  classical
  let L := FractionRing K[X]
  let ι : K[X] →+* L := algebraMap K[X] L
  have hι_inj : Function.Injective ι := IsFractionRing.injective K[X] L
  let B := monomials s
  have hB_card : B.card = (s + 2).choose 2 := card_monomials s
  have hp_le : p ≤ B.card := by omega
  let k := B.card - p
  have hk_pos : 0 < k := by omega
  let cost : α → ℕ := fun i => a * loss i + s * c i
  have hcost_bud : ∑ i ∈ T, cost i ≤ a * R₀ + s * C₀ := by
    simp only [cost, Finset.sum_add_distrib, ← Finset.mul_sum]
    exact Nat.add_le_add (Nat.mul_le_mul_left a hR₀) (Nat.mul_le_mul_left s hC₀)
  let Texp := T.filter fun i => D' ≤ k * cost i
  let Tcheap := T.filter fun i => ¬ (D' ≤ k * cost i)
  have hcard_split : T.card = Tcheap.card + Texp.card := by
    rw [add_comm]
    exact (Finset.card_filter_add_card_filter_not (s := T) (p := fun i => D' ≤ k * cost i)).symm
  have hTexp_le : Texp.card ≤ k * (a * R₀ + s * C₀) / D' :=
    markov_expensive_card_le T cost hD'_pos hcost_bud
  -- Show every `B.card × B.card` minor stacking the `p` fixed rows and `k` rows from `Tcheap` vanishes!
  let fixedL : Fin p → ↥B → L := fun r j => TangentVeronesePacking.monomial s j.val (ι (H_fix r)) (ι (R_fix r)) (ι (V_fix r))
  have hfixed_li : LinearIndependent L fixedL :=
    fixed_rows_linearIndependent hps (fun r => ι (H_fix r)) (fun r => ι (R_fix r)) (fun r => ι (V_fix r))
      (fun r => (map_ne_zero_iff ι hι_inj).mpr (hH_fix_ne r)) hfix_inj
  have hdet_zero : ∀ g : Fin (B.card - p) → α, (∀ idx, g idx ∈ Tcheap) →
      (Matrix.of (fun (row : Fin B.card) (col : Fin B.card) =>
        stackRows fixedL (fun idx j => TangentVeronesePacking.monomial s j.val (ι (H (g idx))) (ι (R (g idx))) (ι (V (g idx))))
          (Fin.cast (Nat.add_sub_of_le hp_le).symm row)
          ((finEquiv B).symm col))).det = 0 := by
    intro g hg
    let Hrow : Fin B.card → K[X] := fun row =>
      stackRows H_fix (fun idx => H (g idx)) (Fin.cast (Nat.add_sub_of_le hp_le).symm row)
    let Rrow : Fin B.card → K[X] := fun row =>
      stackRows R_fix (fun idx => R (g idx)) (Fin.cast (Nat.add_sub_of_le hp_le).symm row)
    let Vrow : Fin B.card → K[X] := fun row =>
      stackRows V_fix (fun idx => V (g idx)) (Fin.cast (Nat.add_sub_of_le hp_le).symm row)
    let crow : Fin B.card → ℕ := fun row =>
      stackRows c_fix (fun idx => c (g idx)) (Fin.cast (Nat.add_sub_of_le hp_le).symm row)
    let lossrow : Fin B.card → ℕ := fun row =>
      stackRows loss_fix (fun idx => loss (g idx)) (Fin.cast (Nat.add_sub_of_le hp_le).symm row)
    let Srow : Fin B.card → Finset I := fun row =>
      stackRows S_fix (fun idx => S (g idx)) (Fin.cast (Nat.add_sub_of_le hp_le).symm row)
    let Mpoly : Matrix (Fin B.card) (Fin B.card) K[X] := Matrix.of fun row col =>
      TangentVeronesePacking.monomial s ((finEquiv B).symm col).val (Hrow row) (Rrow row) (Vrow row)
    have hM_map : Mpoly.map ι = Matrix.of (fun row col =>
        stackRows fixedL (fun idx j => TangentVeronesePacking.monomial s j.val (ι (H (g idx))) (ι (R (g idx))) (ι (V (g idx))))
          (Fin.cast (Nat.add_sub_of_le hp_le).symm row)
          ((finEquiv B).symm col)) := by
      apply Matrix.ext; intro row col
      simp only [Matrix.map_apply, Mpoly, Matrix.of_apply, Hrow, Rrow, Vrow]
      generalize Fin.cast (Nat.add_sub_of_le hp_le).symm row = r
      refine Fin.addCases (fun i => ?_) (fun j => ?_) r
      · simp [stackRows, fixedL, TangentVeronesePacking.monomial]
      · simp [stackRows, TangentVeronesePacking.monomial]
    rw [← hM_map]
    change (RingHom.mapMatrix ι Mpoly).det = 0
    rw [← RingHom.map_det]
    by_contra hdet_ne
    have hpoly_ne : Mpoly.det ≠ 0 := fun h0 => hdet_ne (by rw [h0, map_zero])
    have hinc := downward_closed_incidence (a := a) B Subset.rfl
      (fun ab hab ij h1 h2 => (mem_monomials_iff s ij).mpr (by have := (mem_monomials_iff s ab).mp hab; omega))
      dom u v Hrow Rrow Vrow crow
      (by
        intro row
        dsimp only [Hrow, Rrow, Vrow, crow]
        generalize Fin.cast (Nat.add_sub_of_le hp_le).symm row = r
        refine Fin.addCases (fun i => ?_) (fun j => ?_) r
        · simpa [stackRows] using hfix_deg i
        · simpa [stackRows] using hdeg (g j) (Finset.mem_filter.mp (hg j)).1)
      hpoly_ne Srow
      (by
        intro row z hz
        dsimp only [Rrow, Hrow, Vrow, Srow] at hz ⊢
        generalize Fin.cast (Nat.add_sub_of_le hp_le).symm row = r at hz ⊢
        refine Fin.addCases (fun i => ?_) (fun j => ?_) r hz
        · intro hz'; simpa [stackRows] using hfix_ag i z (by simpa [stackRows] using hz')
        · intro hz'; simpa [stackRows] using hag (g j) (Finset.mem_filter.mp (hg j)).1 z (by simpa [stackRows] using hz'))
    have hsum_enough : B.card * t ≤ (∑ row : Fin B.card, (Srow row).card) + ∑ row : Fin B.card, lossrow row := by
      rw [← Finset.sum_add_distrib]
      calc B.card * t = ∑ _row : Fin B.card, t := by simp
        _ ≤ ∑ row : Fin B.card, ((Srow row).card + lossrow row) := Finset.sum_le_sum fun row _ => by
            dsimp only [Srow, lossrow]
            generalize Fin.cast (Nat.add_sub_of_le hp_le).symm row = r
            refine Fin.addCases (fun i => ?_) (fun j => ?_) r
            · simpa [stackRows] using hfix_enough i
            · simpa [stackRows] using henough (g j) (Finset.mem_filter.mp (hg j)).1
    have hsum_c : ∑ row : Fin B.card, crow row = (∑ r : Fin p, c_fix r) + ∑ idx : Fin k, c (g idx) := by
      rw [Fintype.sum_equiv (finCongr (Nat.add_sub_of_le hp_le)).symm crow
        (fun r => stackRows c_fix (fun idx => c (g idx)) r) (fun _ => rfl)]
      rw [Fin.sum_univ_add]; simp [stackRows]; rfl
    have hsum_loss : ∑ row : Fin B.card, lossrow row =
        (∑ r : Fin p, loss_fix r) + ∑ idx : Fin k, loss (g idx) := by
      rw [Fintype.sum_equiv (finCongr (Nat.add_sub_of_le hp_le)).symm lossrow
        (fun r => stackRows loss_fix (fun idx => loss (g idx)) r) (fun _ => rfl)]
      rw [Fin.sum_univ_add]; simp [stackRows]; rfl
    have hcheap_sum : ∑ idx : Fin k, cost (g idx) < D' := by
      have hmul_lt : k * ∑ idx : Fin k, cost (g idx) < k * D' := by
        rw [Finset.mul_sum]
        calc ∑ idx : Fin k, k * cost (g idx)
            < ∑ _idx : Fin k, D' := Finset.sum_lt_sum_of_nonempty
                (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk_pos⟩⟩)
                (fun idx _ => lt_of_not_ge (Finset.mem_filter.mp (hg idx)).2)
          _ = k * D' := by simp [k]
      exact Nat.lt_of_mul_lt_mul_left hmul_lt
    have hcost_eq : ∑ idx : Fin k, cost (g idx) =
        a * (∑ idx : Fin k, loss (g idx)) + s * (∑ idx : Fin k, c (g idx)) := by
      simp only [cost, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_sub_weight_monomials s a has, sum_weight_monomials s, ← Finset.mul_sum] at hinc
    have hmul_en := Nat.mul_le_mul_left a hsum_enough
    rw [Nat.mul_add, ← mul_assoc] at hmul_en
    have hBt : a * B.card * t = a * (s + 2).choose 2 * t := by rw [hB_card]
    rw [hsum_c] at hinc
    rw [hsum_loss] at hmul_en
    have hring1 : a * (∑ r : Fin p, loss_fix r + ∑ idx : Fin k, loss (g idx)) =
        a * (∑ r : Fin p, loss_fix r) + a * (∑ idx : Fin k, loss (g idx)) := Nat.mul_add _ _ _
    have hring2 : s * (∑ r : Fin p, c_fix r + ∑ idx : Fin k, c (g idx)) =
        s * (∑ r : Fin p, c_fix r) + s * (∑ idx : Fin k, c (g idx)) := Nat.mul_add _ _ _
    have hring3 : Fintype.card I * (a + 2).choose 3 = (a + 2).choose 3 * Fintype.card I := mul_comm _ _
    omega
  -- Extract nonzero degree-`s` dual curve `Q : MvPolynomial (Fin 3) L` vanishing on `Tcheap`.
  obtain ⟨Q, hQ_hom, hQ_ne, _, hQ_van⟩ := exists_dual_curve_of_vanishing_minors B Subset.rfl hp_le
    fixedL hfixed_li Tcheap (fun i => ι (H i)) (fun i => ι (R i)) (fun i => ι (V i)) hdet_zero
  -- Map `Tcheap` injectively into `S_pts : Finset (L × L)` and apply `polar_affine_card_le`!
  let S_pts : Finset (L × L) := Tcheap.image pt
  have hS_card : S_pts.card = Tcheap.card :=
    Finset.card_image_of_injOn (hpt_inj.mono (Finset.filter_subset _ _))
  have hcharL : ∀ j : ℕ, 0 < j → j ≤ m * (m - 1) → (j : L) ≠ 0 := by
    intro j hj1 hj2 h0
    apply hchar j hj1 hj2
    have h1 : ι (Polynomial.C (j : K)) = 0 := by simpa [map_natCast] using h0
    exact Polynomial.C_eq_zero.mp ((map_eq_zero_iff ι hι_inj).mp h1)
  -- Define `H_pt, R_pt, V_pt : L × L → L` via the unique preimage in `Tcheap`.
  let H_pt : L × L → L := fun q => if h : ∃ i ∈ Tcheap, pt i = q then ι (H (Classical.choose h)) else 0
  let R_pt : L × L → L := fun q => if h : ∃ i ∈ Tcheap, pt i = q then ι (R (Classical.choose h)) else 0
  let V_pt : L × L → L := fun q => if h : ∃ i ∈ Tcheap, pt i = q then ι (V (Classical.choose h)) else 0
  have hH_pt (i : α) (hi : i ∈ Tcheap) : H_pt (pt i) = ι (H i) := by
    have hex : ∃ k ∈ Tcheap, pt k = pt i := ⟨i, hi, rfl⟩
    have heq : Classical.choose hex = i :=
      hpt_inj (Finset.mem_filter.mp (Classical.choose_spec hex).1).1
        (Finset.mem_filter.mp hi).1 (Classical.choose_spec hex).2
    simp only [H_pt, hex, ↓reduceDIte, heq]
  have hR_pt (i : α) (hi : i ∈ Tcheap) : R_pt (pt i) = ι (R i) := by
    have hex : ∃ k ∈ Tcheap, pt k = pt i := ⟨i, hi, rfl⟩
    have heq : Classical.choose hex = i :=
      hpt_inj (Finset.mem_filter.mp (Classical.choose_spec hex).1).1
        (Finset.mem_filter.mp hi).1 (Classical.choose_spec hex).2
    simp only [R_pt, hex, ↓reduceDIte, heq]
  have hV_pt (i : α) (hi : i ∈ Tcheap) : V_pt (pt i) = ι (V i) := by
    have hex : ∃ k ∈ Tcheap, pt k = pt i := ⟨i, hi, rfl⟩
    have heq : Classical.choose hex = i :=
      hpt_inj (Finset.mem_filter.mp (Classical.choose_spec hex).1).1
        (Finset.mem_filter.mp hi).1 (Classical.choose_spec hex).2
    simp only [V_pt, hex, ↓reduceDIte, heq]
  have hS_cap : S_pts.card ≤ s * (m * (m - 1) - (m - b) * (m - b - 1)) := by
    refine polar_affine_card_le f hm_eq hm hb hbm hf_geom hcharL Q hQ_hom hQ_ne hms S_pts
      (fun q hq => ?_) H_pt R_pt V_pt (fun q hq => ?_) (fun q hq => ?_) (fun q hq => ?_) (fun q hq => ?_)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact hpt_on i (Finset.mem_filter.mp hi).1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [hH_pt i hi]
      exact (map_ne_zero_iff ι hι_inj).mpr (hH_ne i (Finset.mem_filter.mp hi).1)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [hH_pt i hi, hV_pt i hi]
      exact htan i (Finset.mem_filter.mp hi).1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [hH_pt i hi, hR_pt i hi, hV_pt i hi]
      exact hR_eq i (Finset.mem_filter.mp hi).1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [hH_pt i hi, hR_pt i hi, hV_pt i hi]
      exact hQ_van i hi
  rw [hS_card] at hS_cap
  have hk_eq : k = (s + 2).choose 2 - p := by dsimp only [k]; rw [hB_card]
  rw [hk_eq] at hTexp_le
  omega

/-- Specialization of `veronese_polar_cap` to `p = 0` fixed rows (directly matching
`TangentPolarWindows.component`). -/
theorem veronese_polar_cap_p0 {K I α : Type*} [Field K] [Fintype I]
    {s a m b d t D' C₀ R₀ : ℕ}
    (has : a ≤ s) (hm : 2 ≤ m) (hbm : b ≤ m) (hms : s * (s - 1) < m)
    (hchar : ∀ k : ℕ, 0 < k → k ≤ m * (m - 1) → (k : K) ≠ 0)
    (dom : I ↪ K) (u v : I → K)
    (f : (FractionRing K[X])[X][X])
    (hm_eq : (mv2EquivBiv.symm f).totalDegree = m)
    (hb : f.natDegree ≤ b)
    (hf_geom : Irreducible (mapBiv (algebraMap (FractionRing K[X]) (AlgebraicClosure (FractionRing K[X]))) f))
    (T : Finset α) (pt : α → FractionRing K[X] × FractionRing K[X])
    (hpt_inj : Set.InjOn pt (T : Set α))
    (hpt_on : ∀ i ∈ T, (f.map (evalRingHom (pt i).1)).eval (pt i).2 = 0)
    (H R V : α → K[X]) (c loss : α → ℕ) (S : α → Finset I)
    (hH_ne : ∀ i ∈ T, H i ≠ 0)
    (hdeg : ∀ i ∈ T, (H i).natDegree ≤ c i ∧ (R i).natDegree ≤ d + c i ∧ (V i).natDegree ≤ d + c i)
    (hag : ∀ i ∈ T, ∀ z ∈ S i,
      (R i).eval (dom z) = u z * (H i).eval (dom z) ∧
      (V i).eval (dom z) = v z * (H i).eval (dom z))
    (henough : ∀ i ∈ T, t ≤ (S i).card + loss i)
    (htan : ∀ i ∈ T,
      algebraMap K[X] (FractionRing K[X]) (H i) *
        MvPolynomial.eval ![(pt i).1, (pt i).2] (pderiv 0 (mv2EquivBiv.symm f)) +
      algebraMap K[X] (FractionRing K[X]) (V i) *
        MvPolynomial.eval ![(pt i).1, (pt i).2] (pderiv 1 (mv2EquivBiv.symm f)) = 0)
    (hR_eq : ∀ i ∈ T,
      algebraMap K[X] (FractionRing K[X]) (R i) =
        (pt i).2 * algebraMap K[X] (FractionRing K[X]) (H i) -
        (pt i).1 * algebraMap K[X] (FractionRing K[X]) (V i))
    (hC₀ : ∑ i ∈ T, c i ≤ C₀)
    (hR₀ : ∑ i ∈ T, loss i ≤ R₀)
    (hD'_pos : 0 < D')
    (hgap : (a + 2).choose 3 * Fintype.card I + (s * (s + 1) * (s + 2) / 3) * d + D' ≤
      a * (s + 2).choose 2 * t) :
    T.card ≤ s * (m * (m - 1) - (m - b) * (m - b - 1)) +
      (s + 2).choose 2 * (a * R₀ + s * C₀) / D' := by
  have hp_lt : 0 < (s + 2).choose 2 := by
    have h1 := card_monomials s
    have hmem : (0, 0) ∈ monomials s := (mem_monomials_iff s (0, 0)).mpr (by omega)
    have hpos : 0 < (monomials s).card := Finset.card_pos.mpr ⟨(0, 0), hmem⟩
    omega
  simpa using veronese_polar_cap (p := 0) has (by omega) hp_lt hm hbm hms hchar dom u v
    Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0
    (fun r => Fin.elim0 r) (fun r => Fin.elim0 r) (fun r => Fin.elim0 r)
    (fun r => Fin.elim0 r) (fun r => Fin.elim0 r)
    f hm_eq hb hf_geom T pt hpt_inj hpt_on H R V c loss S hH_ne hdeg hag henough htan hR_eq
    hC₀ hR₀ hD'_pos (by simpa using hgap)

/-- **Beyond-Johnson Conic 5-Column Cap (`m = 2`)**:
Directly matches `TangentPolarWindows.beyond_johnson` at `696,254,464` errors!
Omits one degree-2 monomial `e₀` chosen by `conic_five_column_polar_cap`, leaving a 5-element
downward-closed column basis `B5` with `∑ (1 - w) = 1` and `∑ w = 6`, yielding:
`T.card ≤ 4 + 5 * (R₀ + 2 * C₀) / D` whenever `n + 6 * d + D ≤ 5 * t`. -/
theorem conic_five_column_cap {K I α : Type*} [Field K] [Fintype I]
    {d t D C₀ R₀ : ℕ}
    (hchar2 : (2 : K) ≠ 0)
    (dom : I ↪ K) (u v : I → K)
    (f : (FractionRing K[X])[X][X])
    (hm_eq : (mv2EquivBiv.symm f).totalDegree = 2)
    (hf_geom : Irreducible (mapBiv (algebraMap (FractionRing K[X]) (AlgebraicClosure (FractionRing K[X]))) f))
    (T : Finset α) (pt : α → FractionRing K[X] × FractionRing K[X])
    (hpt_inj : Set.InjOn pt (T : Set α))
    (hpt_on : ∀ i ∈ T, (f.map (evalRingHom (pt i).1)).eval (pt i).2 = 0)
    (H R V : α → K[X]) (c loss : α → ℕ) (S : α → Finset I)
    (hH_ne : ∀ i ∈ T, H i ≠ 0)
    (hdeg : ∀ i ∈ T, (H i).natDegree ≤ c i ∧ (R i).natDegree ≤ d + c i ∧ (V i).natDegree ≤ d + c i)
    (hag : ∀ i ∈ T, ∀ z ∈ S i,
      (R i).eval (dom z) = u z * (H i).eval (dom z) ∧
      (V i).eval (dom z) = v z * (H i).eval (dom z))
    (henough : ∀ i ∈ T, t ≤ (S i).card + loss i)
    (htan : ∀ i ∈ T,
      algebraMap K[X] (FractionRing K[X]) (H i) *
        MvPolynomial.eval ![(pt i).1, (pt i).2] (pderiv 0 (mv2EquivBiv.symm f)) +
      algebraMap K[X] (FractionRing K[X]) (V i) *
        MvPolynomial.eval ![(pt i).1, (pt i).2] (pderiv 1 (mv2EquivBiv.symm f)) = 0)
    (hR_eq : ∀ i ∈ T,
      algebraMap K[X] (FractionRing K[X]) (R i) =
        (pt i).2 * algebraMap K[X] (FractionRing K[X]) (H i) -
        (pt i).1 * algebraMap K[X] (FractionRing K[X]) (V i))
    (hC₀ : ∑ i ∈ T, c i ≤ C₀)
    (hR₀ : ∑ i ∈ T, loss i ≤ R₀)
    (hD_pos : 0 < D)
    (hgap : Fintype.card I + 6 * d + D ≤ 5 * t) :
    T.card ≤ 4 + 5 * (R₀ + 2 * C₀) / D := by
  classical
  let L := FractionRing K[X]
  let ι : K[X] →+* L := algebraMap K[X] L
  have hι_inj : Function.Injective ι := IsFractionRing.injective K[X] L
  have hchar2L : (2 : L) ≠ 0 := by
    intro h0; apply hchar2
    have h1 : ι (Polynomial.C (2 : K)) = 0 := by simpa [map_ofNat] using h0
    exact Polynomial.C_eq_zero.mp ((map_eq_zero_iff ι hι_inj).mp h1)
  obtain ⟨e₀, he₀, hcap_e₀⟩ := conic_five_column_polar_cap f hm_eq hf_geom hchar2L
  let B5 := (monomials 2).erase e₀
  obtain ⟨hB5_card, hB5_down, hB5_w, hB5_sub⟩ := conic_five_columns_props he₀
  have hB5_sub_m : B5 ⊆ monomials 2 := Finset.erase_subset e₀ (monomials 2)
  let cost : α → ℕ := fun i => loss i + 2 * c i
  have hcost_bud : ∑ i ∈ T, cost i ≤ R₀ + 2 * C₀ := by
    simp only [cost, Finset.sum_add_distrib, ← Finset.mul_sum]
    exact Nat.add_le_add hR₀ (Nat.mul_le_mul_left 2 hC₀)
  let Texp := T.filter fun i => D ≤ 5 * cost i
  let Tcheap := T.filter fun i => ¬ (D ≤ 5 * cost i)
  have hcard_split : T.card = Tcheap.card + Texp.card := by
    rw [add_comm]
    exact (Finset.card_filter_add_card_filter_not (s := T) (p := fun i => D ≤ 5 * cost i)).symm
  have hTexp_le : Texp.card ≤ 5 * (R₀ + 2 * C₀) / D :=
    markov_expensive_card_le T cost hD_pos hcost_bud
  have hfixed_li : LinearIndependent L (Fin.elim0 : Fin 0 → ↥B5 → L) := by
    rw [Fintype.linearIndependent_iff]; intro _ _ r; exact Fin.elim0 r
  have hdet_zero : ∀ g : Fin (B5.card - 0) → α, (∀ idx, g idx ∈ Tcheap) →
      (Matrix.of (fun (row : Fin B5.card) (col : Fin B5.card) =>
        stackRows (Fin.elim0 : Fin 0 → ↥B5 → L)
          (fun idx j => TangentVeronesePacking.monomial 2 j.val (ι (H (g idx))) (ι (R (g idx))) (ι (V (g idx))))
          (Fin.cast (Nat.add_sub_of_le (Nat.zero_le B5.card)).symm row)
          ((finEquiv B5).symm col))).det = 0 := by
    intro g hg
    let g' : Fin B5.card → α := fun row => g (Fin.cast (Nat.sub_zero B5.card).symm row)
    let Mpoly : Matrix (Fin B5.card) (Fin B5.card) K[X] := Matrix.of fun row col =>
      TangentVeronesePacking.monomial 2 ((finEquiv B5).symm col).val (H (g' row)) (R (g' row)) (V (g' row))
    have hM_map : Mpoly.map ι = Matrix.of (fun row col =>
        stackRows (Fin.elim0 : Fin 0 → ↥B5 → L)
          (fun idx j => TangentVeronesePacking.monomial 2 j.val (ι (H (g idx))) (ι (R (g idx))) (ι (V (g idx))))
          (Fin.cast (Nat.add_sub_of_le (Nat.zero_le B5.card)).symm row)
          ((finEquiv B5).symm col)) := by
      ext row col
      simp only [Matrix.map_apply, Mpoly, Matrix.of_apply, g', stackRows]
      have hcast : Fin.cast (Nat.add_sub_of_le (Nat.zero_le B5.card)).symm row =
          Fin.natAdd 0 (Fin.cast (Nat.sub_zero B5.card).symm row) := by ext; simp
      rw [hcast, Fin.append_right]
      simp [TangentVeronesePacking.monomial]
    rw [← hM_map]
    change (RingHom.mapMatrix ι Mpoly).det = 0
    rw [← RingHom.map_det]
    by_contra hdet_ne
    have hpoly_ne : Mpoly.det ≠ 0 := fun h0 => hdet_ne (by rw [h0, map_zero])
    have hinc := downward_closed_incidence (s := 2) (d := d) (a := 1) B5 hB5_sub_m hB5_down
      dom u v (fun r => H (g' r)) (fun r => R (g' r)) (fun r => V (g' r)) (fun r => c (g' r))
      (fun r => hdeg (g' r) (Finset.mem_filter.mp (hg _)).1) hpoly_ne (fun r => S (g' r))
      (fun r z hz => hag (g' r) (Finset.mem_filter.mp (hg _)).1 z hz)
    have hsum_enough : B5.card * t ≤ (∑ r : Fin B5.card, (S (g' r)).card) + ∑ r : Fin B5.card, loss (g' r) := by
      rw [← Finset.sum_add_distrib]
      calc B5.card * t = ∑ _r : Fin B5.card, t := by simp
        _ ≤ ∑ r : Fin B5.card, ((S (g' r)).card + loss (g' r)) :=
            Finset.sum_le_sum fun r _ => henough (g' r) (Finset.mem_filter.mp (hg _)).1
    have hB5_c : B5.card = 5 := hB5_card
    have hcheap_sum : ∑ r : Fin B5.card, cost (g' r) < D := by
      have hmul_lt : 5 * ∑ r : Fin B5.card, cost (g' r) < 5 * D := by
        rw [Finset.mul_sum]
        calc ∑ r : Fin B5.card, 5 * cost (g' r)
            < ∑ _r : Fin B5.card, D := Finset.sum_lt_sum_of_nonempty
                (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩)
                (fun r _ => lt_of_not_ge (Finset.mem_filter.mp (hg _)).2)
          _ = 5 * D := by simp [hB5_c]
      exact Nat.lt_of_mul_lt_mul_left hmul_lt
    have hcost_eq : ∑ r : Fin B5.card, cost (g' r) =
        (∑ r : Fin B5.card, loss (g' r)) + 2 * (∑ r : Fin B5.card, c (g' r)) := by
      simp only [cost, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hB5_sub, hB5_w, one_mul, mul_one, ← Finset.mul_sum] at hinc
    have h5t : 5 * t = B5.card * t := by rw [hB5_c]
    omega
  obtain ⟨Q, hQ_hom, hQ_ne, hQ_supp, hQ_van⟩ := exists_dual_curve_of_vanishing_minors
    B5 hB5_sub_m (Nat.zero_le B5.card) Fin.elim0 hfixed_li
    Tcheap (fun i => ι (H i)) (fun i => ι (R i)) (fun i => ι (V i)) hdet_zero
  have hQ_e0 : Q.coeff (Finsupp.single 1 e₀.1 + Finsupp.single 2 e₀.2) = 0 := by
    have hve : veroneseExp 2 e₀ = Finsupp.single 1 e₀.1 + Finsupp.single 2 e₀.2 := by
      simp [veroneseExp, he₀]
    rw [← hve]
    exact hQ_supp e₀ ((mem_monomials_iff 2 e₀).mpr (le_of_eq he₀)) (Finset.notMem_erase e₀ _)
  let S_pts : Finset (L × L) := Tcheap.image pt
  have hS_card : S_pts.card = Tcheap.card :=
    Finset.card_image_of_injOn (hpt_inj.mono (Finset.filter_subset _ _))
  let H_pt : L × L → L := fun q => if h : ∃ i ∈ Tcheap, pt i = q then ι (H (Classical.choose h)) else 0
  let R_pt : L × L → L := fun q => if h : ∃ i ∈ Tcheap, pt i = q then ι (R (Classical.choose h)) else 0
  let V_pt : L × L → L := fun q => if h : ∃ i ∈ Tcheap, pt i = q then ι (V (Classical.choose h)) else 0
  have hH_pt (i : α) (hi : i ∈ Tcheap) : H_pt (pt i) = ι (H i) := by
    have hex : ∃ k ∈ Tcheap, pt k = pt i := ⟨i, hi, rfl⟩
    have heq : Classical.choose hex = i :=
      hpt_inj (Finset.mem_filter.mp (Classical.choose_spec hex).1).1
        (Finset.mem_filter.mp hi).1 (Classical.choose_spec hex).2
    simp only [H_pt, hex, ↓reduceDIte, heq]
  have hR_pt (i : α) (hi : i ∈ Tcheap) : R_pt (pt i) = ι (R i) := by
    have hex : ∃ k ∈ Tcheap, pt k = pt i := ⟨i, hi, rfl⟩
    have heq : Classical.choose hex = i :=
      hpt_inj (Finset.mem_filter.mp (Classical.choose_spec hex).1).1
        (Finset.mem_filter.mp hi).1 (Classical.choose_spec hex).2
    simp only [R_pt, hex, ↓reduceDIte, heq]
  have hV_pt (i : α) (hi : i ∈ Tcheap) : V_pt (pt i) = ι (V i) := by
    have hex : ∃ k ∈ Tcheap, pt k = pt i := ⟨i, hi, rfl⟩
    have heq : Classical.choose hex = i :=
      hpt_inj (Finset.mem_filter.mp (Classical.choose_spec hex).1).1
        (Finset.mem_filter.mp hi).1 (Classical.choose_spec hex).2
    simp only [V_pt, hex, ↓reduceDIte, heq]
  have hS_cap : S_pts.card ≤ 4 := by
    refine hcap_e₀ Q hQ_hom hQ_ne hQ_e0 S_pts (fun q hq => ?_) H_pt R_pt V_pt
      (fun q hq => ?_) (fun q hq => ?_) (fun q hq => ?_) (fun q hq => ?_)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact hpt_on i (Finset.mem_filter.mp hi).1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [hH_pt i hi]
      exact (map_ne_zero_iff ι hι_inj).mpr (hH_ne i (Finset.mem_filter.mp hi).1)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [hH_pt i hi, hV_pt i hi]
      exact htan i (Finset.mem_filter.mp hi).1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [hH_pt i hi, hR_pt i hi, hV_pt i hi]
      exact hR_eq i (Finset.mem_filter.mp hi).1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [hH_pt i hi, hR_pt i hi, hV_pt i hi]
      exact hQ_van i hi
  rw [hS_card] at hS_cap
  omega

/-- **Transverse Polar Cap (`s = 1`, L2d)**:
Splits `T` into off-line tangents (`rationalDet ≠ 0`, bounded by
`EighthCollinearOutlier.rational_tangent_population`) and on-line tangents (`rationalDet = 0`,
which satisfy a nonzero degree-`1` dual equation and are bounded by L2a–c `polar_affine_card_le`
at `m * (m - 1) - (m - b) * (m - b - 1)`).

Directly covers `QuarterTransverseTangentBudget` and the `lineGap` branch of `TangentPolarWindows`. -/
theorem transverse_polar_cap {F I : Type} {K α : Type*}
    [Field F] [Fintype F] [DecidableEq F] [Fintype I] [DecidableEq I] [Field K]
    (φ : F →+* K)
    {j d C_core t gap m b C₀ R₀ a : ℕ}
    (hm : 2 ≤ m) (hbm : b ≤ m)
    (hchar : ∀ k : ℕ, 0 < k → k ≤ m * (m - 1) → (k : K) ≠ 0)
    (dom : I ↪ F) (u v : I → F)
    (base dir : F[X] × F[X]) (ab : base ≠ dir)
    (L_heads : Fin j → F[X] × F[X]) (hinj_L : Function.Injective L_heads)
    (hcoll : ∀ i, HalfPredecessorRateQuarterDeterminantCollapse.lineDeterminant base dir (L_heads i) = 0)
    (hdegA : base.1.natDegree ≤ d ∧ base.2.natDegree ≤ d)
    (hdegL : ∀ i, (L_heads i).1.natDegree ≤ d ∧ (L_heads i).2.natDegree ≤ d)
    (hbig : ∀ i, C_core ≤ (HalfPredecessorLineCoreGeometry.jointCore dom u v (L_heads i).1 (L_heads i).2).card)
    -- Geometrically irreducible curve `f` over `L = FractionRing K[X]`
    (f : (FractionRing K[X])[X][X])
    (hm_eq : (mv2EquivBiv.symm f).totalDegree = m)
    (hb : f.natDegree ≤ b)
    (hf_geom : Irreducible (mapBiv (algebraMap (FractionRing K[X]) (AlgebraicClosure (FractionRing K[X]))) f))
    -- Candidate tangent family `T` on `f = 0`
    (T : Finset α) (pt : α → FractionRing K[X] × FractionRing K[X])
    (hpt_inj : Set.InjOn pt (T : Set α))
    (hpt_on : ∀ i ∈ T, (f.map (evalRingHom (pt i).1)).eval (pt i).2 = 0)
    (H R V : α → K[X]) (c loss : α → ℕ) (S : α → Finset I)
    (hH_ne : ∀ i ∈ T, H i ≠ 0)
    (hdeg : ∀ i ∈ T, (H i).natDegree ≤ c i ∧ (R i).natDegree ≤ d + c i ∧ (V i).natDegree ≤ d + c i)
    (hag : ∀ i ∈ T, ∀ z ∈ S i,
      (R i).eval (φ (dom z)) = φ (u z) * (H i).eval (φ (dom z)) ∧
      (V i).eval (φ (dom z)) = φ (v z) * (H i).eval (φ (dom z)))
    (henough : ∀ i ∈ T, t ≤ (S i).card + loss i)
    (htan : ∀ i ∈ T,
      algebraMap K[X] (FractionRing K[X]) (H i) *
        MvPolynomial.eval ![(pt i).1, (pt i).2] (pderiv 0 (mv2EquivBiv.symm f)) +
      algebraMap K[X] (FractionRing K[X]) (V i) *
        MvPolynomial.eval ![(pt i).1, (pt i).2] (pderiv 1 (mv2EquivBiv.symm f)) = 0)
    (hR_eq : ∀ i ∈ T,
      algebraMap K[X] (FractionRing K[X]) (R i) =
        (pt i).2 * algebraMap K[X] (FractionRing K[X]) (H i) -
        (pt i).1 * algebraMap K[X] (FractionRing K[X]) (V i))
    (hC₀ : ∑ i ∈ T, c i ≤ C₀)
    (hR₀ : ∑ i ∈ T, loss i ≤ R₀)
    (haj : a < j) (hgap_pos : 0 < gap)
    (hgap : a * (a + 1) * (Fintype.card I + d) + j * (j - 1) * d + gap ≤
      a * (a + 1) * t + 2 * a * (j * C_core)) :
    T.card ≤ (m * (m - 1) - (m - b) * (m - b - 1)) + a * (a + 1) * (C₀ + R₀) / gap := by
  classical
  let L := FractionRing K[X]
  let ι : K[X] →+* L := algebraMap K[X] L
  have hι_inj : Function.Injective ι := IsFractionRing.injective K[X] L
  let Toff := T.filter fun i => rationalDet φ base dir (H i) (R i) (V i) ≠ 0
  let Ton := T.filter fun i => ¬ (rationalDet φ base dir (H i) (R i) (V i) ≠ 0)
  have hsplit : T.card = Ton.card + Toff.card := by
    rw [add_comm]
    exact (Finset.card_filter_add_card_filter_not (s := T)
      (p := fun i => rationalDet φ base dir (H i) (R i) (V i) ≠ 0)).symm
  -- 1. Off-line tangents bounded directly by `EighthCollinearOutlier.rational_tangent_population`.
  have hToff_le : Toff.card ≤ a * (a + 1) * (C₀ + R₀) / gap := by
    refine rational_tangent_population φ dom u v base dir ab L_heads hinj_L hcoll hdegA hdegL hbig
      Toff H R V c S
      (fun i hi => (hdeg i (Finset.mem_filter.mp hi).1).1)
      (fun i hi => (hdeg i (Finset.mem_filter.mp hi).1).2)
      (fun i hi => (Finset.mem_filter.mp hi).2)
      (fun i hi z hz => hag i (Finset.mem_filter.mp hi).1 z hz)
      ((Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hC₀)
      ?_ a haj hgap_pos hgap
    have hsum_en : Toff.card * t ≤ (∑ i ∈ Toff, (S i).card) + ∑ i ∈ Toff, loss i := by
      rw [← Finset.sum_add_distrib]
      calc Toff.card * t = ∑ _i ∈ Toff, t := by simp
        _ ≤ ∑ i ∈ Toff, ((S i).card + loss i) :=
            Finset.sum_le_sum fun i hi => henough i (Finset.mem_filter.mp hi).1
    exact hsum_en.trans (Nat.add_le_add_left
      ((Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hR₀) _)
  -- 2. On-line tangents satisfy a nonzero linear dual equation `Q_lin(H, R, V) = 0`, bounded by L2a–c (`s = 1`).
  let P_dir : K[X] := (HalfPredecessorRateQuarterPrimitiveDirection.primitiveIntercept base dir).map φ
  let Q_dir : K[X] := (HalfPredecessorRateQuarterPrimitiveDirection.primitiveSlope base dir).map φ
  have hPQ_nz : P_dir ≠ 0 ∨ Q_dir ≠ 0 := by
    rcases HalfPredecessorRateQuarterPrimitiveDirection.primitiveDirection_eval_ne_zero ab (0 : F) with hp | hq
    · left
      intro h0
      apply hp
      have h1 : HalfPredecessorRateQuarterPrimitiveDirection.primitiveIntercept base dir = 0 :=
        Polynomial.map_injective φ φ.injective (by simpa [P_dir] using h0)
      change (HalfPredecessorRateQuarterPrimitiveDirection.primitiveIntercept base dir).eval 0 = 0
      simp [h1]
    · right
      intro h0
      apply hq
      have h1 : HalfPredecessorRateQuarterPrimitiveDirection.primitiveSlope base dir = 0 :=
        Polynomial.map_injective φ φ.injective (by simpa [Q_dir] using h0)
      change (HalfPredecessorRateQuarterPrimitiveDirection.primitiveSlope base dir).eval 0 = 0
      simp [h1]
  let c0 : L := ι (Q_dir * base.1.map φ - P_dir * base.2.map φ)
  let c1 : L := ι (-Q_dir)
  let c2 : L := ι P_dir
  let Q_lin : MvPolynomial (Fin 3) L :=
    MvPolynomial.C c0 * MvPolynomial.X 0 + MvPolynomial.C c1 * MvPolynomial.X 1 +
      MvPolynomial.C c2 * MvPolynomial.X 2
  have hQ_hom : Q_lin.IsHomogeneous 1 := by
    rw [← mem_homogeneousSubmodule]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · rw [mem_homogeneousSubmodule]; simpa using (MvPolynomial.isHomogeneous_C (Fin 3) c0).mul (MvPolynomial.isHomogeneous_X L 0)
    · rw [mem_homogeneousSubmodule]; simpa using (MvPolynomial.isHomogeneous_C (Fin 3) c1).mul (MvPolynomial.isHomogeneous_X L 1)
    · rw [mem_homogeneousSubmodule]; simpa using (MvPolynomial.isHomogeneous_C (Fin 3) c2).mul (MvPolynomial.isHomogeneous_X L 2)
  have hQ_ne : Q_lin ≠ 0 := by
    intro h0
    rcases hPQ_nz with hP | hQ
    · have hc2 : Q_lin.coeff (Finsupp.single 2 1) = c2 := by
        have h02 : Finsupp.single (0 : Fin 3) 1 ≠ Finsupp.single 2 1 := by
          intro h; have := congrArg (fun g : Fin 3 →₀ ℕ => g 0) h; simp at this
        have h12 : Finsupp.single (1 : Fin 3) 1 ≠ Finsupp.single 2 1 := by
          intro h; have := congrArg (fun g : Fin 3 →₀ ℕ => g 1) h; simp at this
        simp [Q_lin, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, h02, h12]
      rw [h0] at hc2; simp only [AddMonoidAlgebra.coeff_zero] at hc2
      exact hP ((map_eq_zero_iff ι hι_inj).mp hc2.symm)
    · have hc1 : Q_lin.coeff (Finsupp.single 1 1) = c1 := by
        have h01 : Finsupp.single (0 : Fin 3) 1 ≠ Finsupp.single 1 1 := by
          intro h; have := congrArg (fun g : Fin 3 →₀ ℕ => g 0) h; simp at this
        have h21 : Finsupp.single (2 : Fin 3) 1 ≠ Finsupp.single 1 1 := by
          intro h; have := congrArg (fun g : Fin 3 →₀ ℕ => g 2) h; simp at this
        simp [Q_lin, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, h01, h21]
      rw [h0] at hc1; simp only [AddMonoidAlgebra.coeff_zero] at hc1
      exact hQ (neg_eq_zero.mp ((map_eq_zero_iff ι hι_inj).mp hc1.symm))
  have hQ_van : ∀ i ∈ Ton, MvPolynomial.eval ![ι (H i), ι (R i), ι (V i)] Q_lin = 0 := by
    intro i hi
    have hdet0 : rationalDet φ base dir (H i) (R i) (V i) = 0 :=
      not_not.mp (Finset.mem_filter.mp hi).2
    have heq : MvPolynomial.eval ![ι (H i), ι (R i), ι (V i)] Q_lin =
        ι (rationalDet φ base dir (H i) (R i) (V i)) := by
      simp only [Q_lin, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, c0, c1, c2,
        rationalDet, P_dir, Q_dir, map_sub, map_neg]
      ring
    rw [heq, hdet0, map_zero]
  have hcharL : ∀ k : ℕ, 0 < k → k ≤ m * (m - 1) → (k : L) ≠ 0 := by
    intro k hk1 hk2 h0
    apply hchar k hk1 hk2
    have h1 : ι (Polynomial.C (k : K)) = 0 := by simpa [map_natCast] using h0
    exact Polynomial.C_eq_zero.mp ((map_eq_zero_iff ι hι_inj).mp h1)
  let S_pts : Finset (L × L) := Ton.image pt
  have hS_card : S_pts.card = Ton.card :=
    Finset.card_image_of_injOn (hpt_inj.mono (Finset.filter_subset _ _))
  let H_pt : L × L → L := fun q => if h : ∃ i ∈ Ton, pt i = q then ι (H (Classical.choose h)) else 0
  let R_pt : L × L → L := fun q => if h : ∃ i ∈ Ton, pt i = q then ι (R (Classical.choose h)) else 0
  let V_pt : L × L → L := fun q => if h : ∃ i ∈ Ton, pt i = q then ι (V (Classical.choose h)) else 0
  have hH_pt (i : α) (hi : i ∈ Ton) : H_pt (pt i) = ι (H i) := by
    have hex : ∃ k ∈ Ton, pt k = pt i := ⟨i, hi, rfl⟩
    have heq : Classical.choose hex = i :=
      hpt_inj (Finset.mem_filter.mp (Classical.choose_spec hex).1).1
        (Finset.mem_filter.mp hi).1 (Classical.choose_spec hex).2
    simp only [H_pt, hex, ↓reduceDIte, heq]
  have hR_pt (i : α) (hi : i ∈ Ton) : R_pt (pt i) = ι (R i) := by
    have hex : ∃ k ∈ Ton, pt k = pt i := ⟨i, hi, rfl⟩
    have heq : Classical.choose hex = i :=
      hpt_inj (Finset.mem_filter.mp (Classical.choose_spec hex).1).1
        (Finset.mem_filter.mp hi).1 (Classical.choose_spec hex).2
    simp only [R_pt, hex, ↓reduceDIte, heq]
  have hV_pt (i : α) (hi : i ∈ Ton) : V_pt (pt i) = ι (V i) := by
    have hex : ∃ k ∈ Ton, pt k = pt i := ⟨i, hi, rfl⟩
    have heq : Classical.choose hex = i :=
      hpt_inj (Finset.mem_filter.mp (Classical.choose_spec hex).1).1
        (Finset.mem_filter.mp hi).1 (Classical.choose_spec hex).2
    simp only [V_pt, hex, ↓reduceDIte, heq]
  have hTon_le : S_pts.card ≤ 1 * (m * (m - 1) - (m - b) * (m - b - 1)) := by
    refine polar_affine_card_le (s := 1) f hm_eq hm hb hbm hf_geom hcharL Q_lin hQ_hom hQ_ne
      (by omega) S_pts (fun q hq => ?_) H_pt R_pt V_pt
      (fun q hq => ?_) (fun q hq => ?_) (fun q hq => ?_) (fun q hq => ?_)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact hpt_on i (Finset.mem_filter.mp hi).1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [hH_pt i hi]
      exact (map_ne_zero_iff ι hι_inj).mpr (hH_ne i (Finset.mem_filter.mp hi).1)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [hH_pt i hi, hV_pt i hi]
      exact htan i (Finset.mem_filter.mp hi).1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [hH_pt i hi, hR_pt i hi, hV_pt i hi]
      exact hR_eq i (Finset.mem_filter.mp hi).1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [hH_pt i hi, hR_pt i hi, hV_pt i hi]
      exact hQ_van i hi
  rw [hS_card, one_mul] at hTon_le
  omega

/-- Simplified `lineGap` form of `transverse_polar_cap` matching `TangentPolarWindows.component`:
when `0 < a` and `a * (a + 1) * lineGap ≤ gap`, `a * (a + 1) * (C₀ + R₀) / gap ≤ (C₀ + R₀) / lineGap`. -/
theorem transverse_div_le {a C₀ R₀ lineGap gap : ℕ}
    (ha : 0 < a) (hlg : 0 < lineGap) (hle : a * (a + 1) * lineGap ≤ gap) :
    a * (a + 1) * (C₀ + R₀) / gap ≤ (C₀ + R₀) / lineGap := by
  have hA_pos : 0 < a * (a + 1) := Nat.mul_pos ha (Nat.succ_pos a)
  have hgap_pos : 0 < gap := lt_of_lt_of_le (Nat.mul_pos hA_pos hlg) hle
  rw [Nat.le_div_iff_mul_le hlg]
  have h1 := Nat.div_mul_le_self (a * (a + 1) * (C₀ + R₀)) gap
  have h2 : (a * (a + 1) * (C₀ + R₀) / gap) * (a * (a + 1) * lineGap) ≤
      (a * (a + 1) * (C₀ + R₀) / gap) * gap := Nat.mul_le_mul_left _ hle
  have h3 : (a * (a + 1)) * ((a * (a + 1) * (C₀ + R₀) / gap) * lineGap) ≤
      (a * (a + 1)) * (C₀ + R₀) := by
    calc (a * (a + 1)) * ((a * (a + 1) * (C₀ + R₀) / gap) * lineGap)
        = (a * (a + 1) * (C₀ + R₀) / gap) * (a * (a + 1) * lineGap) := by ring
      _ ≤ (a * (a + 1) * (C₀ + R₀) / gap) * gap := h2
      _ ≤ a * (a + 1) * (C₀ + R₀) := h1
  exact Nat.le_of_mul_le_mul_left h3 hA_pos

end MainPolarCaps

#print axioms card_monomials
#print axioms sum_weight_monomials
#print axioms sum_sub_weight_monomials
#print axioms fixed_rows_linearIndependent
#print axioms exists_dual_curve_of_vanishing_minors
#print axioms downward_closed_incidence
#print axioms veronese_polar_cap
#print axioms veronese_polar_cap_p0
#print axioms conic_five_column_cap
#print axioms transverse_polar_cap
#print axioms transverse_div_le

end ArkLib.ProximityGap.Frontier.VeroneseCheapRowPolarCap
