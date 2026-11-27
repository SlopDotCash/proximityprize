/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothPowerListDescent
import ArkLib.Research.ProximityGap.Frontier.MixedInclusionOmissionJohnson
import ArkLib.Research.ProximityGap.Frontier.InterleavedListProjection
import Mathlib.LinearAlgebra.Lagrange

/-!
# Smooth Coset-Folding List Descent, Saturated Three-Split Pencils, and Multi-Step Inclusion Bounds

This module establishes three beyond-Johnson tools for Reed–Solomon list decoding:

1. **Exact `m`-Way Coset-Folding Decomposition and Defect-Sensitive List Descent**:
   Every polynomial `P` of degree `< m * k` decomposes uniquely into `m` slices
   `foldSlice m k P r` of degree `< k` via `P(X) = ∑ r, X ^ r * P_r(X ^ m)`. On any regular
   `m`-to-`1` power fiber `F_v` of size `m` (`D i ^ m = E v`), full-fiber agreement of `P` with
   any received word `y` is equivalent (`↔`) via `Lagrange.eq_interpolate_iff` to column agreement
   of `(P_0(E v), ..., P_{m - 1}(E v))` with the Lagrange-interpolated folded center. Combining
   this with the exact fiber-error accounting identity
   `hammingDist foldedWord foldedCenter + fiberErrorExcess = hammingDist c y` yields coset-burst,
   excess-sensitive, and low-error list-size transfers from `(m * width)`-interleaved RS on `E`
   to `width`-interleaved RS on `D` — including smooth multiplicative cosets via
   `SmoothPowerMcaDescent.exists_smooth_base`.

2. **Algebraic Common-Core Star Bound and Saturated Three-Split Locator Pencils**:
   Any `r` distinct `width`-interleaved codewords of degree `< k` whose `≥ t`-agreement sets all
   contain a common `(k - 1)`-subset satisfy `r * (t - (k - 1)) ≤ |I| - (k - 1)` (`r ≤ 2` at
   production rate `1/2` `J + 1`, and `r ≤ 3` at rates `1/4` and `1/8` `J + 1`). Whenever three
   distinct scalar codewords form a saturated overlap triangle (`|S_a ∩ S_b| = k - 1`) with
   triple core `|S_0 ∩ S_1 ∩ S_2| = w < k - 1`, their pairwise differences factor through three
   pairwise disjoint subsets `A, B, C_set ⊆ I \ W` of positive cardinality `m = k - 1 - w`
   (`m ≥ 3 * t - 2 * (k - 1) - |I|`) satisfying the exact monic three-split locator pencil
   `Lagrange.nodal C_set D = C μ * Lagrange.nodal A D + C (1 - μ) * Lagrange.nodal B D`
   with `μ ∈ F \ {0, 1}`. Consequently, whenever `|I| - (k - 1) < 4 * (t - (k - 1))`, every
   saturated `4`-clique unconditionally forces a positive-degree three-split locator pencil.

3. **Multi-Step Mixed Inclusion–Omission Bounds at Production Length `n = 2^30`**:
   Proves the all-`k`, all-`s` algebraic identity at rate `1/16` (`Johnson + s`) showing pure
   `s`-site inclusion (`r = 0`) remains strictly inside the punctured Johnson cone at every step
   `s ≥ 1`, and certifies sharp `n = 2^30` all-domain / all-field / all-width list bounds at
   rate `1/8` (`J + 2`: `8,589,934,703`, `2.65×` below `MultipleOmissionJohnson`; `J + 3`:
   `58,139,264,338`, `3.47×` below pure omission) and rate `1/16` (`J + 2`: `17,179,869,712`,
   `8.31×`; `J + 3`: `68,719,480,960`, `15.57×`).
-/

set_option autoImplicit false

namespace ProximityGap.CarbonListSmoothFoldedRigidity

open Finset Code Polynomial InterleavedListJohnsonRank
open scoped BigOperators ENNReal

/-! ### 1. Exact `m`-way polynomial folding and fiberwise list descent -/

/-- The `r`-th `m`-way folded slice of `P`, collecting coefficients `q * m + r`. -/
noncomputable def foldSlice {F : Type*} [Semiring F] (m k : ℕ) (P : F[X]) (r : Fin m) : F[X] :=
  ∑ q ∈ range k, C (P.coeff (q * m + r.val)) * X ^ q

/-- Every folded slice has degree strictly below `k`. -/
theorem degree_foldSlice_lt {F : Type*} [Semiring F] (m k : ℕ) (P : F[X]) (r : Fin m) :
    (foldSlice m k P r).degree < (k : WithBot ℕ) := by
  refine (degree_sum_le (range k) _).trans_lt ?_
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe k)).mpr
  intro q hq
  have hqk : q < k := mem_range.mp hq
  calc
    (C (P.coeff (q * m + r.val)) * X ^ q).degree ≤
        (C (P.coeff (q * m + r.val))).degree + (X ^ q : F[X]).degree := degree_mul_le _ _
    _ ≤ 0 + (q : WithBot ℕ) := add_le_add degree_C_le (Polynomial.degree_X_pow_le q)
    _ = (q : WithBot ℕ) := zero_add _
    _ < (k : WithBot ℕ) := WithBot.coe_lt_coe.mpr hqk

private theorem mul_foldSlice_comp_eq {F : Type*} [CommRing F] (m k : ℕ) (P : F[X]) (r : Fin m) :
    X ^ r.val * (foldSlice m k P r).comp (X ^ m) =
      ∑ q ∈ range k, C (P.coeff (q * m + r.val)) * X ^ (q * m + r.val) := by
  unfold foldSlice
  rw [Polynomial.sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mul_comp, C_comp, pow_comp, X_comp, ← pow_mul, mul_comm m q]
  calc
    X ^ r.val * (C (P.coeff (q * m + r.val)) * X ^ (q * m)) =
        C (P.coeff (q * m + r.val)) * (X ^ (q * m) * X ^ r.val) := by ring
    _ = C (P.coeff (q * m + r.val)) * X ^ (q * m + r.val) := by rw [← pow_add]

/-- Every polynomial of degree `< m * k` reconstructs from its `m` folded slices evaluated at
`X ^ m`. -/
theorem sum_foldSlice_comp {F : Type*} [CommRing F] {m k : ℕ} (hm : 0 < m) {P : F[X]}
    (hP : P.degree < ((m * k : ℕ) : WithBot ℕ)) :
    (∑ r : Fin m, X ^ r.val * (foldSlice m k P r).comp (X ^ m)) = P := by
  ext n
  simp_rw [mul_foldSlice_comp_eq, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  by_cases hn : n < m * k
  · let q₀ : ℕ := n / m
    let r₀ : Fin m := ⟨n % m, Nat.mod_lt n hm⟩
    have hdiv : q₀ * m + r₀.val = n := by
      dsimp only [q₀, r₀]
      rw [mul_comm]
      exact Nat.div_add_mod n m
    have hq₀ : q₀ < k := by
      by_contra! hkq
      have hmul := Nat.mul_le_mul_right m hkq
      have hrlt := r₀.isLt
      nlinarith
    rw [Fintype.sum_eq_single r₀]
    · rw [Finset.sum_eq_single q₀]
      · rw [ite_eq_left hdiv.symm, mul_one, hdiv]
      · intro q _ hqne
        have hne : n ≠ q * m + r₀.val := by
          intro heq
          apply hqne
          have hmulEq : q * m = q₀ * m := by omega
          exact Nat.eq_of_mul_eq_mul_right hm hmulEq
        rw [ite_eq_right hne, mul_zero]
      · intro hnot
        exact False.elim (hnot (mem_range.mpr hq₀))
    · intro r hrne
      apply Finset.sum_eq_zero
      intro q _
      have hne : n ≠ q * m + r.val := by
        intro heq
        apply hrne
        apply Fin.ext
        have hrlt := r.isLt
        have hr₀lt := r₀.isLt
        rcases lt_trichotomy q q₀ with hlt | rfl | hgt
        · have hle := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hlt)
          rw [Nat.succ_mul] at hle
          omega
        · omega
        · have hle := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hgt)
          rw [Nat.succ_mul] at hle
          omega
      rw [ite_eq_right hne, mul_zero]
  · rw [coeff_eq_zero_of_degree_lt (hP.trans_le (WithBot.coe_le_coe.mpr (not_lt.mp hn)))]
    apply Fintype.sum_eq_zero
    intro r
    apply Finset.sum_eq_zero
    intro q hq
    have hqk : q < k := mem_range.mp hq
    have hrlt : r.val < m := r.isLt
    have hlt : q * m + r.val < m * k := by
      have hle := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hqk)
      rw [Nat.succ_mul, mul_comm k m] at hle
      omega
    have hne : n ≠ q * m + r.val := by omega
    rw [ite_eq_right hne, mul_zero]

/-- On an `m`-element fiber `F_z` where `D i ^ m = z`, full-fiber agreement of `P` (`deg P < m * k`)
with `y` is equivalent to agreement of all `m` folded slices at `z` with the coefficients of the
Lagrange interpolant of `y` on `F_z`. -/
theorem eval_eq_on_fiber_iff_folded {I F : Type*} [DecidableEq I] [Field F]
    (D : I ↪ F) {m k : ℕ} (hm : 0 < m) {F_z : Finset I} {z : F}
    (hcard : F_z.card = m) (hpow : ∀ i ∈ F_z, D i ^ m = z)
    {P : F[X]} (hP : P.degree < ((m * k : ℕ) : WithBot ℕ)) (y : I → F) :
    (∀ i ∈ F_z, P.eval (D i) = y i) ↔
      ∀ r : Fin m, (foldSlice m k P r).eval z = (Lagrange.interpolate F_z D y).coeff r.val := by
  let Q : F[X] := ∑ r : Fin m, C ((foldSlice m k P r).eval z) * X ^ r.val
  have hQdeg : Q.degree < (F_z.card : WithBot ℕ) := by
    rw [hcard]
    refine (degree_sum_le univ _).trans_lt ?_
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe m)).mpr
    intro r _
    calc
      (C ((foldSlice m k P r).eval z) * X ^ r.val).degree ≤
          (C ((foldSlice m k P r).eval z)).degree + (X ^ r.val : F[X]).degree := degree_mul_le _ _
      _ ≤ 0 + (r.val : WithBot ℕ) := add_le_add degree_C_le (Polynomial.degree_X_pow_le r.val)
      _ < (m : WithBot ℕ) := by
        rw [zero_add]
        exact WithBot.coe_lt_coe.mpr r.isLt
  have hQeval : ∀ i ∈ F_z, Q.eval (D i) = P.eval (D i) := by
    intro i hi
    conv_rhs => rw [← sum_foldSlice_comp hm hP]
    simp only [Q, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_comp, hpow i hi]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hQcoeff : ∀ r : Fin m, Q.coeff r.val = (foldSlice m k P r).eval z := by
    intro r
    simp only [Q, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Fintype.sum_eq_single r]
    · simp only [↓reduceIte, mul_one]
    · intro r' hr'
      rw [ite_eq_right (Fin.val_ne_of_ne hr'.symm), mul_zero]
  have hvs : Set.InjOn D F_z := D.injective.injOn
  have hinterp : (∀ i ∈ F_z, P.eval (D i) = y i) ↔ Q = Lagrange.interpolate F_z D y := by
    constructor
    · intro hag
      exact (Lagrange.eq_interpolate_iff (s := F_z) (v := D) (f := Q) y hvs).mp
        ⟨hQdeg, fun i hi => (hQeval i hi).trans (hag i hi)⟩
    · intro heq i hi
      have hnode := ((Lagrange.eq_interpolate_iff (s := F_z) (v := D) (f := Q) y hvs).mpr heq).2
      exact (hQeval i hi).symm.trans (hnode i hi)
  rw [hinterp]
  constructor
  · intro heq r
    rw [← hQcoeff r, heq]
  · intro hall
    ext n
    by_cases hn : n < m
    · let r : Fin m := ⟨n, hn⟩
      change Q.coeff r.val = (Lagrange.interpolate F_z D y).coeff r.val
      rw [hQcoeff r, hall r]
    · have hle : (F_z.card : WithBot ℕ) ≤ (n : WithBot ℕ) := by
        rw [hcard]
        exact WithBot.coe_le_coe.mpr (not_lt.mp hn)
      rw [coeff_eq_zero_of_degree_lt (hQdeg.trans_le hle),
        coeff_eq_zero_of_degree_lt
          ((Lagrange.degree_interpolate_lt (s := F_z) (v := D) y hvs).trans_le hle)]

/-- Number of coordinate errors on fiber `v` of `π : I → J`. -/
def fiberErrors {I J α : Type*} [Fintype I] [DecidableEq J] [DecidableEq α]
    (π : I → J) (c y : I → α) (v : J) : ℕ :=
  (univ.filter fun i : I => π i = v ∧ c i ≠ y i).card

/-- Multi-error excess across all fibers: each damaged fiber with `s ≥ 1` coordinate errors
contributes `s - 1` excess errors beyond its single base-symbol error. -/
def fiberErrorExcess {I J α : Type*} [Fintype I] [Fintype J] [DecidableEq J] [DecidableEq α]
    (π : I → J) (c y : I → α) : ℕ :=
  ∑ v : J, (fiberErrors π c y v - 1)

/-- Exact fiber-error accounting identity: base Hamming distance plus multi-error excess equals
coordinate Hamming distance. -/
theorem hammingDist_add_fiberExcess_eq {I J α β : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] [DecidableEq α] [DecidableEq β]
    (π : I → J) (c y : I → α) (c' y' : J → β)
    (hiff : ∀ v : J, c' v = y' v ↔ ∀ i : I, π i = v → c i = y i) :
    hammingDist c' y' + fiberErrorExcess π c y = hammingDist c y := by
  have hbase : hammingDist c' y' = ∑ v : J, if c' v ≠ y' v then 1 else 0 := by
    change (univ.filter fun v : J => c' v ≠ y' v).card = _
    rw [Finset.card_filter]
  rw [hbase, fiberErrorExcess, ← Finset.sum_add_distrib]
  have hpoint (v : J) :
      (if c' v ≠ y' v then 1 else 0) + (fiberErrors π c y v - 1) = fiberErrors π c y v := by
    have hpos_iff : c' v ≠ y' v ↔ 0 < fiberErrors π c y v := by
      rw [ne_eq, hiff v, fiberErrors, Finset.card_pos]
      constructor
      · intro hnot
        push Not at hnot
        obtain ⟨i, hπ, hne⟩ := hnot
        exact ⟨i, mem_filter.mpr ⟨mem_univ i, hπ, hne⟩⟩
      · rintro ⟨i, hi⟩ hall
        obtain ⟨_, hπ, hne⟩ := mem_filter.mp hi
        exact hne (hall i hπ)
    by_cases hne : c' v ≠ y' v
    · have hpos : 0 < fiberErrors π c y v := hpos_iff.mp hne
      rw [ite_eq_left hne]
      omega
    · have hzero : ¬ 0 < fiberErrors π c y v := fun hp => hne (hpos_iff.mpr hp)
      rw [ite_eq_right hne]
      omega
  simp_rw [hpoint]
  let E_set : Finset I := univ.filter fun i : I => c i ≠ y i
  have hfib_eq (v : J) : fiberErrors π c y v = (E_set.filter fun i => π i = v).card := by
    unfold fiberErrors
    congr 1
    ext i
    simp only [E_set, mem_filter, mem_univ, true_and, and_comm]
  simp_rw [hfib_eq]
  have htotal := Finset.sum_card_fiberwise_eq_card_filter (s := E_set) (t := (univ : Finset J))
    (g := π)
  rw [Finset.filter_true_of_mem (fun x _ => mem_univ (π x))] at htotal
  exact htotal

/-- General coset-folding list-size transfer: for any regular `m`-to-`1` power projection
`D i ^ m = E (π i)` onto `E : J ↪ F`, any finite family `S` of `width`-interleaved codewords of
degree `< m * k` around `y` whose damaged fiber count `hammingDist c y - fiberErrorExcess π c y`
is at most `eFib` has cardinality bounded by `Code.Lambda` of the `(m * width)`-interleaved RS
code on `E` of degree `< k` at relative radius `eFib / |J|`. -/
theorem folded_family_card_le_base_lambda {I J F : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [Nonempty J] [DecidableEq J] [Field F] [DecidableEq F]
    (D : I ↪ F) (E : J ↪ F) (π : I → J) {m k width eFib : ℕ} (hm : 0 < m)
    (hdom : ∀ i : I, D i ^ m = E (π i))
    (hfib : ∀ v : J, (univ.filter fun i : I => π i = v).card = m)
    (y : I → Fin width → F) (S : Finset (I → Fin width → F))
    (hcode : ∀ c ∈ S, c ∈ interleavedCodeSet (κ := Fin width)
      (ReedSolomon.code D (m * k) : Set (I → F)))
    (herr : ∀ c ∈ S,
      hammingDist c y ≤ eFib + fiberErrorExcess π c y) :
    (S.card : ℕ∞) ≤ Code.Lambda (interleavedCodeSet (κ := Fin (m * width))
      (ReedSolomon.code E k : Set (J → F))) ((eFib : ℝ) / Fintype.card J) := by
  classical
  let packEquiv : Fin m × Fin width ≃ Fin (m * width) :=
    Fintype.equivFinOfCardEq (by simp only [Fintype.card_prod, Fintype.card_fin])
  let fibSet (v : J) : Finset I := univ.filter fun i : I => π i = v
  let yFold : J → Fin (m * width) → F := fun v idx =>
    let p := packEquiv.symm idx
    (Lagrange.interpolate (fibSet v) D (fun i => y i p.2)).coeff p.1.val
  let polyOf (c : I → Fin width → F) (col : Fin width) : F[X] :=
    if hc : c ∈ interleavedCodeSet (κ := Fin width)
        (ReedSolomon.code D (m * k) : Set (I → F)) then
      Classical.choose (ReedSolomon.mem_code_iff_eval.mp (hc col))
    else 0
  have hpolySpec {c : I → Fin width → F} (hc : c ∈ S) (col : Fin width) :
      (polyOf c col).degree < ((m * k : ℕ) : WithBot ℕ) ∧
        ∀ i : I, (polyOf c col).eval (D i) = c i col := by
    have hmem := hcode c hc
    simp only [polyOf, hmem, ↓reduceDIte]
    exact Classical.choose_spec (ReedSolomon.mem_code_iff_eval.mp (hmem col))
  let foldMap (c : I → Fin width → F) : J → Fin (m * width) → F := fun v idx =>
    let p := packEquiv.symm idx
    (foldSlice m k (polyOf c p.2) p.1).eval (E v)
  have hinj : (S : Set (I → Fin width → F)).InjOn foldMap := by
    intro c₁ hc₁ c₂ hc₂ heq
    funext i col
    obtain ⟨hdeg₁, heval₁⟩ := hpolySpec hc₁ col
    obtain ⟨hdeg₂, heval₂⟩ := hpolySpec hc₂ col
    rw [← heval₁ i, ← heval₂ i, ← sum_foldSlice_comp hm hdeg₁, ← sum_foldSlice_comp hm hdeg₂]
    simp only [eval_finsetSum, eval_mul, eval_pow, eval_X, eval_comp, hdom i]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hidx := congrFun (congrFun heq (π i)) (packEquiv (r, col))
    dsimp only [foldMap] at hidx
    rw [packEquiv.symm_apply_apply] at hidx
    rw [hidx]
  have htarget : ∀ c ∈ S, foldMap c ∈ closeCodewordsRel
      (interleavedCodeSet (κ := Fin (m * width)) (ReedSolomon.code E k : Set (J → F)))
      yFold ((eFib : ℝ) / Fintype.card J) := by
    intro c hc
    refine mem_closeCodewordsRel_iff.mpr ⟨?_, ?_⟩
    · intro idx
      let p := packEquiv.symm idx
      exact ReedSolomon.mem_code_iff_eval.mpr
        ⟨foldSlice m k (polyOf c p.2) p.1, degree_foldSlice_lt m k _ _, fun v => rfl⟩
    · have hiff : ∀ v : J, foldMap c v = yFold v ↔ ∀ i : I, π i = v → c i = y i := by
        intro v
        have hpow : ∀ i ∈ fibSet v, D i ^ m = E v := by
          intro i hi
          rw [hdom i, (mem_filter.mp hi).2]
        constructor
        · intro hv i hπ
          funext col
          obtain ⟨hdeg, heval⟩ := hpolySpec hc col
          have hi : i ∈ fibSet v := mem_filter.mpr ⟨mem_univ i, hπ⟩
          have hall : ∀ r : Fin m, (foldSlice m k (polyOf c col) r).eval (E v) =
              (Lagrange.interpolate (fibSet v) D (fun x => y x col)).coeff r.val := by
            intro r
            have hcol := congrFun hv (packEquiv (r, col))
            dsimp only [foldMap, yFold] at hcol
            rwa [packEquiv.symm_apply_apply] at hcol
          have hfibEq := (eval_eq_on_fiber_iff_folded D hm (hfib v) hpow hdeg
            (fun x => y x col)).mpr hall
          exact (heval i).symm.trans (hfibEq i hi)
        · intro hall
          funext idx
          let p := packEquiv.symm idx
          obtain ⟨hdeg, heval⟩ := hpolySpec hc p.2
          have hfibEq : ∀ i ∈ fibSet v, (polyOf c p.2).eval (D i) = y i p.2 := by
            intro i hi
            exact (heval i).trans (congrFun (hall i (mem_filter.mp hi).2) p.2)
          exact (eval_eq_on_fiber_iff_folded D hm (hfib v) hpow hdeg
            (fun x => y x p.2)).mp hfibEq p.1
      have hacc := hammingDist_add_fiberExcess_eq π c y (foldMap c) yFold hiff
      have hdist_le : hammingDist (foldMap c) yFold ≤ eFib := by
        have herr_c := herr c hc
        omega
      rw [relHammingDist_coe, hammingDist_comm yFold]
      have hJpos : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos (α := J)
      exact div_le_div_of_nonneg_right (by exact_mod_cast hdist_le) hJpos.le
  have himg : ((S : Set (I → Fin width → F)).image foldMap).encard ≤
      Code.Lambda (interleavedCodeSet (κ := Fin (m * width))
        (ReedSolomon.code E k : Set (J → F))) ((eFib : ℝ) / Fintype.card J) :=
    encard_le_Lambda_of_subset_closeCodewordsRel (by
      rintro _ ⟨c, hc, rfl⟩
      exact htarget c hc)
  rwa [hinj.encard_image, Set.encard_coe_eq_coe_finsetCard] at himg

/-- Unconditional low-error coset-folding inequality on smooth domains: since `e` coordinate
errors can damage at most `e` power fibers, any `width`-interleaved list bound on the smooth
quotient of size `h` at radius `e / h` bounds `Code.Lambda` on the full smooth domain of size
`m * h` at radius `e / (m * h)`. -/
theorem smooth_folded_low_error_lambda_le {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D]
    {m h k width e B : ℕ} (hm : 0 < m) (hn : Fintype.card I = m * h) (hp : ∃ b : ℕ, h = 2 ^ b)
    (hbase : ∀ (V : Finset F), V.card = h →
      ReedSolomon.Smooth (Function.Embedding.subtype (· ∈ V)) →
      Code.Lambda (interleavedCodeSet (κ := Fin (m * width))
        (ReedSolomon.code (Function.Embedding.subtype (· ∈ V)) k : Set (V → F)))
        ((e : ℝ) / h) ≤ (B : ℕ∞)) :
    Code.Lambda (interleavedCodeSet (κ := Fin width)
      (ReedSolomon.code D (m * k) : Set (I → F))) ((e : ℝ) / (m * h : ℕ)) ≤ (B : ℕ∞) := by
  classical
  obtain ⟨V, hV, hmem, hfib, ⟨sm⟩, -⟩ := SmoothPowerMcaDescent.exists_smooth_base D hm hn hp
  have hhpos : 0 < h := by
    obtain ⟨b, rfl⟩ := hp
    positivity
  let _ : Nonempty V := Fintype.card_pos_iff.mp (by simpa only [Fintype.card_coe, hV] using hhpos)
  let E : V ↪ F := Function.Embedding.subtype (· ∈ V)
  let π (i : I) : V := ⟨D i ^ m, hmem i⟩
  have hf (v : V) : (univ.filter fun i : I => π i = v).card = m := by
    simpa only [π, Subtype.ext_iff] using hfib v.val v.property
  apply Lambda_le_of_forall_finset_card_le
  intro y S hS
  have hcode : ∀ c ∈ S, c ∈ interleavedCodeSet (κ := Fin width)
      (ReedSolomon.code D (m * k) : Set (I → F)) :=
    fun c hc => (mem_closeCodewordsRel_iff.mp (hS c hc)).1
  have herr : ∀ c ∈ S, hammingDist c y ≤ e + fiberErrorExcess π c y := by
    intro c hc
    have hd := (mem_closeCodewordsRel_iff.mp (hS c hc)).2
    rw [relHammingDist_coe, hn, hammingDist_comm] at hd
    have hcardPos : (0 : ℝ) < ((m * h : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos hm hhpos
    have hle : hammingDist c y ≤ e := by
      exact_mod_cast (div_le_div_iff_of_pos_right hcardPos).mp hd
    exact hle.trans (Nat.le_add_right e _)
  have hcard := folded_family_card_le_base_lambda D E π hm (fun _ => rfl) hf y S hcode herr
  simp only [Fintype.card_coe, hV] at hcard
  exact_mod_cast hcard.trans (hbase V hV sm)

/-! ### 2. Common `(k - 1)`-core star bound and saturated three-split locator pencils -/

private theorem nodal_dvd_of_eval_eq_zero {I F : Type*} [DecidableEq I] [Field F]
    (D : I ↪ F) {T : Finset I} {R : F[X]} (hroots : ∀ x ∈ T, R.eval (D x) = 0) :
    Lagrange.nodal T D ∣ R := by
  rw [Lagrange.nodal_eq]
  refine Finset.prod_dvd_of_coprime ?_ (fun x hx => Polynomial.dvd_iff_isRoot.mpr (hroots x hx))
  intro x _ y _ hne
  exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    (Ne.isUnit (sub_ne_zero.mpr (D.injective.ne hne)))

private theorem rs_eq_of_agree_card_ge {I F : Type*} [DecidableEq I] [Field F]
    (D : I ↪ F) {k : ℕ} {P Q : F[X]} (hP : P.natDegree < k) (hQ : Q.natDegree < k)
    {T : Finset I} (hT : k ≤ T.card) (hag : ∀ x ∈ T, P.eval (D x) = Q.eval (D x)) :
    P = Q := by
  by_contra hne
  have hroots : ∀ x ∈ T, (P - Q).eval (D x) = 0 := by
    intro x hx
    rw [eval_sub, hag x hx, sub_self]
  have hdiv := nodal_dvd_of_eval_eq_zero D hroots
  have hdeg := Polynomial.natDegree_le_of_dvd hdiv (sub_ne_zero.mpr hne)
  rw [Lagrange.natDegree_nodal] at hdeg
  have hsub := Polynomial.natDegree_sub_le P Q
  omega

/-- Common `(k - 1)`-core star bound: if `r` distinct `width`-interleaved codewords of degree `< k`
agree with `y` on sets `S a` (`|S a| ≥ t`) that all contain a fixed `(k - 1)`-subset `W`, then
their residual agreement sets `S a \ W` are pairwise disjoint inside `I \ W`, forcing
`r * (t - (k - 1)) ≤ |I| - (k - 1)`. -/
theorem common_core_star_bound {I F : Type*} [Fintype I] [DecidableEq I] [Field F]
    (D : I ↪ F) {r k t width : ℕ} (hk : 1 ≤ k)
    (c : Fin r → I → Fin width → F) (hinj : Function.Injective c)
    (hcode : ∀ a, c a ∈ interleavedCodeSet (κ := Fin width)
      (ReedSolomon.code D k : Set (I → F)))
    (y : I → Fin width → F) (S : Fin r → Finset I) (ht : ∀ a, t ≤ (S a).card)
    (hag : ∀ a, ∀ x ∈ S a, c a x = y x)
    (W : Finset I) (hWcard : W.card = k - 1) (hWsub : ∀ a, W ⊆ S a) :
    r * (t - (k - 1)) ≤ Fintype.card I - (k - 1) := by
  let _ : NeZero k := ⟨by omega⟩
  have hdisj : (Set.univ : Set (Fin r)).PairwiseDisjoint (fun a => S a \ W) := by
    intro a _ b _ hab
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hxa hxb
    obtain ⟨hxSa, hxW⟩ := mem_sdiff.mp hxa
    obtain ⟨hxSb, _⟩ := mem_sdiff.mp hxb
    apply hab
    apply hinj
    funext i col
    obtain ⟨Pa, hPa, hevalA⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hcode a col)
    obtain ⟨Pb, hPb, hevalB⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hcode b col)
    have hPeq : Pa = Pb := by
      apply rs_eq_of_agree_card_ge D hPa hPb (T := insert x W)
      · rw [card_insert_of_notMem hxW, hWcard]
        omega
      · intro z hz
        rcases mem_insert.mp hz with hzx | hzW
        · rw [hzx]
          exact (hevalA x).trans ((congrFun (hag a x hxSa) col).trans
            ((congrFun (hag b x hxSb) col).symm.trans (hevalB x).symm))
        · exact (hevalA z).trans ((congrFun (hag a z (hWsub a hzW)) col).trans
            ((congrFun (hag b z (hWsub b hzW)) col).symm.trans (hevalB z).symm))
    exact (hevalA i).symm.trans ((congrArg (Polynomial.eval (D i)) hPeq).trans (hevalB i))
  have hsub : univ.biUnion (fun a : Fin r => S a \ W) ⊆ univ \ W := by
    intro x hx
    obtain ⟨a, _, hxa⟩ := mem_biUnion.mp hx
    exact mem_sdiff.mpr ⟨mem_univ x, (mem_sdiff.mp hxa).2⟩
  have hsum : ∑ a : Fin r, (S a \ W).card ≤ Fintype.card I - (k - 1) := by
    rw [← card_biUnion (fun a _ b _ hab => hdisj (Set.mem_univ a) (Set.mem_univ b) hab)]
    refine (card_le_card hsub).trans ?_
    rw [card_sdiff_of_subset (subset_univ W), card_univ, hWcard]
  calc
    r * (t - (k - 1)) = ∑ _a : Fin r, (t - (k - 1)) := by
      simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ ∑ a : Fin r, (S a \ W).card := by
      refine sum_le_sum fun a _ => ?_
      rw [card_sdiff_of_subset (hWsub a), hWcard]
      exact Nat.sub_le_sub_right (ht a) (k - 1)
    _ ≤ Fintype.card I - (k - 1) := hsum

private theorem eq_C_mul_nodal_of_saturated {I F : Type*} [DecidableEq I] [Field F]
    (D : I ↪ F) {k : ℕ} {P Q : F[X]} (hne : P ≠ Q) (hP : P.natDegree < k)
    (hQ : Q.natDegree < k) {T : Finset I} (hT : T.card = k - 1)
    (hroots : ∀ x ∈ T, (P - Q).eval (D x) = 0) :
    ∃ c : F, c ≠ 0 ∧ P - Q = C c * Lagrange.nodal T D := by
  have hdiv := nodal_dvd_of_eval_eq_zero D hroots
  obtain ⟨R, hmul⟩ := hdiv
  have hsubNe : P - Q ≠ 0 := sub_ne_zero.mpr hne
  have hRne : R ≠ 0 := right_ne_zero_of_mul (hmul ▸ hsubNe)
  have hdegMul := Polynomial.natDegree_mul (Lagrange.nodal_ne_zero (s := T) (v := D)) hRne
  have hdegSub := Polynomial.natDegree_sub_le P Q
  rw [← hmul, Lagrange.natDegree_nodal, hT] at hdegMul
  have hRdeg : R.natDegree = 0 := by omega
  have hRC := Polynomial.eq_C_of_natDegree_eq_zero hRdeg
  refine ⟨R.coeff 0, ?_, ?_⟩
  · intro hc0
    apply hRne
    rw [hRC, hc0, map_zero]
  · conv_lhs => rw [hmul, hRC, mul_comm]

/-- Saturated-triangle three-split locator pencil theorem: if three distinct polynomials of degree
`< k` agree with `y` on sets `S₀, S₁, S₂` (`|S_i| ≥ t`) with all three pairwise overlaps equal to
`k - 1` and triple intersection `|S₀ ∩ S₁ ∩ S₂| < k - 1`, then the residual pairwise overlaps
`A, B, C_set` form three pairwise disjoint subsets of `I \ (S₀ ∩ S₁ ∩ S₂)` of equal positive size
`m = k - 1 - |S₀ ∩ S₁ ∩ S₂|` (`m + |I| + 2 * (k - 1) ≥ 3 * t`) whose monic nodal polynomials
satisfy `Lagrange.nodal C_set D = C μ * Lagrange.nodal A D + C (1 - μ) * Lagrange.nodal B D`
for some `μ ∈ F \ {0, 1}`. -/
theorem saturated_triangle_three_split_pencil {I F : Type*} [Fintype I] [DecidableEq I] [Field F]
    (D : I ↪ F) {k t : ℕ} {P₀ P₁ P₂ : F[X]} (h01 : P₀ ≠ P₁) (h12 : P₁ ≠ P₂) (h20 : P₂ ≠ P₀)
    (hdeg₀ : P₀.natDegree < k) (hdeg₁ : P₁.natDegree < k) (hdeg₂ : P₂.natDegree < k)
    (y : I → F) {S₀ S₁ S₂ : Finset I}
    (ht₀ : t ≤ S₀.card) (ht₁ : t ≤ S₁.card) (ht₂ : t ≤ S₂.card)
    (hag₀ : ∀ x ∈ S₀, P₀.eval (D x) = y x)
    (hag₁ : ∀ x ∈ S₁, P₁.eval (D x) = y x)
    (hag₂ : ∀ x ∈ S₂, P₂.eval (D x) = y x)
    (hsat₀₁ : (S₀ ∩ S₁).card = k - 1)
    (hsat₁₂ : (S₁ ∩ S₂).card = k - 1)
    (hsat₂₀ : (S₂ ∩ S₀).card = k - 1)
    (htriple : (S₀ ∩ S₁ ∩ S₂).card < k - 1) :
    let W := S₀ ∩ S₁ ∩ S₂
    let m := k - 1 - W.card
    let A := (S₀ ∩ S₁) \ W
    let B := (S₁ ∩ S₂) \ W
    let C_set := (S₂ ∩ S₀) \ W
    1 ≤ m ∧ 3 * t ≤ m + Fintype.card I + 2 * (k - 1) ∧
      A.card = m ∧ B.card = m ∧ C_set.card = m ∧
      Disjoint A B ∧ Disjoint B C_set ∧ Disjoint C_set A ∧
      ∃ μ : F, μ ≠ 0 ∧ μ ≠ 1 ∧
        Lagrange.nodal C_set D =
          C μ * Lagrange.nodal A D + C (1 - μ) * Lagrange.nodal B D := by
  let W := S₀ ∩ S₁ ∩ S₂
  let m := k - 1 - W.card
  let A := (S₀ ∩ S₁) \ W
  let B := (S₁ ∩ S₂) \ W
  let C_set := (S₂ ∩ S₀) \ W
  have hW₀₁ : W ⊆ S₀ ∩ S₁ := inter_subset_left
  have hW₁₂ : W ⊆ S₁ ∩ S₂ := fun x hx =>
    mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hx).1).2, (mem_inter.mp hx).2⟩
  have hW₂₀ : W ⊆ S₂ ∩ S₀ := fun x hx =>
    mem_inter.mpr ⟨(mem_inter.mp hx).2, (mem_inter.mp (mem_inter.mp hx).1).1⟩
  have hcardA : A.card = m := by rw [card_sdiff_of_subset hW₀₁, hsat₀₁]
  have hcardB : B.card = m := by rw [card_sdiff_of_subset hW₁₂, hsat₁₂]
  have hcardC : C_set.card = m := by rw [card_sdiff_of_subset hW₂₀, hsat₂₀]
  have hm1 : 1 ≤ m := by dsimp only [m, W]; omega
  have hie : 3 * t ≤ m + Fintype.card I + 2 * (k - 1) := by
    have hu1 := card_union_add_card_inter S₀ (S₁ ∪ S₂)
    have hu2 := card_union_add_card_inter S₁ S₂
    have hdistr : S₀ ∩ (S₁ ∪ S₂) = (S₀ ∩ S₁) ∪ (S₂ ∩ S₀) := by
      ext x
      simp only [mem_inter, mem_union]
      tauto
    have hinter3 : (S₀ ∩ S₁) ∩ (S₂ ∩ S₀) = W := by
      ext x
      simp only [W, mem_inter]
      tauto
    have hu3 := card_union_add_card_inter (S₀ ∩ S₁) (S₂ ∩ S₀)
    rw [← hdistr, hinter3, hsat₀₁, hsat₂₀] at hu3
    rw [hsat₁₂] at hu2
    have hunion_le : (S₀ ∪ (S₁ ∪ S₂)).card ≤ Fintype.card I := card_le_univ _
    have hWl : W.card < k - 1 := htriple
    dsimp only [m]
    omega
  have hdisAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨hx01, hxW⟩ := mem_sdiff.mp hxA
    obtain ⟨hx12, _⟩ := mem_sdiff.mp hxB
    exact hxW (mem_inter.mpr ⟨hx01, (mem_inter.mp hx12).2⟩)
  have hdisBC : Disjoint B C_set := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    obtain ⟨hx12, hxW⟩ := mem_sdiff.mp hxB
    obtain ⟨hx20, _⟩ := mem_sdiff.mp hxC
    exact hxW (mem_inter.mpr ⟨mem_inter.mpr ⟨(mem_inter.mp hx20).2, (mem_inter.mp hx12).1⟩,
      (mem_inter.mp hx12).2⟩)
  have hdisCA : Disjoint C_set A := by
    rw [Finset.disjoint_left]
    intro x hxC hxA
    obtain ⟨hx20, hxW⟩ := mem_sdiff.mp hxC
    obtain ⟨hx01, _⟩ := mem_sdiff.mp hxA
    exact hxW (mem_inter.mpr ⟨hx01, (mem_inter.mp hx20).1⟩)
  obtain ⟨c₀₁, hc₀₁, hfac₀₁⟩ := eq_C_mul_nodal_of_saturated D h01 hdeg₀ hdeg₁ hsat₀₁
    (fun x hx => by
      rw [eval_sub, hag₀ x (mem_inter.mp hx).1, hag₁ x (mem_inter.mp hx).2, sub_self])
  obtain ⟨c₁₂, hc₁₂, hfac₁₂⟩ := eq_C_mul_nodal_of_saturated D h12 hdeg₁ hdeg₂ hsat₁₂
    (fun x hx => by
      rw [eval_sub, hag₁ x (mem_inter.mp hx).1, hag₂ x (mem_inter.mp hx).2, sub_self])
  obtain ⟨c₂₀, hc₂₀, hfac₂₀⟩ := eq_C_mul_nodal_of_saturated D h20 hdeg₂ hdeg₀ hsat₂₀
    (fun x hx => by
      rw [eval_sub, hag₂ x (mem_inter.mp hx).1, hag₀ x (mem_inter.mp hx).2, sub_self])
  have split_nodal {T : Finset I} (hWT : W ⊆ T) :
      Lagrange.nodal T D = Lagrange.nodal W D * Lagrange.nodal (T \ W) D := by
    have hunion : W ∪ (T \ W) = T := union_sdiff_of_subset hWT
    have hdis : Disjoint W (T \ W) := disjoint_sdiff_self_right
    conv_lhs => rw [← hunion]
    simp only [Lagrange.nodal_eq, Finset.prod_union hdis]
  rw [split_nodal hW₀₁] at hfac₀₁
  rw [split_nodal hW₁₂] at hfac₁₂
  rw [split_nodal hW₂₀] at hfac₂₀
  have hsum_zero :
      Lagrange.nodal W D *
        (C c₀₁ * Lagrange.nodal A D + C c₁₂ * Lagrange.nodal B D +
          C c₂₀ * Lagrange.nodal C_set D) = 0 := by
    have htel : (P₀ - P₁) + (P₁ - P₂) + (P₂ - P₀) = 0 := by ring
    rw [hfac₀₁, hfac₁₂, hfac₂₀] at htel
    dsimp only [A, B, C_set]
    linear_combination htel
  have hpencil : C c₀₁ * Lagrange.nodal A D + C c₁₂ * Lagrange.nodal B D +
      C c₂₀ * Lagrange.nodal C_set D = 0 :=
    (mul_eq_zero.mp hsum_zero).resolve_left (Lagrange.nodal_ne_zero (s := W) (v := D))
  have hcoeff_sum : c₀₁ + c₁₂ + c₂₀ = 0 := by
    have hc := congrArg (fun p : F[X] => p.coeff m) hpencil
    have hlead {T : Finset I} (hT : T.card = m) (c : F) :
        (C c * Lagrange.nodal T D).coeff m = c := by
      rw [coeff_C_mul, ← hT, ← Lagrange.natDegree_nodal (s := T) (v := D),
        Lagrange.nodal_monic.coeff_natDegree, mul_one]
    simpa only [coeff_add, coeff_zero, hlead hcardA, hlead hcardB, hlead hcardC] using hc
  let μ : F := -c₀₁ / c₂₀
  have hμ0 : μ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hc₀₁) hc₂₀
  have h1sub : 1 - μ = -c₁₂ / c₂₀ := by
    dsimp only [μ]
    field_simp
    linear_combination hcoeff_sum
  have hμ1 : μ ≠ 1 := by
    intro h1
    have hzero : 1 - μ = 0 := sub_eq_zero.mpr h1.symm
    rw [h1sub] at hzero
    exact div_ne_zero (neg_ne_zero.mpr hc₁₂) hc₂₀ hzero
  have hrel : Lagrange.nodal C_set D =
      C μ * Lagrange.nodal A D + C (1 - μ) * Lagrange.nodal B D := by
    rw [h1sub]
    have hscale : C (-c₂₀⁻¹) * (C c₀₁ * Lagrange.nodal A D + C c₁₂ * Lagrange.nodal B D +
        C c₂₀ * Lagrange.nodal C_set D) = 0 := by
      rw [hpencil, mul_zero]
    have hcC : C (-c₂₀⁻¹) * C c₂₀ = -1 := by
      rw [← map_mul, neg_mul, inv_mul_cancel₀ hc₂₀, map_neg, map_one]
    have hcA : C (-c₂₀⁻¹) * C c₀₁ = C (-c₀₁ / c₂₀) := by
      rw [← map_mul]
      congr 1
      ring
    have hcB : C (-c₂₀⁻¹) * C c₁₂ = C (-c₁₂ / c₂₀) := by
      rw [← map_mul]
      congr 1
      ring
    have hexp : C (-c₀₁ / c₂₀) * Lagrange.nodal A D + C (-c₁₂ / c₂₀) * Lagrange.nodal B D -
        Lagrange.nodal C_set D = 0 := by
      calc
        C (-c₀₁ / c₂₀) * Lagrange.nodal A D + C (-c₁₂ / c₂₀) * Lagrange.nodal B D -
            Lagrange.nodal C_set D =
          (C (-c₂₀⁻¹) * C c₀₁) * Lagrange.nodal A D +
            (C (-c₂₀⁻¹) * C c₁₂) * Lagrange.nodal B D +
            (C (-c₂₀⁻¹) * C c₂₀) * Lagrange.nodal C_set D := by
          rw [hcA, hcB, hcC]
          ring
        _ = C (-c₂₀⁻¹) * (C c₀₁ * Lagrange.nodal A D + C c₁₂ * Lagrange.nodal B D +
            C c₂₀ * Lagrange.nodal C_set D) := by ring
        _ = 0 := hscale
    dsimp only [μ]
    linear_combination -hexp
  exact ⟨hm1, hie, hcardA, hcardB, hcardC, hdisAB, hdisBC, hdisCA, μ, hμ0, hμ1, hrel⟩

/-- Whenever `|I| - (k - 1) < 4 * (t - (k - 1))` (in particular at production length `2^30` for
rates `1/2`, `1/4`, and `1/8` at `J + 1`), every saturated `4`-clique `(P₀, P₁, P₂, P₃)` forces a
positive-degree three-split monic locator pencil on `D`. -/
theorem saturated_four_clique_forces_three_split_pencil {I F : Type*} [Fintype I] [DecidableEq I]
    [Field F] (D : I ↪ F) {k t : ℕ} (hk : 1 ≤ k)
    (hstar : Fintype.card I - (k - 1) < 4 * (t - (k - 1)))
    (P : Fin 4 → F[X]) (hinj : Function.Injective P) (hdeg : ∀ a, (P a).natDegree < k)
    (y : I → F) (S : Fin 4 → Finset I) (ht : ∀ a, t ≤ (S a).card)
    (hag : ∀ a, ∀ x ∈ S a, (P a).eval (D x) = y x)
    (hsat : ∀ a b, a ≠ b → (S a ∩ S b).card = k - 1) :
    ∃ (A B C_set : Finset I) (m : ℕ) (μ : F),
      1 ≤ m ∧ A.card = m ∧ B.card = m ∧ C_set.card = m ∧
      Disjoint A B ∧ Disjoint B C_set ∧ Disjoint C_set A ∧
      μ ≠ 0 ∧ μ ≠ 1 ∧
      Lagrange.nodal C_set D = C μ * Lagrange.nodal A D + C (1 - μ) * Lagrange.nodal B D := by
  have htri : (S 0 ∩ S 1 ∩ S 2).card < k - 1 ∨ (S 0 ∩ S 1 ∩ S 3).card < k - 1 := by
    by_contra! hboth
    have heq2 : S 0 ∩ S 1 ∩ S 2 = S 0 ∩ S 1 :=
      eq_of_subset_of_card_le inter_subset_left (by rw [hsat 0 1 (by decide)]; exact hboth.1)
    have heq3 : S 0 ∩ S 1 ∩ S 3 = S 0 ∩ S 1 :=
      eq_of_subset_of_card_le inter_subset_left (by rw [hsat 0 1 (by decide)]; exact hboth.2)
    let W := S 0 ∩ S 1
    have hWsub : ∀ a : Fin 4, W ⊆ S a := by
      intro a
      dsimp only [W]
      fin_cases a
      · exact inter_subset_left
      · exact inter_subset_right
      · rw [← heq2]; exact inter_subset_right
      · rw [← heq3]; exact inter_subset_right
    let c (a : Fin 4) (i : I) (_ : Fin 1) : F := (P a).eval (D i)
    have hcinj : Function.Injective c := by
      intro a b hab
      apply hinj
      refine rs_eq_of_agree_card_ge D (hdeg a) (hdeg b) (T := univ) ?_
        (fun x _ => congrFun (congrFun hab x) 0)
      rw [card_univ]
      have hsub : S 0 ⊆ univ := subset_univ _
      have hs0 := card_le_card hsub
      rw [card_univ] at hs0
      have ht0 := ht 0
      omega
    have hccode (a : Fin 4) : c a ∈ interleavedCodeSet (κ := Fin 1)
        (ReedSolomon.code D k : Set (I → F)) := by
      intro _
      exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (P a) (hdeg a)
        (fun _ => rfl)
    have hstar_le := common_core_star_bound D hk c hcinj hccode (fun x _ => y x) S ht
      (fun a x hx => funext fun _ => hag a x hx) W (hsat 0 1 (by decide)) hWsub
    omega
  rcases htri with h2 | h3
  · obtain ⟨hm1, _, hcA, hcB, hcC, hdAB, hdBC, hdCA, μ, hμ0, hμ1, hp⟩ :=
      saturated_triangle_three_split_pencil D
        (hinj.ne (by decide : (0 : Fin 4) ≠ 1))
        (hinj.ne (by decide : (1 : Fin 4) ≠ 2))
        (hinj.ne (by decide : (2 : Fin 4) ≠ 0))
        (hdeg 0) (hdeg 1) (hdeg 2) y (ht 0) (ht 1) (ht 2) (hag 0) (hag 1) (hag 2)
        (hsat 0 1 (by decide)) (hsat 1 2 (by decide)) (hsat 2 0 (by decide)) h2
    exact ⟨_, _, _, _, μ, hm1, hcA, hcB, hcC, hdAB, hdBC, hdCA, hμ0, hμ1, hp⟩
  · obtain ⟨hm1, _, hcA, hcB, hcC, hdAB, hdBC, hdCA, μ, hμ0, hμ1, hp⟩ :=
      saturated_triangle_three_split_pencil D
        (hinj.ne (by decide : (0 : Fin 4) ≠ 1))
        (hinj.ne (by decide : (1 : Fin 4) ≠ 3))
        (hinj.ne (by decide : (3 : Fin 4) ≠ 0))
        (hdeg 0) (hdeg 1) (hdeg 3) y (ht 0) (ht 1) (ht 3) (hag 0) (hag 1) (hag 3)
        (hsat 0 1 (by decide)) (hsat 1 3 (by decide)) (hsat 3 0 (by decide)) h3
    exact ⟨_, _, _, _, μ, hm1, hcA, hcB, hcC, hdAB, hdBC, hdCA, hμ0, hμ1, hp⟩

/-! ### 3. Multi-step mixed inclusion–omission bounds at `J + 2` and `J + 3` -/

/-- Exact all-`k`, all-`s` identity at rate `1/16` (`n = 16 * k`, `d = k - 1`, `t = 4 * k - 2 - s`
corresponding to `Johnson + s` errors): pure `s`-site inclusion (`r = 0`) leaves strictly positive
Johnson slack `s * k + (3 * s + 4) * (s + 1) > 0` for every `s ≥ 1`. -/
theorem rate_sixteenth_inclusion_family_gap {k s : ℕ} (hs : 1 ≤ s) (hsk : s + 1 ≤ k)
    (hst : 2 * s + 2 ≤ 4 * k) :
    (4 * k - 2 - 2 * s) ^ 2 =
      (16 * k - s) * (k - 1 - s) + (s * k + (3 * s + 4) * (s + 1)) ∧
    (16 * k - s) * (k - 1 - s) < (4 * k - 2 - 2 * s) ^ 2 := by
  have hid : (4 * k - 2 - 2 * s) ^ 2 =
      (16 * k - s) * (k - 1 - s) + (s * k + (3 * s + 4) * (s + 1)) := by
    have h1 : 2 + 2 * s ≤ 4 * k := by omega
    have h2 : s ≤ 16 * k := by omega
    have h3 : 1 + s ≤ k := by omega
    rw [Nat.sub_sub, Nat.sub_sub]
    zify [h1, h2, h3]
    ring
  refine ⟨hid, ?_⟩
  rw [hid]
  have hpos : 0 < s * k + (3 * s + 4) * (s + 1) := by positivity
  omega

private theorem atErrors_of_mixed {F : Type*} [Field F]
    (D : Fin 1073741824 ↪ F) (width k e t s r B : ℕ)
    (he : e + t = 1073741824) (hts : s + 1 ≤ t)
    (hstrict : (1073741824 - s - r) * (k - 1 - s) < (t - s) ^ 2)
    (hbudget : (1073741824 : ℕ).choose s * (1073741824 - s).choose r *
        (1073741824 - s - r) <
      (B + 1) * (t.choose s * (1073741824 - t).choose r)) :
    AtErrors D width k e B := by
  apply MixedInclusionOmissionJohnson.list_le_of_inclusion_omission
    D k t width s r B ((e : ℝ) / 1073741824) hts
  · simp only [Fintype.card_fin, Nat.cast_ofNat]
    have hsum : (e : ℝ) + t = 1073741824 := by exact_mod_cast he
    linarith
  · simpa only [Fintype.card_fin] using hstrict
  · simpa only [Fintype.card_fin] using hbudget

/-- Rate `1/8`, second step beyond Johnson (`e = 694,116,764`): pure 2-site inclusion
(`s = 2, r = 0`) certifies list size `≤ 8,589,934,703` (`8.00 n`), improving
`MultipleOmissionJohnson.eighth_second_step` (`22,763,326,668`) by `2.65×` across all fields,
all injective domains, and all interleaving widths. -/
theorem rate_eighth_johnson_plus_two {F : Type*} [Field F]
    (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 134217728 694116764 8589934703 :=
  atErrors_of_mixed D width 134217728 694116764 379625060 2 0 8589934703
    (by decide) (by decide) (by decide)
    (by simp only [Nat.choose_eq_descFactorial_div_factorial]; decide)

/-- Rate `1/8`, third step beyond Johnson (`e = 694,116,765`): mixed `(s = 3, r = 2)`
certifies list size `≤ 58,139,264,338` (`54.15 n`, `3.47×` below pure omission's `187.76 n`). -/
theorem rate_eighth_johnson_plus_three {F : Type*} [Field F]
    (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 134217728 694116765 58139264338 :=
  atErrors_of_mixed D width 134217728 694116765 379625059 3 2 58139264338
    (by decide) (by decide) (by decide)
    (by simp only [Nat.choose_eq_descFactorial_div_factorial]; decide)

/-- Rate `1/16`, second step beyond Johnson (`e = 805,306,372`): pure 2-site inclusion
(`s = 2, r = 0`) certifies list size `≤ 17,179,869,712` (`16.00 n`, `8.31×` below pure omission's
`133.03 n`). -/
theorem rate_sixteenth_johnson_plus_two {F : Type*} [Field F]
    (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 67108864 805306372 17179869712 :=
  atErrors_of_mixed D width 67108864 805306372 268435452 2 0 17179869712
    (by decide) (by decide) (by decide)
    (by simp only [Nat.choose_eq_descFactorial_div_factorial]; decide)

/-- Rate `1/16`, third step beyond Johnson (`e = 805,306,373`): pure 3-site inclusion
(`s = 3, r = 0`) certifies list size `≤ 68,719,480,960` (`64.00 n`, `15.57×` below pure omission's
`996.62 n`). -/
theorem rate_sixteenth_johnson_plus_three {F : Type*} [Field F]
    (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 67108864 805306373 68719480960 :=
  atErrors_of_mixed D width 67108864 805306373 268435451 3 0 68719480960
    (by decide) (by decide) (by decide)
    (by simp only [Nat.choose_eq_descFactorial_div_factorial]; decide)

end ProximityGap.CarbonListSmoothFoldedRigidity

#print axioms ProximityGap.CarbonListSmoothFoldedRigidity.sum_foldSlice_comp
#print axioms ProximityGap.CarbonListSmoothFoldedRigidity.eval_eq_on_fiber_iff_folded
#print axioms ProximityGap.CarbonListSmoothFoldedRigidity.hammingDist_add_fiberExcess_eq
#print axioms ProximityGap.CarbonListSmoothFoldedRigidity.folded_family_card_le_base_lambda
#print axioms ProximityGap.CarbonListSmoothFoldedRigidity.smooth_folded_low_error_lambda_le
#print axioms ProximityGap.CarbonListSmoothFoldedRigidity.common_core_star_bound
#print axioms ProximityGap.CarbonListSmoothFoldedRigidity.saturated_triangle_three_split_pencil
open ProximityGap.CarbonListSmoothFoldedRigidity in
#print axioms saturated_four_clique_forces_three_split_pencil
#print axioms ProximityGap.CarbonListSmoothFoldedRigidity.rate_sixteenth_inclusion_family_gap
#print axioms ProximityGap.CarbonListSmoothFoldedRigidity.rate_eighth_johnson_plus_two
#print axioms ProximityGap.CarbonListSmoothFoldedRigidity.rate_eighth_johnson_plus_three
#print axioms ProximityGap.CarbonListSmoothFoldedRigidity.rate_sixteenth_johnson_plus_two
#print axioms ProximityGap.CarbonListSmoothFoldedRigidity.rate_sixteenth_johnson_plus_three
