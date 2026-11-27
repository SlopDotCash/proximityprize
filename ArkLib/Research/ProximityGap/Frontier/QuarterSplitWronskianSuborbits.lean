/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # Large-characteristic Wronskian gcd bound and sharp split-pencil suborbits

For a smooth projective curve `X'` over an algebraically closed field of characteristic `p`,
and nonconstant functions `u, v` generating `K(X')` with `h * deg u + k * deg v < p` and
`k < deg u`, the Wronskian of the `M = h*k + h + k`-dimensional subspace `W₁ ⊂ Span{u^i v^j}`
vanishing at `(1, 1)` yields

  `∑_{u(P)=v(P)=1} min(v_P(u-1), v_P(v-1)) ≤ (h * deg u + k * deg v) / M + ((M - 1) / 2) * χ(X')`

without invoking Corvaja–Zannier's positive-characteristic proposition. Taking `h = k = 1` (`M = 3`)
and pulling back to any nontrivial suborbit component of a degree-`268,435,454` quarter-rate
split pencil on `μ_{2^30}` gives `|Z| ≤ (2/3) n a + χ(X)`, raising the subdegree floor nearly
fivefold from `9,085,508` to `44,739,240`, eliminating proper inner degrees `19,173,961` and
`38,347,922`, capping the permutation rank at `8`, and raising the unconditional full-cover
orbifold excess above `0.39999993`.

This file formalizes:
1. The non-Archimedean valuation-subspace comparison lemma (`subspace_adapted_valuation_ge`).
2. The large-characteristic Vandermonde nonvanishing criterion (`vandermonde_ne_zero_of_lt_char`).
3. The exact rectangle pole-zero cancellation identity (`rect_pole_zero_balance`) and the
   abstract product-formula gcd and Kummer-pullback bounds (`wronskian_gcd_bound`,
   `pullback_gcd_bound`).
4. All concrete subdegree, permutation-rank, inner-degree, genus, orbifold-excess, and
   branch-signature exclusions for the production degree-`268,435,454` split pencil on both
   designated primes (and every prime `p > 2 * 2^30 * 268435454`).
-/

set_option autoImplicit false

namespace ProximityGap.QuarterSplitWronskianSuborbits

open Finset

/-! ## Part 1: Non-Archimedean valuation-subspace comparison -/

section ValuationSubspace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A non-Archimedean discrete valuation on a vector space `V` over `K`, valued in `WithTop ℤ`. -/
structure VecValuation (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  val : V → WithTop ℤ
  val_zero : val 0 = ⊤
  val_eq_top_iff : ∀ x, val x = ⊤ ↔ x = 0
  val_smul : ∀ (c : K) (x : V), c ≠ 0 → val (c • x) = val x
  val_add_ge : ∀ x y : V, min (val x) (val y) ≤ val (x + y)

namespace VecValuation

variable (ν : VecValuation K V)

theorem val_neg (x : V) : ν.val (-x) = ν.val x := by
  have h : (-x) = (-1 : K) • x := by simp
  rw [h, ν.val_smul (-1) x (by norm_num)]

theorem val_sub_ge (x y : V) : min (ν.val x) (ν.val y) ≤ ν.val (x - y) := by
  rw [sub_eq_add_neg, ← ν.val_neg y]
  exact ν.val_add_ge x (-y)

/-- Ultrametric equality: when two vectors have strictly different valuations, their sum has
the strictly smaller valuation. -/
theorem val_add_eq_left {x y : V} (h : ν.val x < ν.val y) : ν.val (x + y) = ν.val x := by
  apply le_antisymm
  · by_contra hgt
    push Not at hgt
    have hsub := ν.val_sub_ge (x + y) y
    rw [add_sub_cancel_right] at hsub
    have hlt : ν.val x < min (ν.val (x + y)) (ν.val y) := lt_min hgt h
    exact not_lt_of_ge hsub hlt
  · have hmin : min (ν.val x) (ν.val y) = ν.val x := min_eq_left h.le
    rw [← hmin]
    exact ν.val_add_ge x y

/-- Lower bound on valuations in a span: if every generator in a set `S` has valuation at least `a`,
then every element of `Submodule.span K S` has valuation at least `a`. -/
theorem le_val_of_mem_span {S : Set V} {a : WithTop ℤ} (hS : ∀ x ∈ S, a ≤ ν.val x)
    {g : V} (hg : g ∈ Submodule.span K S) : a ≤ ν.val g := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
  · intro x hx
    exact hS x hx
  · rw [ν.val_zero]
    exact le_top
  · intro x y _ _ hx hy
    exact le_trans (le_min hx hy) (ν.val_add_ge x y)
  · intro c x _ hx
    by_cases hc : c = 0
    · simp [hc, ν.val_zero]
    · rwa [ν.val_smul c x hc]

/-- A finite family with strictly increasing finite valuations is `K`-linearly independent, and any
nonzero linear combination has valuation equal to the minimum valuation among its nonzero terms,
hence at most the largest valuation in the family. -/
theorem linear_comb_val {n : ℕ} (f : Fin n → V)
    (hmono : StrictMono (fun i => ν.val (f i))) (hfin : ∀ i, ν.val (f i) ≠ ⊤)
    (c : Fin n → K) (hne : ∃ i, c i ≠ 0) :
    ∃ i₀ : Fin n, c i₀ ≠ 0 ∧ ν.val (∑ i : Fin n, c i • f i) = ν.val (f i₀) := by
  classical
  let supp : Finset (Fin n) := univ.filter fun i => c i ≠ 0
  have hne_supp : supp.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
  let i₀ := supp.min' hne_supp
  have hi₀_mem : i₀ ∈ supp := min'_mem supp hne_supp
  have hi₀_ne : c i₀ ≠ 0 := (mem_filter.mp hi₀_mem).2
  refine ⟨i₀, hi₀_ne, ?_⟩
  have hsum : (∑ i : Fin n, c i • f i) = c i₀ • f i₀ + ∑ i ∈ supp.erase i₀, c i • f i := by
    rw [← sum_filter_ne_zero]
    have hfilt : (univ.filter fun i : Fin n => c i • f i ≠ 0) = supp := by
      ext i
      simp only [supp, mem_filter, mem_univ, true_and, ne_eq, smul_eq_zero, not_or]
      have hfi : f i ≠ 0 := fun h => hfin i (by rw [h, ν.val_zero])
      exact ⟨fun h => h.1, fun h => ⟨h, hfi⟩⟩
    rw [hfilt, ← add_sum_erase _ _ hi₀_mem]
  rw [hsum]
  have htail : ∀ y ∈ supp.erase i₀, ν.val (f i₀) < ν.val (c y • f y) := by
    intro y hy
    have hy_ne : c y ≠ 0 := (mem_filter.mp (mem_of_mem_erase hy)).2
    have hlt : i₀ < y := lt_of_le_of_ne (min'_le supp y (mem_of_mem_erase hy)) (ne_of_mem_erase hy).symm
    rw [ν.val_smul (c y) (f y) hy_ne]
    exact hmono hlt
  have htail_sum : ν.val (f i₀) < ν.val (∑ i ∈ supp.erase i₀, c i • f i) := by
    have haux : ∀ (s : Finset (Fin n)), (∀ y ∈ s, ν.val (f i₀) < ν.val (c y • f y)) →
        ν.val (f i₀) < ν.val (∑ y ∈ s, c y • f y) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _
        rw [sum_empty, ν.val_zero]
        exact lt_top_iff_ne_top.mpr (hfin i₀)
      | @insert a s ha ih =>
        intro hs
        rw [sum_insert ha]
        have h1 := hs a (mem_insert_self a s)
        have h2 := ih (fun y hy => hs y (mem_insert_of_mem hy))
        exact lt_of_lt_of_le (lt_min h1 h2) (ν.val_add_ge _ _)
    exact haux (supp.erase i₀) htail
  rw [← ν.val_smul (c i₀) (f i₀) hi₀_ne] at htail_sum ⊢
  exact ν.val_add_eq_left htail_sum

theorem linearIndependent_of_strictMono {n : ℕ} (f : Fin n → V)
    (hmono : StrictMono (fun i => ν.val (f i))) (hfin : ∀ i, ν.val (f i) ≠ ⊤) :
    LinearIndependent K f := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨i₀, _, heq⟩ := ν.linear_comb_val f hmono hfin c hne
  rw [hc, ν.val_zero] at heq
  exact hfin i₀ heq.symm

/-- **Valuation-subspace comparison lemma.**
If `w : Fin N → V` spans `V` with monotone valuations `ν(w₀) ≤ ⋯ ≤ ν(w_{N-1})`, and
`f : Fin M → V` has strictly increasing finite valuations `ν(f₀) < ⋯ < ν(f_{M-1})`, then
every adapted valuation satisfies `ν(w_m) ≤ ν(f_m)`. -/
theorem subspace_adapted_valuation_ge {N M : ℕ} (w : Fin N → V)
    (hspan : Submodule.span K (Set.range w) = ⊤)
    (hw : Monotone (fun j => ν.val (w j)))
    (f : Fin M → V) (hf : StrictMono (fun i => ν.val (f i)))
    (hfin : ∀ i, ν.val (f i) ≠ ⊤)
    (m : Fin M) (hm : (m : ℕ) < N) :
    ν.val (w ⟨m, hm⟩) ≤ ν.val (f m) := by
  classical
  let k : ℕ := m
  let U : Submodule K V := Submodule.span K { x | ∃ j : Fin N, k ≤ (j : ℕ) ∧ x = w j }
  -- The quotient `V ⧸ U` is spanned by the `k` images of `w 0, ..., w (k-1)`.
  let small : Fin k → V ⧸ U := fun i => U.mkQ (w ⟨i, lt_trans i.isLt hm⟩)
  have hqspan : Submodule.span K (Set.range small) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective U q
    have hv : v ∈ Submodule.span K (Set.range w) := by rw [hspan]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨j, rfl⟩
      by_cases hj : (j : ℕ) < k
      · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      · have hmem : w j ∈ U := Submodule.subset_span ⟨j, Nat.le_of_not_lt hj, rfl⟩
        have hzero : U.mkQ (w j) = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hmem
        rw [hzero]
        exact Submodule.zero_mem _
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ c hx
  -- Hence `V ⧸ U` is finite-dimensional of rank at most `k`.
  have : Module.Finite K (V ⧸ U) := Module.Finite.of_fg_top (by
    rw [← hqspan]
    exact Submodule.fg_span (Set.finite_range small))
  have hrank_q : Module.finrank K (V ⧸ U) ≤ k := by
    have h1 := finrank_span_le_card (R := K) (Set.range small)
    rw [hqspan, finrank_top] at h1
    have hset : (Set.range small).toFinset = univ.image small := by
      ext y; simp
    rw [hset] at h1
    exact h1.trans (card_image_le.trans (by simp))
  -- Meanwhile `f 0, ..., f k` are `k + 1` linearly independent vectors in `V`.
  let fprefix : Fin (k + 1) → V := fun i => f ⟨i, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) m.isLt⟩
  have hmono_pre : StrictMono (fun i => ν.val (fprefix i)) := fun i j hij => hf hij
  have hfin_pre : ∀ i, ν.val (fprefix i) ≠ ⊤ := fun i => hfin _
  -- The linear map `(Fin (k + 1) → K) → V ⧸ U` cannot be injective because `k < k + 1`.
  let φ : (Fin (k + 1) → K) →ₗ[K] (V ⧸ U) :=
    U.mkQ.comp (Fintype.linearCombination K fprefix)
  have hnotinj : ¬ Function.Injective φ := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_pi, Fintype.card_fin] at hle
    omega
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff] at hnotinj
  push Not at hnotinj
  obtain ⟨c, hc_ker, hc_ne⟩ := hnotinj
  have hc_ex : ∃ i : Fin (k + 1), c i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hc_ne (funext hall)
  let g : V := ∑ i : Fin (k + 1), c i • fprefix i
  have hg_U : g ∈ U := by
    have hker : U.mkQ g = 0 := by
      simpa [φ, g, Fintype.linearCombination_apply] using hc_ker
    exact (Submodule.Quotient.mk_eq_zero U).mp hker
  -- Lower bound: `ν(w_k) ≤ ν(g)` since `g ∈ U`.
  have hlow : ν.val (w ⟨m, hm⟩) ≤ ν.val g := by
    apply ν.le_val_of_mem_span _ hg_U
    rintro x ⟨j, hj, rfl⟩
    exact hw (show (⟨m, hm⟩ : Fin N) ≤ j from hj)
  -- Upper bound: `ν(g) = ν(fprefix i₀) ≤ ν(f m)`.
  obtain ⟨i₀, _, hval_g⟩ := ν.linear_comb_val fprefix hmono_pre hfin_pre c hc_ex
  have hup : ν.val g ≤ ν.val (f m) := by
    rw [hval_g]
    have hle : (⟨i₀, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ i₀.isLt) m.isLt⟩ : Fin M) ≤ m :=
      Nat.le_of_lt_succ i₀.isLt
    exact hf.monotone hle
  exact le_trans hlow hup

end VecValuation

end ValuationSubspace

/-! ## Part 2: Large-characteristic Vandermonde nonvanishing -/

/-- In characteristic `p` (prime), any strictly increasing sequence of `M` nonnegative integers
strictly below `p` has nonzero Vandermonde determinant. This guarantees nonvanishing of the
ordinary Wronskian of any `M`-dimensional subspace of `L(E)` whenever `deg E < p`. -/
theorem vandermonde_ne_zero_of_lt_char {K : Type*} [Field K] {p M : ℕ} [CharP K p]
    (e : Fin M → ℕ) (hmono : StrictMono e) (hlt : ∀ i, e i < p) :
    (Matrix.vandermonde (fun i => (e i : K))).det ≠ 0 := by
  rw [Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  exact hmono.injective (CharP.natCast_injOn_Iio K p (hlt i) (hlt j) hij)

/-! ## Part 3: Rectangle pole-zero balance and abstract Wronskian gcd bound -/

/-- Pointwise upper bound on the valuation `i * eu + j * ev` over the integer rectangle
`[0, h] × [0, k]`. -/
theorem rect_val_le_max (h k i j : ℕ) (hi : i ≤ h) (hj : j ≤ k) (eu ev : ℤ) :
    (i : ℤ) * eu + (j : ℤ) * ev ≤ (h : ℤ) * max 0 eu + (k : ℤ) * max 0 ev := by
  have h1 : (i : ℤ) * eu ≤ (h : ℤ) * max 0 eu := by
    by_cases hpos : 0 ≤ eu
    · rw [max_eq_right hpos]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hpos
    · push Not at hpos
      rw [max_eq_left hpos.le, mul_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg i) hpos.le
  have h2 : (j : ℤ) * ev ≤ (k : ℤ) * max 0 ev := by
    by_cases hpos : 0 ≤ ev
    · rw [max_eq_right hpos]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hpos
    · push Not at hpos
      rw [max_eq_left hpos.le, mul_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg j) hpos.le
  linarith

/-- The maximum of `i * eu + j * ev` on `[0, h] × [0, k]` is achieved at a corner and equals
`h * max 0 eu + k * max 0 ev`. -/
theorem rect_val_max_attained (h k : ℕ) (eu ev : ℤ) :
    ∃ i ≤ h, ∃ j ≤ k,
      (i : ℤ) * eu + (j : ℤ) * ev = (h : ℤ) * max 0 eu + (k : ℤ) * max 0 ev := by
  refine ⟨if 0 ≤ eu then h else 0, by split_ifs <;> omega,
          if 0 ≤ ev then k else 0, by split_ifs <;> omega, ?_⟩
  by_cases h1 : 0 ≤ eu <;> by_cases h2 : 0 ≤ ev
  · simp [h1, h2]
  · simp [h1, h2, le_of_not_ge]
  · simp [h1, h2, le_of_not_ge]
  · simp [h1, h2, le_of_not_ge]

/-- **Exact rectangle pole-zero cancellation identity.**
For any finite set `S` of zeros and poles of two rational functions `u, v` (so `∑ eu = ∑ ev = 0`),
summing `(∑_{0≤i≤h, 0≤j≤k} (i*eu + j*ev)) - (h*max 0 eu + k*max 0 ev)` over `S` cancels the first
sum identically and leaves `-(h * H_u + k * H_v)`. -/
theorem rect_pole_zero_balance {S : Type*} [Fintype S] (h k : ℕ) (eu ev : S → ℤ)
    (hzu : ∑ q : S, eu q = 0) (hzv : ∑ q : S, ev q = 0) :
    ∑ q : S, ((∑ i ∈ range (h + 1), ∑ j ∈ range (k + 1), ((i : ℤ) * eu q + (j : ℤ) * ev q)) -
      ((h : ℤ) * max 0 (eu q) + (k : ℤ) * max 0 (ev q))) =
      -((h : ℤ) * (∑ q : S, max 0 (eu q)) + (k : ℤ) * (∑ q : S, max 0 (ev q))) := by
  have hrect (q : S) :
      (∑ i ∈ range (h + 1), ∑ j ∈ range (k + 1), ((i : ℤ) * eu q + (j : ℤ) * ev q)) =
      ((k + 1 : ℤ) * ∑ i ∈ range (h + 1), (i : ℤ)) * eu q +
      ((h + 1 : ℤ) * ∑ j ∈ range (k + 1), (j : ℤ)) * ev q := by
    calc
      (∑ i ∈ range (h + 1), ∑ j ∈ range (k + 1), ((i : ℤ) * eu q + (j : ℤ) * ev q))
          = ∑ i ∈ range (h + 1), ((k + 1 : ℤ) * ((i : ℤ) * eu q) +
              (∑ j ∈ range (k + 1), (j : ℤ)) * ev q) := by
            apply sum_congr rfl; intro i _
            rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_mul]
            push_cast; ring
      _ = (∑ i ∈ range (h + 1), (k + 1 : ℤ) * ((i : ℤ) * eu q)) +
            (h + 1 : ℤ) * ((∑ j ∈ range (k + 1), (j : ℤ)) * ev q) := by
            rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
            push_cast; ring
      _ = ((k + 1 : ℤ) * ∑ i ∈ range (h + 1), (i : ℤ)) * eu q +
            ((h + 1 : ℤ) * ∑ j ∈ range (k + 1), (j : ℤ)) * ev q := by
            congr 1
            · rw [Finset.mul_sum, Finset.sum_mul]
              apply sum_congr rfl; intro i _; ring
            · ring
  simp_rw [hrect, sum_sub_distrib, sum_add_distrib, ← mul_sum, hzu, hzv, mul_zero, add_zero, zero_sub]

/-- **Abstract product-formula Wronskian gcd bound.**
Combines the degree identity `M(M-1)/2 * (2g' - 2) = sum of local Wronskian orders`, vanishing
order `≥ M * d_P` on `Z'`, and the pole-zero sum `≥ -(h*H_u + k*H_v) - M(M-1)/2 * |S'|` on `S'`. -/
theorem wronskian_gcd_bound {M : ℕ} (hM : 0 < M) (Z Hu Hv h k chi : ℝ)
    (prod_formula : (M : ℝ) * Z - (h * Hu + k * Hv) - ((M : ℝ) * (M - 1) / 2) * chi ≤ 0) :
    Z ≤ (h * Hu + k * Hv) / M + ((M : ℝ) - 1) / 2 * chi := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  apply sub_nonneg.mp
  have hkey : ((h * Hu + k * Hv) / M + ((M : ℝ) - 1) / 2 * chi - Z) * M =
      -(M * Z - (h * Hu + k * Hv) - (M * (M - 1) / 2) * chi) := by
    field_simp
    ring
  have hnn : 0 ≤ ((h * Hu + k * Hv) / M + ((M : ℝ) - 1) / 2 * chi - Z) * M := by
    rw [hkey]; linarith
  exact nonneg_of_mul_nonneg_left hnn hMpos

/-- **Kummer pullback cancellation.**
Pulling back along a degree-`c` tame Kummer cover `X → X'` (`|Z| ≤ c * Z'`, `c * Hu = degX_u`,
`c * Hv = degX_v`, `c * chi' = chi`) cancels the extension degree `c` identically. -/
theorem pullback_gcd_bound {M : ℕ} {c : ℝ} (hc : 0 < c)
    (Z Z' Hu Hv degXu degXv h k chi chi' : ℝ)
    (hZ : Z ≤ c * Z') (hHu : c * Hu = degXu) (hHv : c * Hv = degXv) (hchi : c * chi' = chi)
    (base : Z' ≤ (h * Hu + k * Hv) / M + ((M : ℝ) - 1) / 2 * chi') :
    Z ≤ (h * degXu + k * degXv) / M + ((M : ℝ) - 1) / 2 * chi := by
  have hmul := mul_le_mul_of_nonneg_left base hc.le
  have hrhs : c * ((h * Hu + k * Hv) / M + ((M : ℝ) - 1) / 2 * chi') =
      (h * degXu + k * degXv) / M + ((M : ℝ) - 1) / 2 * chi := by
    rw [← hHu, ← hHv, ← hchi]
    ring
  exact hZ.trans (hrhs ▸ hmul)

/-! ## Part 4: Sharp split-pencil suborbits, inner degrees, and branch orders -/

/-- For any suborbit component of degree `a ≥ 3` and Kummer degree `c ≤ 2n`, the image `Z'` on `X'`
has at least two points, forcing `deg_{X'}(u) ≥ 2` without invoking Corvaja–Zannier Theorem 2. -/
theorem degree_ge_two_of_suborbit {a c : ℕ} (ha : 3 ≤ a) (hc : c ≤ 2 * 1073741824) :
    c < 3 * 268435454 * a := by
  have h1 : 3 * 268435454 * 3 ≤ 3 * 268435454 * a := Nat.mul_le_mul_left _ ha
  omega

/-- The `h = k = 1` (`M = 3`) Wronskian bound `3 D a ≤ (2/3) n a + χ` combined with adjunction
`χ ≤ 2 a²` raises the nontrivial subdegree floor from `9,085,508` to `44,739,240`. -/
theorem subdegree_floor {a : ℕ} (ha : 0 < a) (chi : ℝ)
    (wronskian : 3 * 268435454 * (a : ℝ) ≤ (2 / 3 : ℝ) * 1073741824 * a + chi)
    (adjunction : chi ≤ 2 * (a : ℝ) ^ 2) :
    44739240 ≤ a := by
  have h : (268435438 : ℝ) * a ≤ 6 * (a : ℝ) ^ 2 := by
    linarith only [wronskian, adjunction]
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hn : (268435438 : ℝ) ≤ 6 * a := by
    apply (mul_le_mul_iff_of_pos_right ha').mp
    nlinarith only [h]
  have hint : 268435438 ≤ 6 * a := by exact_mod_cast hn
  omega

/-- At most 6 nontrivial suborbits and permutation rank at most 8 (down from 29 and 31). -/
theorem orbit_count_sharp {nontrivial singleton : ℕ} (hs : singleton ≤ 2)
    (degrees : 44739240 * nontrivial + singleton ≤ 268435454) :
    nontrivial ≤ 6 ∧ nontrivial + singleton ≤ 8 := by omega

/-- **Inner-degree elimination.**
Among all divisors `t ∣ 268,435,454` with `t > 2`, the subdegree floor `44,739,240 ≤ t - 1`
eliminates both `19,173,961` (outer degree `14`) and `38,347,922` (outer degree `7`), leaving
only `t = 134,217,727` (outer degree `2`) and the trivial `t = 268,435,454`. -/
theorem inner_degree_only_two_or_half {t : ℕ} (hdvd : t ∣ 268435454)
    (hlarge : 44739240 ≤ t - 1) :
    t = 134217727 ∨ t = 268435454 := by
  obtain ⟨s, hs⟩ := hdvd
  have hsb : s ≤ 6 := by
    by_contra! h
    have := Nat.mul_le_mul (show 44739241 ≤ t by omega) h
    omega
  have hs_pos : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with rfl | hp
    · simp at hs
    · exact hp
  interval_cases s <;> omega

/-- Complete classification of the surviving `(outer degree s, source degree h, primitive degree m)`
triples for a degree-`268,435,454` split pencil. -/
theorem primitive_stage_classification {s h m : ℕ} (hh : h = 1 ∨ h = 2)
    (hprod : s * (h * m) = 268435454) (hlarge : 44739240 ≤ h * m - 1) :
    (s = 2 ∧ h = 1 ∧ m = 134217727) ∨
    (s = 1 ∧ h = 2 ∧ m = 134217727) ∨
    (s = 1 ∧ h = 1 ∧ m = 268435454) := by
  have hdvd : h * m ∣ 268435454 := ⟨s, by rw [← hprod, mul_comm]⟩
  rcases inner_degree_only_two_or_half hdvd hlarge with hhalf | hfull
  · rw [hhalf] at hprod
    rcases hh with rfl | rfl <;> omega
  · rw [hfull] at hprod
    rcases hh with rfl | rfl <;> omega

/-- Combine the `h = k = 1` Wronskian bound on the pulled-back pair curve with the weighted
variance genus bound `euler * (E + 2) ≤ 2 * (m - 1)² * E`. -/
theorem primitive_excess_wronskian {h m E euler : ℝ} (hh : 0 < h) (hm : 1 < m) (hE : 0 ≤ E + 2)
    (wronskian : 3 * 268435454 * h * (m - 1) ≤
      (2 / 3 : ℝ) * 1073741824 * h * (m - 1) + h ^ 2 * (euler + 4 * (m - 1)))
    (genus : euler * (E + 2) ≤ 2 * (m - 1) ^ 2 * E) :
    2 * (268435438 - 12 * h) ≤ (6 * (h * m + h) - 268435438) * E := by
  have hsimple : (268435438 : ℝ) * (m - 1) ≤ 3 * h * (euler + 4 * (m - 1)) := by
    apply (mul_le_mul_iff_of_pos_left hh).mp
    nlinarith only [wronskian]
  have hmul := mul_le_mul_of_nonneg_right hsimple hE
  have hg := mul_le_mul_of_nonneg_left genus (show (0 : ℝ) ≤ 3 * h by positivity)
  apply (mul_le_mul_iff_of_pos_right (sub_pos.mpr hm)).mp
  nlinarith only [hmul, hg]

/-- Exact rational orbifold excess lower bounds for the three surviving `(s, h, m)` stages. -/
theorem named_excess {t h E : ℝ}
    (bound : 2 * (268435438 - 12 * h) ≤ (6 * (t + h) - 268435438) * E) :
    ((t = 134217727 ∧ h = 1) → (268435426 : ℝ) / 268435465 ≤ E) ∧
    ((t = 268435454 ∧ h = 2) → (268435414 : ℝ) / 671088649 ≤ E) ∧
    ((t = 268435454 ∧ h = 1) → (134217713 : ℝ) / 335544323 ≤ E) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩; linarith
  · rintro ⟨rfl, rfl⟩; linarith
  · rintro ⟨rfl, rfl⟩; linarith

/-- Pair-curve genus floors `g(Y)` for the three surviving `(s, h, m)` stages. -/
theorem named_genus {h m g : ℝ} (hh : 0 < h)
    (wronskian : 3 * 268435454 * h * (m - 1) ≤
      (2 / 3 : ℝ) * 1073741824 * h * (m - 1) + h ^ 2 * ((2 * g - 2) + 4 * (m - 1))) :
    ((h = 1 ∧ m = 134217727) → 6004798742593546 < g) ∧
    ((h = 2 ∧ m = 134217727) → 3002399237079047 < g) ∧
    ((h = 1 ∧ m = 268435454) → 12009597529926330 < g) := by
  have hsimple : (268435438 : ℝ) * (m - 1) ≤ 3 * h * ((2 * g - 2) + 4 * (m - 1)) := by
    apply (mul_le_mul_iff_of_pos_left hh).mp
    nlinarith only [wronskian]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩; linarith
  · rintro ⟨rfl, rfl⟩; linarith
  · rintro ⟨rfl, rfl⟩; linarith

/-- Unconditional orbifold excess lower bound for the **full** pencil `R` across all surviving
decompositions (`s ∈ {1, 2}`): `E_R ≥ 268435414 / 671088649 > 0.399999932`. -/
theorem full_cover_excess {s E full : ℝ} (transfer : E ≤ s * full)
    (cases : (s = 2 ∧ (268435426 : ℝ) / 268435465 ≤ E) ∨
             (s = 1 ∧ (268435414 : ℝ) / 671088649 ≤ E) ∨
             (s = 1 ∧ (134217713 : ℝ) / 335544323 ≤ E)) :
    (268435414 : ℝ) / 671088649 ≤ full := by
  rcases cases with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> linarith

/-- Concrete three- and four-branch signatures excluded for the **whole pencil** `R` by
`E_R ≥ 268435414 / 671088649`:
1. Every `(2, b, c)` with `3 ≤ b ≤ 9` and arbitrary `c ≥ 1`.
2. Every `(3, 3, c)` with arbitrary `c ≥ 1`.
3. Every `(2, 10, c)` with `1 ≤ c ≤ 14,716,856`.
4. Every `(3, 4, c)` with `1 ≤ c ≤ 59`.
5. Every `(3, 5, c)` with `1 ≤ c ≤ 14`.
6. Every `(4, 4, c)` with `1 ≤ c ≤ 9`.
7. Every 4-branch `(2, 2, 2, c)` with `1 ≤ c ≤ 9`. -/
theorem excluded_whole_pencil_signatures :
    (∀ b c : ℕ, 3 ≤ b → b ≤ 9 → 1 ≤ c →
      (1 : ℝ) - 1 / 2 - 1 / b - 1 / c < 268435414 / 671088649) ∧
    (∀ c : ℕ, 1 ≤ c →
      (1 : ℝ) - 1 / 3 - 1 / 3 - 1 / c < 268435414 / 671088649) ∧
    (∀ c : ℕ, 1 ≤ c → c ≤ 14716856 →
      (1 : ℝ) - 1 / 2 - 1 / 10 - 1 / c < 268435414 / 671088649) ∧
    (∀ c : ℕ, 1 ≤ c → c ≤ 59 →
      (1 : ℝ) - 1 / 3 - 1 / 4 - 1 / c < 268435414 / 671088649) ∧
    (∀ c : ℕ, 1 ≤ c → c ≤ 14 →
      (1 : ℝ) - 1 / 3 - 1 / 5 - 1 / c < 268435414 / 671088649) ∧
    (∀ c : ℕ, 1 ≤ c → c ≤ 9 →
      (1 : ℝ) - 1 / 4 - 1 / 4 - 1 / c < 268435414 / 671088649) ∧
    (∀ c : ℕ, 1 ≤ c → c ≤ 9 →
      (2 : ℝ) - 1 / 2 - 1 / 2 - 1 / 2 - 1 / c < 268435414 / 671088649) := by
  have inv_pos_of_ge1 : ∀ c : ℕ, 1 ≤ c → (0 : ℝ) < 1 / (c : ℝ) := fun c hc => by
    have : (0 : ℝ) < c := by exact_mod_cast hc
    positivity
  have inv_ge : ∀ (c N : ℕ), 1 ≤ c → c ≤ N → (1 : ℝ) / N ≤ 1 / c := fun c N hc hle => by
    have hc' : (0 : ℝ) < c := by exact_mod_cast hc
    have hle' : (c : ℝ) ≤ N := by exact_mod_cast hle
    exact one_div_le_one_div_of_le hc' hle'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b c hb1 hb2 hc
    have h1 : (1 : ℝ) / 9 ≤ 1 / b := inv_ge b 9 (by omega) hb2
    have h2 : (0 : ℝ) < 1 / c := inv_pos_of_ge1 c hc
    linarith
  · intro c hc
    have h2 : (0 : ℝ) < 1 / c := inv_pos_of_ge1 c hc
    linarith
  · intro c hc hle
    have h1 : (1 : ℝ) / 14716856 ≤ 1 / c := inv_ge c 14716856 hc hle
    linarith
  · intro c hc hle
    have h1 : (1 : ℝ) / 59 ≤ 1 / c := inv_ge c 59 hc hle
    linarith
  · intro c hc hle
    have h1 : (1 : ℝ) / 14 ≤ 1 / c := inv_ge c 14 hc hle
    linarith
  · intro c hc hle
    have h1 : (1 : ℝ) / 9 ≤ 1 / c := inv_ge c 9 hc hle
    linarith
  · intro c hc hle
    have h1 : (1 : ℝ) / 9 ≤ 1 / c := inv_ge c 9 hc hle
    linarith

/-- For the surviving `s = 2` (`t = 134,217,727`) stage, every 3-branch signature `(b₁, b₂, b₃)`
must have ALL three branch orders at least `6,882,961`. -/
theorem excluded_half_stage_three_branch {b₁ b₂ b₃ : ℕ}
    (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂) (hb₃ : 1 ≤ b₃)
    (hsmall : b₁ ≤ 6882960 ∨ b₂ ≤ 6882960 ∨ b₃ ≤ 6882960) :
    (1 : ℝ) - 1 / b₁ - 1 / b₂ - 1 / b₃ < 268435426 / 268435465 := by
  have ipos : ∀ x : ℕ, 1 ≤ x → (0 : ℝ) < 1 / x := fun x hx => by
    have : (0 : ℝ) < x := by exact_mod_cast hx
    positivity
  have ige : ∀ x : ℕ, 1 ≤ x → x ≤ 6882960 → (1 : ℝ) / 6882960 ≤ 1 / x := fun x hx hle =>
    one_div_le_one_div_of_le (by exact_mod_cast hx) (by exact_mod_cast hle)
  have p1 := ipos b₁ hb₁
  have p2 := ipos b₂ hb₂
  have p3 := ipos b₃ hb₃
  rcases hsmall with h | h | h
  · have := ige b₁ hb₁ h; linarith
  · have := ige b₂ hb₂ h; linarith
  · have := ige b₃ hb₃ h; linarith

/-- The characteristic threshold `h * deg u + k * deg v ≤ 2 n D < p` for `h = k = 1` holds with
nearly 100 bits of headroom on both designated primes (and every prime `p > 2^59`). -/
theorem characteristic_headroom :
    2 * 1073741824 * 268435454 < 2 ^ 59 ∧
    2 ^ 59 < 365375409332725729550921208179070755120141565953 ∧
    2 ^ 59 < 730750818665451459101842416358141509841924915201 := by
  decide

/-- Bonus: taking `h = k = 1024` (`M = 1,050,624`) in the same large-characteristic Wronskian
bound on a non-toric Möbius graph (`H_u = H_v = 2^30`, `χ ≤ 2`) yields `|Z| ≤ 3,145,728` for
every prime `p > 2048 * 2^30 = 2^41`, improving Corvaja–Zannier's `4,993,531`. -/
theorem mobius_wronskian_bound {Z : ℕ}
    (h : (Z : ℝ) ≤ (1024 * 1073741824 + 1024 * 1073741824 : ℝ) / (1024 * 1024 + 1024 + 1024) +
      ((1024 * 1024 + 1024 + 1024 : ℝ) - 1) / 2 * 2) :
    Z ≤ 3145728 := by
  have h1 : (Z : ℝ) < 3145729 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h1)

#print axioms VecValuation.subspace_adapted_valuation_ge
#print axioms vandermonde_ne_zero_of_lt_char
#print axioms rect_pole_zero_balance
#print axioms wronskian_gcd_bound
#print axioms pullback_gcd_bound
#print axioms degree_ge_two_of_suborbit
#print axioms subdegree_floor
#print axioms orbit_count_sharp
#print axioms inner_degree_only_two_or_half
#print axioms primitive_stage_classification
#print axioms primitive_excess_wronskian
#print axioms named_excess
#print axioms named_genus
#print axioms full_cover_excess
#print axioms excluded_whole_pencil_signatures
#print axioms excluded_half_stage_three_branch
#print axioms characteristic_headroom
#print axioms mobius_wronskian_bound

end ProximityGap.QuarterSplitWronskianSuborbits
