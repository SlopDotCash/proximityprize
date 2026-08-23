/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/-!
# Guruswami–Sudan multiplicity interpolation: EXISTENCE via dimension count

The interpolation step of the Guruswami–Sudan list decoder asks for a *nonzero*
bivariate polynomial `Q(X, Y)` of bounded `(1, k)`-weighted degree (`< D`) that
vanishes to order `m` at every interpolation point `(xᵢ, yᵢ)`.

This file proves that such a `Q` **exists** whenever the number of available
monomials exceeds the number of vanishing constraints, i.e.

  `n · (m · (m + 1) / 2)  <  #{ (a, b) : a + k·b < D }`.

The proof is the standard *underdetermined linear system* argument, identical in
spirit to the in-tree `BCKHS25 §2` Berlekamp–Welch dimension count
(`ArkLib/.../BCKHS25/Interpolation.lean`):

* the order-`m` vanishing conditions at the `n` points form a linear map
  `Φ : (coefficient space)  →ₗ  (constraint space)`,
* `finrank (constraint space) = n · m(m+1)/2  <  #monomials = finrank (coefficient space)`,
* hence `ker Φ ≠ ⊥`, giving a nonzero coefficient vector — equivalently a nonzero
  `Q` — satisfying all the constraints.

## Self-contained definitions

`vanishesToOrder` is defined directly as the genuine bivariate
Hasse-derivative-evaluation condition: `Q` vanishes to order `m` at `(x₀, y₀)`
iff every order-`(a, b)` Hasse coefficient (`a + b < m`)

  `∑_{(s,t)} C(s,a) · C(t,b) · c(s,t) · x₀^{s-a} · y₀^{t-b}`

vanishes. The `(a, b) = (0, 0)` instance is ordinary evaluation
(`vanishesToOrder_imp_eval` / `hasseCoeff_zero_zero`), matching
`Polynomial.hasseDeriv` at order `0`; this is recorded as a sanity lemma.

All statements are universe-polymorphic over an arbitrary field `F` and use only
Mathlib (`Matrix.mulVecLin`, `Module.finrank_pi`,
`LinearMap.ker_ne_bot_of_finrank_lt`, `Finset.antidiagonal`).
-/

namespace GSMultInterp

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Index sets: monomials and multiplicity constraints -/

/-- The monomial index set of the `(1, k)`-weighted-degree-`< D` space:
all `(a, b) ∈ ℕ × ℕ` with `a + k·b < D`. This is the *count of monomials*
appearing on the right-hand side of the interpolation feasibility bound; its
cardinality is `(monoIdx k D).card`. -/
def monoIdx (k D : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range D ×ˢ Finset.range D).filter (fun ab => ab.1 + k * ab.2 < D)

/-- The multiplicity-`m` constraint index set at a single point: all `(a, b)`
with `a + b < m`. Realized as the (disjoint) union of the antidiagonals
`a + b = s` for `s < m`. -/
def multIdx (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range m).biUnion (fun s => Finset.antidiagonal s)

@[simp] lemma mem_multIdx {m : ℕ} {ab : ℕ × ℕ} : ab ∈ multIdx m ↔ ab.1 + ab.2 < m := by
  classical
  simp only [multIdx, Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal]
  constructor
  · rintro ⟨s, hs, hab⟩; omega
  · intro h; exact ⟨ab.1 + ab.2, h, rfl⟩

lemma mem_monoIdx {k D : ℕ} {ab : ℕ × ℕ} :
    ab ∈ monoIdx k D ↔ ab.1 < D ∧ ab.2 < D ∧ ab.1 + k * ab.2 < D := by
  classical
  simp only [monoIdx, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  tauto

/-- For positive weight `k ≥ 1`, the box bounds are automatic: membership reduces
to the genuine weighted-degree condition `a + k·b < D` (and then `b ≤ D / k`). -/
lemma mem_monoIdx_of_pos {k D : ℕ} (hk : 0 < k) {ab : ℕ × ℕ} :
    ab ∈ monoIdx k D ↔ ab.1 + k * ab.2 < D := by
  rw [mem_monoIdx]
  constructor
  · rintro ⟨_, _, h⟩; exact h
  · intro h
    have hb : ab.2 < D := lt_of_le_of_lt (Nat.le_mul_of_pos_left ab.2 hk) (by omega)
    exact ⟨by omega, hb, h⟩

/-- **The number of multiplicity-`m` constraints per point is `m·(m+1)/2`.** -/
theorem card_multIdx (m : ℕ) : (multIdx m).card = m * (m + 1) / 2 := by
  classical
  -- disjoint union of antidiagonals, each of card `s + 1`
  have hdisj : (↑(Finset.range m) : Set ℕ).PairwiseDisjoint
      (fun s => Finset.antidiagonal s) := by
    intro s _ t _ hst
    apply Finset.disjoint_left.mpr
    intro ab hs ht
    rw [Finset.mem_antidiagonal] at hs ht
    exact hst (by omega)
  rw [multIdx, Finset.card_biUnion hdisj]
  simp only [Finset.Nat.card_antidiagonal]
  -- ∑_{s<m} (s+1) = m·(m+1)/2 directly: it is ∑_{s<m+1} s
  have hshift : ∑ s ∈ Finset.range m, (s + 1) = ∑ s ∈ Finset.range (m + 1), s := by
    rw [Finset.sum_range_succ']
    simp
  rw [hshift, Finset.sum_range_id]
  -- (m+1)·((m+1)-1)/2 = m·(m+1)/2
  rw [Nat.add_sub_cancel, Nat.mul_comm]

/-! ## The coefficient and constraint spaces -/

/-- Coefficient space: one field entry per monomial of weighted degree `< D`. -/
abbrev CoeffSpace (k D : ℕ) := {ab : ℕ × ℕ // ab ∈ monoIdx k D} → F

/-- Constraint space: one field entry per (point, low-order-Hasse-index) pair. -/
abbrev ConstrSpace (n m : ℕ) := (Fin n × {ab : ℕ × ℕ // ab ∈ multIdx m}) → F

/-! ## The vanishing condition (self-contained bivariate Hasse formulation) -/

/-- The order-`(a, b)` *Hasse coefficient* of the bivariate polynomial
`Q = ∑_{(s,t)∈monoIdx} c(s,t)·X^s·Y^t`, evaluated at `(x₀, y₀)`:

  `∑_{(s,t)} C(s,a)·C(t,b)·c(s,t)·x₀^{s-a}·y₀^{t-b}`.

This is exactly `(D^{(a,b)} Q)(x₀, y₀)`, the bivariate Hasse derivative
evaluation. It is `F`-linear in the coefficient vector `c`. -/
def hasseCoeff (k D : ℕ) (c : CoeffSpace (F := F) k D) (a b : ℕ) (x₀ y₀ : F) : F :=
  ∑ st : {ab : ℕ × ℕ // ab ∈ monoIdx k D},
    (Nat.choose st.1.1 a : F) * (Nat.choose st.1.2 b : F) * c st
      * x₀ ^ (st.1.1 - a) * y₀ ^ (st.1.2 - b)

omit [DecidableEq F] in
/-- **Sanity / consistency check.** The order-`(0,0)` Hasse coefficient is plain
evaluation `∑ c(s,t)·x₀^s·y₀^t`, matching `Polynomial.hasseDeriv` at order `0`.
This confirms `vanishesToOrder … (m ≥ 1)` includes the pointwise root condition
`Q(x₀, y₀) = 0`. -/
@[simp] lemma hasseCoeff_zero_zero (k D : ℕ) (c : CoeffSpace (F := F) k D) (x₀ y₀ : F) :
    hasseCoeff k D c 0 0 x₀ y₀
      = ∑ st : {ab : ℕ × ℕ // ab ∈ monoIdx k D}, c st * x₀ ^ st.1.1 * y₀ ^ st.1.2 := by
  simp only [hasseCoeff, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]

/-- `Q` (given by coefficient vector `c`) **vanishes to order `m`** at `(x₀, y₀)`:
every Hasse coefficient of order `a + b < m` vanishes. -/
def vanishesToOrder (k D m : ℕ) (c : CoeffSpace (F := F) k D) (x₀ y₀ : F) : Prop :=
  ∀ a b : ℕ, a + b < m → hasseCoeff k D c a b x₀ y₀ = 0

omit [DecidableEq F] in
/-- The order-`m` vanishing condition includes the ordinary root condition when
`m ≥ 1`. -/
lemma vanishesToOrder_imp_eval {k D m : ℕ} {c : CoeffSpace (F := F) k D} {x₀ y₀ : F}
    (hm : 0 < m) (hv : vanishesToOrder k D m c x₀ y₀) :
    (∑ st : {ab : ℕ × ℕ // ab ∈ monoIdx k D}, c st * x₀ ^ st.1.1 * y₀ ^ st.1.2) = 0 := by
  have := hv 0 0 (by omega)
  rwa [hasseCoeff_zero_zero] at this

/-! ## The constraint matrix and its kernel -/

/-- The interpolation constraint matrix. The row indexed by
`(i, ⟨(a,b), _⟩)` (point `i`, Hasse order `(a, b)` with `a + b < m`) and the
column indexed by the monomial `⟨(s,t), _⟩` is the coefficient

  `C(s,a)·C(t,b)·xᵢ^{s-a}·yᵢ^{t-b}`,

so that `(M · c)` at row `(i, (a,b))` is exactly `hasseCoeff … c a b xᵢ yᵢ`. -/
noncomputable def constrMatrix (k D m n : ℕ) (xs ys : Fin n → F) :
    Matrix (Fin n × {ab : ℕ × ℕ // ab ∈ multIdx m})
           {ab : ℕ × ℕ // ab ∈ monoIdx k D} F :=
  fun row st =>
    (Nat.choose st.1.1 row.2.1.1 : F) * (Nat.choose st.1.2 row.2.1.2 : F)
      * xs row.1 ^ (st.1.1 - row.2.1.1) * ys row.1 ^ (st.1.2 - row.2.1.2)

omit [DecidableEq F] in
/-- The matrix row applied to a coefficient vector reproduces `hasseCoeff`. -/
lemma constrMatrix_mulVec (k D m n : ℕ) (xs ys : Fin n → F) (c : CoeffSpace (F := F) k D)
    (i : Fin n) (ab : {ab : ℕ × ℕ // ab ∈ multIdx m}) :
    Matrix.mulVec (constrMatrix k D m n xs ys) c (i, ab)
      = hasseCoeff k D c ab.1.1 ab.1.2 (xs i) (ys i) := by
  simp only [Matrix.mulVec, dotProduct, constrMatrix, hasseCoeff]
  apply Finset.sum_congr rfl
  intro st _
  ring

omit [DecidableEq F] in
/-- A coefficient vector lies in the kernel iff `Q` vanishes to order `m` at every
interpolation point. -/
lemma mulVec_eq_zero_iff (k D m n : ℕ) (xs ys : Fin n → F) (c : CoeffSpace (F := F) k D) :
    Matrix.mulVec (constrMatrix k D m n xs ys) c = 0
      ↔ ∀ i : Fin n, vanishesToOrder k D m c (xs i) (ys i) := by
  classical
  constructor
  · intro hker i a b hab
    have h := congrFun hker (i, ⟨(a, b), mem_multIdx.mpr (by simpa using hab)⟩)
    rw [constrMatrix_mulVec] at h
    simpa using h
  · intro hv
    funext row
    obtain ⟨i, ab⟩ := row
    rw [constrMatrix_mulVec]
    exact hv i ab.1.1 ab.1.2 (mem_multIdx.mp ab.2)

/-! ## Existence via the dimension count -/

/-- **Abstract underdetermined-system existence** (mirrors
`BCKHS25.exists_ne_zero_map_eq_zero`): a linear map between finite-dimensional
spaces with strictly larger domain has a nonzero kernel vector. -/
theorem exists_ne_zero_map_eq_zero {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (Φ : V →ₗ[K] W) (h : Module.finrank K W < Module.finrank K V) :
    ∃ v : V, v ≠ 0 ∧ Φ v = 0 := by
  have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) h
  rcases Submodule.ne_bot_iff _ |>.mp hk with ⟨v, hvmem, hv0⟩
  exact ⟨v, hv0, hvmem⟩

omit [DecidableEq F] in
/-- **Guruswami–Sudan multiplicity interpolation — EXISTENCE.**

Given `n` interpolation points `(xs i, ys i)`, target multiplicity `m`, weight
`k` and degree bound `D`, if the number of vanishing constraints is strictly
below the number of available monomials,

  `n · (m · (m + 1) / 2)  <  (monoIdx k D).card`,

then there exists a **nonzero** coefficient vector `c` (equivalently a nonzero
bivariate `Q` of `(1, k)`-weighted degree `< D`) that vanishes to order `m` at
every interpolation point.

The proof: the order-`m` vanishing conditions form a linear map into a space of
dimension `n · m(m+1)/2`; with strictly more monomials than constraints, the
kernel is nontrivial (`exists_ne_zero_map_eq_zero`). -/
theorem exists_ne_zero_vanishesToOrder (k D m n : ℕ) (xs ys : Fin n → F)
    (hcount : n * (m * (m + 1) / 2) < (monoIdx k D).card) :
    ∃ c : CoeffSpace (F := F) k D, c ≠ 0 ∧
      ∀ i : Fin n, vanishesToOrder k D m c (xs i) (ys i) := by
  classical
  -- dimension comparison: #constraints = n · m(m+1)/2 < #monomials = dim coeff space
  have hfr : Module.finrank F (ConstrSpace (F := F) n m)
      < Module.finrank F (CoeffSpace (F := F) k D) := by
    simp only [ConstrSpace, CoeffSpace, Module.finrank_pi, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_coe, card_multIdx]
    exact hcount
  obtain ⟨c, hc0, hker⟩ :=
    exists_ne_zero_map_eq_zero (Matrix.mulVecLin (constrMatrix k D m n xs ys)) hfr
  refine ⟨c, hc0, ?_⟩
  rw [← mulVec_eq_zero_iff]
  simpa [Matrix.mulVecLin_apply] using hker

end GSMultInterp
