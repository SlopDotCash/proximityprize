/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BoundarySliceUnconditional
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The generic-far separation engine (#371): the ratio functionals are distinct

Towards the generic-far pin (`#badSet = C(n,k+1)` for some stack): the modular
Wronskian census says the bad scalars of the stack `(Q₀, x^k)` at the boundary
radius are the values `−L_S(Q₀)` over `(k+1)`-subsets `S`, where

  `L_S(W) := (W %ₘ P_S).coeff k`,  `P_S := ∏_{i∈S}(X − xᵢ)`.

This file proves the linear-algebraic core: the functionals `L_S` are
**pairwise distinct** on polynomials of degree `< 2k+2`.

* `coeffFn_lagrange` — the divided-difference form
  `L_S(W) = ∑_{i∈S} W(xᵢ)/∏_{j≠i}(xᵢ−xⱼ)` (via `Lagrange.coeff_eq_sum`).
* `coeffFn_vanishing` — if `L_S(X^j·G) = 0` for all `j ≤ k`, then `G` vanishes
  at every node of `S` (Vandermonde kernel argument).
* `coeffFn_separation` — for `S ≠ S'`, some witness `X^j·P_{S'}` (degree
  `≤ 2k+1`) separates: `L_S ≠ 0 = L_{S'}` on it.
* `coeffFn_X_pow_self` — `L_S(X^k) = 1`: the direction `x^k` normalizes the
  ratio to `−L_S(Q₀)`.

The companion file (`GenericFarPin`) runs the union bound over pairs to produce
a collision-free `Q₀` and the exact count `#badSet = C(n,k+1)`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The node polynomial of a subset of the domain. -/
noncomputable def nodePoly (dom : Fin n ↪ F) (s : Finset (Fin n)) : F[X] :=
  ∏ i ∈ s, (X - C (dom i))

/-- The modular Wronskian functional: the `X^k`-coefficient of the remainder
mod the node polynomial. -/
noncomputable def coeffFn (dom : Fin n ↪ F) (k : ℕ) (s : Finset (Fin n))
    (W : F[X]) : F :=
  (W %ₘ nodePoly dom s).coeff k

theorem nodePoly_monic (dom : Fin n ↪ F) (s : Finset (Fin n)) :
    (nodePoly dom s).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _

theorem natDegree_nodePoly (dom : Fin n ↪ F) (s : Finset (Fin n)) :
    (nodePoly dom s).natDegree = s.card := by
  rw [nodePoly, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
  simp

theorem eval_nodePoly_at_node (dom : Fin n ↪ F) {s : Finset (Fin n)}
    {i : Fin n} (hi : i ∈ s) : (nodePoly dom s).eval (dom i) = 0 := by
  rw [nodePoly, eval_prod]
  exact Finset.prod_eq_zero hi (by simp)

/-- The remainder agrees with the polynomial at the nodes. -/
theorem modByMonic_eval_at_node (dom : Fin n ↪ F) {s : Finset (Fin n)}
    {i : Fin n} (hi : i ∈ s) (W : F[X]) :
    (W %ₘ nodePoly dom s).eval (dom i) = W.eval (dom i) := by
  conv_rhs => rw [← modByMonic_add_div W (nodePoly dom s)]
  simp [eval_add, eval_mul, eval_nodePoly_at_node dom hi]

/-- **The divided-difference form** of the modular Wronskian functional. -/
theorem coeffFn_lagrange (dom : Fin n ↪ F) {k : ℕ} {s : Finset (Fin n)}
    (hcard : s.card = k + 1) (W : F[X]) :
    coeffFn dom k s W
      = ∑ i ∈ s, W.eval (dom i) / ∏ j ∈ s.erase i, (dom i - dom j) := by
  have hinjOn : Set.InjOn dom s := fun a _ b _ h => dom.injective h
  have hdeg : (W %ₘ nodePoly dom s).degree < (s.card : ℕ) := by
    have h1 := degree_modByMonic_lt W (nodePoly_monic dom s)
    rwa [degree_eq_natDegree (nodePoly_monic dom s).ne_zero,
      natDegree_nodePoly] at h1
  have h := Lagrange.coeff_eq_sum hinjOn (P := W %ₘ nodePoly dom s) hdeg
  rw [coeffFn]
  calc (W %ₘ nodePoly dom s).coeff k
      = (W %ₘ nodePoly dom s).coeff (s.card - 1) := by
        rw [hcard, Nat.add_sub_cancel]
    _ = ∑ i ∈ s, (W %ₘ nodePoly dom s).eval (dom i)
          / ∏ j ∈ s.erase i, (dom i - dom j) := h
    _ = ∑ i ∈ s, W.eval (dom i) / ∏ j ∈ s.erase i, (dom i - dom j) :=
        Finset.sum_congr rfl fun i hi => by
          rw [modByMonic_eval_at_node dom hi]

/-- The node products are nonzero. -/
theorem nodeProd_ne_zero (dom : Fin n ↪ F) {s : Finset (Fin n)} {i : Fin n} :
    ∏ j ∈ s.erase i, (dom i - dom j) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  exact sub_ne_zero.mpr fun h => hji (dom.injective h.symm)

open Classical in
/-- **The vanishing lemma**: if all the shifted functionals `L_S(X^j·G)`
(`j ≤ k`) vanish, then `G` vanishes at every node — the Vandermonde kernel
argument. -/
theorem coeffFn_vanishing (dom : Fin n ↪ F) {k : ℕ} {s : Finset (Fin n)}
    (hcard : s.card = k + 1) (G : F[X])
    (hall : ∀ j : Fin (k + 1), coeffFn dom k s (X ^ (j : ℕ) * G) = 0) :
    ∀ i ∈ s, G.eval (dom i) = 0 := by
  -- enumerate the nodes
  set σ : Fin (k + 1) → Fin n :=
    fun a => (s.equivFin.symm (Fin.cast hcard.symm a) : Fin n) with hσ
  have hσinj : Function.Injective σ := by
    intro a b hab
    have h1 : (s.equivFin.symm (Fin.cast hcard.symm a))
        = s.equivFin.symm (Fin.cast hcard.symm b) := Subtype.ext hab
    exact Fin.cast_injective _ (s.equivFin.symm.injective h1)
  have hσmem : ∀ a, σ a ∈ s := fun a =>
    (s.equivFin.symm (Fin.cast hcard.symm a)).2
  have himg : Finset.univ.image σ = s := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      exact hσmem a
    · rw [Finset.card_image_of_injective _ hσinj, Finset.card_univ,
        Fintype.card_fin, hcard]
  -- the kernel vector
  set w : Fin (k + 1) → F :=
    fun a => G.eval (dom (σ a)) / ∏ j ∈ s.erase (σ a), (dom (σ a) - dom j)
    with hw
  -- the Vandermonde-transpose kernel equation
  have hker : ∀ j : Fin (k + 1), ∑ a, (dom (σ a)) ^ (j : ℕ) * w a = 0 := by
    intro j
    have h := hall j
    rw [coeffFn_lagrange dom hcard] at h
    have hsum : ∑ i ∈ s, (X ^ (j : ℕ) * G).eval (dom i)
          / ∏ j' ∈ s.erase i, (dom i - dom j')
        = ∑ a, (dom (σ a)) ^ (j : ℕ) * w a := by
      calc ∑ i ∈ s, (X ^ (j : ℕ) * G).eval (dom i)
            / ∏ j' ∈ s.erase i, (dom i - dom j')
          = ∑ i ∈ s, (dom i) ^ (j : ℕ)
              * (G.eval (dom i) / ∏ j' ∈ s.erase i, (dom i - dom j')) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [eval_mul, eval_pow, eval_X]
            rw [mul_div_assoc]
        _ = ∑ i ∈ Finset.univ.image σ, (dom i) ^ (j : ℕ)
              * (G.eval (dom i) / ∏ j' ∈ s.erase i, (dom i - dom j')) :=
            (Finset.sum_congr himg fun x _ => rfl).symm
        _ = ∑ a, (dom (σ a)) ^ (j : ℕ)
              * (G.eval (dom (σ a))
                / ∏ j' ∈ s.erase (σ a), (dom (σ a) - dom j')) :=
            Finset.sum_image fun a _ b _ h' => hσinj h'
        _ = ∑ a, (dom (σ a)) ^ (j : ℕ) * w a :=
            Finset.sum_congr rfl fun a _ => by rw [hw]
    rw [hsum] at h
    exact h
  -- if the kernel vector is nonzero, the Vandermonde determinant vanishes
  by_cases hw0 : w = 0
  · intro i hi
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp (himg ▸ hi)
    have h := congrFun hw0 a
    rw [hw] at h
    simp only [Pi.zero_apply] at h
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h (nodeProd_ne_zero dom)
  · exfalso
    set M : Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
      (Matrix.vandermonde fun a => dom (σ a)).transpose with hM
    have hMker : M.mulVec w = 0 := by
      funext j
      show ∑ a, M j a * w a = 0
      calc ∑ a, M j a * w a
          = ∑ a, (dom (σ a)) ^ (j : ℕ) * w a :=
            Finset.sum_congr rfl fun a _ => by
              rw [hM]
              simp [Matrix.vandermonde, Matrix.transpose_apply]
        _ = 0 := hker j
    have hdet : M.det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw0, hMker⟩
    rw [hM, Matrix.det_transpose, Matrix.det_vandermonde] at hdet
    have : ∀ i : Fin (k + 1), ∀ j ∈ Finset.Ioi i,
        dom (σ j) - dom (σ i) ≠ 0 := by
      intro i j hj
      refine sub_ne_zero.mpr fun h => ?_
      have hij : i ≠ j := Fin.ne_of_lt (Finset.mem_Ioi.mp hj)
      exact hij (hσinj (dom.injective h)).symm
    exact (Finset.prod_ne_zero_iff.mpr fun i _ =>
      Finset.prod_ne_zero_iff.mpr fun j hj => this i j hj) hdet

/-- Multiples of the node polynomial are killed by their own functional. -/
theorem coeffFn_mul_nodePoly_self (dom : Fin n ↪ F) (k : ℕ)
    (s : Finset (Fin n)) (W : F[X]) :
    coeffFn dom k s (W * nodePoly dom s) = 0 := by
  rw [coeffFn,
    (modByMonic_eq_zero_iff_dvd (nodePoly_monic dom s)).mpr (dvd_mul_left _ _),
    coeff_zero]

open Classical in
/-- **THE SEPARATION**: distinct `(k+1)`-subsets are separated by a witness of
degree ≤ `2k+1` — some `X^j·P_{S'}` has nonzero `L_S` but zero `L_{S'}`. -/
theorem coeffFn_separation (dom : Fin n ↪ F) {k : ℕ}
    {s s' : Finset (Fin n)} (hcard : s.card = k + 1)
    (hcard' : s'.card = k + 1) (hne : s ≠ s') :
    ∃ j : Fin (k + 1),
      coeffFn dom k s (X ^ (j : ℕ) * nodePoly dom s') ≠ 0 ∧
      coeffFn dom k s' (X ^ (j : ℕ) * nodePoly dom s') = 0 := by
  by_contra hno
  push Not at hno
  -- all the s-functionals vanish on the witnesses
  have hall : ∀ j : Fin (k + 1),
      coeffFn dom k s (X ^ (j : ℕ) * nodePoly dom s') = 0 := by
    intro j
    by_contra hjne
    exact hno j hjne (coeffFn_mul_nodePoly_self dom k s' (X ^ (j : ℕ)))
  -- so the node polynomial of s' vanishes on all of s
  have hvan := coeffFn_vanishing dom hcard (nodePoly dom s') hall
  -- hence s ⊆ s', hence s = s'
  have hsub : s ⊆ s' := by
    intro i hi
    have h := hvan i hi
    rw [nodePoly, eval_prod] at h
    obtain ⟨i', hi', hz⟩ := Finset.prod_eq_zero_iff.mp h
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hz
    rw [dom.injective hz]
    exact hi'
  exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))

/-- The direction normalization: `L_S(X^k) = 1`. -/
theorem coeffFn_X_pow_self (dom : Fin n ↪ F) {k : ℕ} {s : Finset (Fin n)}
    (hcard : s.card = k + 1) :
    coeffFn dom k s (X ^ k) = 1 := by
  rw [coeffFn, (modByMonic_eq_self_iff (nodePoly_monic dom s)).mpr (by
    rw [degree_eq_natDegree (nodePoly_monic dom s).ne_zero,
      natDegree_nodePoly, hcard, degree_X_pow]
    exact_mod_cast Nat.lt_succ_self k)]
  simp

/-- Linearity of the functional in the polynomial argument. -/
theorem coeffFn_add (dom : Fin n ↪ F) (k : ℕ) (s : Finset (Fin n))
    (W W' : F[X]) :
    coeffFn dom k s (W + W') = coeffFn dom k s W + coeffFn dom k s W' := by
  rw [coeffFn, coeffFn, coeffFn, add_modByMonic, coeff_add]

theorem coeffFn_smul (dom : Fin n ↪ F) (k : ℕ) (s : Finset (Fin n)) (c : F)
    (W : F[X]) :
    coeffFn dom k s (C c * W) = c * coeffFn dom k s W := by
  rw [coeffFn, coeffFn, show C c * W = c • W from by rw [smul_eq_C_mul],
    smul_modByMonic, coeff_smul, smul_eq_mul]

/-- The functional commutes with finite sums. -/
theorem coeffFn_finset_sum (dom : Fin n ↪ F) (k : ℕ) (s : Finset (Fin n))
    {ι : Type*} [DecidableEq ι] (t : Finset ι) (f : ι → F[X]) :
    coeffFn dom k s (∑ j ∈ t, f j) = ∑ j ∈ t, coeffFn dom k s (f j) := by
  induction t using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, coeffFn, zero_modByMonic,
        coeff_zero]
  | insert a t hat ih =>
      rw [Finset.sum_insert hat, Finset.sum_insert hat, coeffFn_add, ih]

/-- The functional on a monomial expansion. -/
theorem coeffFn_sum_monomials (dom : Fin n ↪ F) (k : ℕ) (s : Finset (Fin n))
    {m : ℕ} (c : Fin m → F) :
    coeffFn dom k s (∑ j, C (c j) * X ^ (j : ℕ))
      = ∑ j, c j * coeffFn dom k s (X ^ (j : ℕ)) := by
  rw [coeffFn_finset_sum]
  exact Finset.sum_congr rfl fun j _ => coeffFn_smul dom k s (c j) _

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.coeffFn_lagrange
#print axioms ProximityGap.Ownership.coeffFn_vanishing
#print axioms ProximityGap.Ownership.coeffFn_separation
