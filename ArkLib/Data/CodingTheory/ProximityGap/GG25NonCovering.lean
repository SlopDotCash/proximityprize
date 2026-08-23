/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodability

/-!
# Curve decodability gives a non-covering condition (issue #334, K5, brick 3)

[Jo26] (ePrint 2026/891) **Lemma 5.4**: a nonzero `F_q`-additive code that is
`(ℓ, δ, a, b)`-curve-decodable with `a ≤ q` and `b > ℓ + 1` cannot `δ`-cover the ambient
space — for every word `y` some codeword is farther than `δ` from it.

Proof (the paper's, formalized): if every codeword were `δ`-close to `y`, the instance
`u₀ = y, u₁ = ⋯ = u_ℓ = 0, f(α) = α^{ℓ+1} • v` (any fixed `0 ≠ v ∈ C`) has **full** close set
(`curve(α) = y` and `f(α) ∈ C` is `δ`-close to `y` by assumption), so decodability produces a
curve `∑ⱼ αʲ • cⱼ` agreeing with `α^{ℓ+1} • v` at `b > ℓ + 1` points. Pushing through a dual
functional that separates `v` from `0` (any nonzero coordinate functional of a basis of the
finite-dimensional `A`), this yields a *nonzero* `F`-polynomial of degree exactly `ℓ + 1` with
more than `ℓ + 1` roots — contradiction.

The brick's reusable core is `eq_zero_of_curve_agree_many`: a module-valued curve identity
holding at more than `ℓ + 1` field points forces the top coefficient to vanish — the
vector-coefficient root-counting step, via dual separation + `Polynomial.card_roots'`.
-/

open Finset Polynomial
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Dual separation**: a nonzero vector of a module over a field admits a linear functional
not vanishing on it. Thin wrapper over Mathlib's `Module.Projective.exists_dual_ne_zero`
(vector spaces are free, hence projective) — kept for the `A →ₗ[F] F` spelling the
root-counting core consumes. -/
theorem exists_dual_ne_zero {x : A} (hx : x ≠ 0) :
    ∃ φ : A →ₗ[F] F, φ x ≠ 0 :=
  Module.Projective.exists_dual_ne_zero F hx

/-- **The vector-coefficient root-counting core**: if `α^{ℓ+1} • v = ∑ⱼ αʲ • c j` holds at
more than `ℓ + 1` distinct field points, then `v = 0`. (Dual separation reduces to a scalar
polynomial of degree ≤ `ℓ + 1` whose top coefficient is `φ v`; too many roots kill it.) -/
theorem eq_zero_of_curve_agree_many {ℓ : ℕ} {v : A} {c : Fin (ℓ + 1) → A}
    {S : Finset F} (hS : ℓ + 1 < S.card)
    (hagree : ∀ α ∈ S, (α : F) ^ (ℓ + 1) • v = ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • c j) :
    v = 0 := by
  classical
  by_contra hv
  obtain ⟨φ, hφ⟩ := exists_dual_ne_zero (F := F) hv
  -- The scalar polynomial `X^{ℓ+1}·φ(v) − ∑ⱼ Xʲ·φ(c j)`.
  set P : Polynomial F :=
    Polynomial.C (φ v) * Polynomial.X ^ (ℓ + 1)
      - ∑ j : Fin (ℓ + 1), Polynomial.C (φ (c j)) * Polynomial.X ^ (j : ℕ) with hP
  have hPdeg : P.natDegree ≤ ℓ + 1 := by
    rw [hP]
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)
    · refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
      rw [Finset.fold_max_le]
      refine ⟨by omega, fun j _ => ?_⟩
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      simp only [Polynomial.natDegree_X_pow]
      omega
  have hPne : P ≠ 0 := by
    intro h0
    have hcoeff : P.coeff (ℓ + 1) = φ v := by
      rw [hP]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl, mul_one, Polynomial.finset_sum_coeff]
      have hz : ∀ x : Fin (ℓ + 1), (if ℓ + 1 = (x : ℕ) then (1 : F) else 0) = 0 :=
        fun x => if_neg (by omega)
      simp [hz]
    rw [h0] at hcoeff
    simp at hcoeff
    exact hφ hcoeff.symm
  -- Every point of `S` is a root.
  have hroots : ∀ α ∈ S, P.IsRoot α := by
    intro α hα
    have h := congrArg φ (hagree α hα)
    rw [map_smul, map_sum] at h
    simp only [map_smul] at h
    rw [hP]
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finset_sum]
    rw [sub_eq_zero]
    simpa [smul_eq_mul, mul_comm] using h
  -- Too many roots for the degree.
  have hsub : S ⊆ P.roots.toFinset := by
    intro α hα
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne]
    exact hroots α hα
  have hcard : S.card ≤ P.natDegree :=
    calc S.card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
  omega

/-- **[Jo26] Lemma 5.4 (curve decodability gives a non-covering condition).** A nonzero
`(ℓ, δ, a, b)`-curve-decodable `F`-additive code (a submodule — additivity is what supplies
`α^{ℓ+1} • v ∈ C`) with `a ≤ q` and `b > ℓ + 1` cannot `δ`-cover the space: for every `y`
some codeword is farther than `δ`. -/
theorem exists_far_codeword_of_curveDecodable {C : Submodule F (ι → A)} {ℓ : ℕ} {δ : ℝ≥0}
    {a b : ℕ}
    (h : CurveDecodable (F := F) (C : Set (ι → A)) ℓ δ a b)
    (ha : a ≤ Fintype.card F) (hb : ℓ + 1 < b)
    {v : ι → A} (hvC : v ∈ C) (hv : v ≠ 0)
    (y : ι → A) :
    ∃ c ∈ C, ¬ ((δᵣ(y, c) : ℝ≥0) ≤ δ) := by
  classical
  by_contra hcon
  push Not at hcon
  -- The instance: u₀ = y, the rest 0; f(α) = α^{ℓ+1} • v.
  set u : Fin (ℓ + 1) → ι → A := fun j => if j = 0 then y else 0 with hu
  set f : F → ι → A := fun α => (α ^ (ℓ + 1)) • v with hf
  have hfC : ∀ α, f α ∈ (C : Set (ι → A)) := fun α => C.smul_mem _ hvC
  -- The curve collapses to y: Σⱼ αʲ • u j = α⁰ • y = y.
  have hcurve : ∀ (α : F) (i : ι), (∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i) = y i := by
    intro α i
    rw [Finset.sum_eq_single (0 : Fin (ℓ + 1))]
    · simp [hu]
    · intro j _ hj
      simp [hu, hj]
    · simp
  -- The close set is everything: every f α is a codeword, hence δ-close to y by hcon.
  have hclose : (curveCloseSet δ u f).card = Fintype.card F := by
    rw [show curveCloseSet δ u f = Finset.univ from ?_, Finset.card_univ]
    rw [Finset.eq_univ_iff_forall]
    intro α
    simp only [curveCloseSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hpt : (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i) = y := by
      funext i
      exact hcurve α i
    rw [hpt]
    exact hcon (f α) (hfC α)
  -- Decodability fires at full close set.
  obtain ⟨cs, _hcs, hcount⟩ := h u f hfC (by rw [hclose]; exact ha)
  -- The explained set has more than ℓ+1 points; pick a nonzero coordinate of v.
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv
  have hi₀' : v i₀ ≠ 0 := by simpa using hi₀
  set S := (curveCloseSet δ u f).filter
    (fun α => f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j i) with hS
  have hScard : ℓ + 1 < S.card := lt_of_lt_of_le hb hcount
  -- The agreement identity at coordinate i₀, on S.
  have hagree : ∀ α ∈ S, (α : F) ^ (ℓ + 1) • (v i₀)
      = ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • (cs j i₀) := by
    intro α hα
    rw [hS, Finset.mem_filter] at hα
    have := congrFun hα.2 i₀
    simpa [hf] using this
  exact hi₀' (eq_zero_of_curve_agree_many hScard hagree)

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.exists_dual_ne_zero
#print axioms ProximityGap.eq_zero_of_curve_agree_many
#print axioms ProximityGap.exists_far_codeword_of_curveDecodable
