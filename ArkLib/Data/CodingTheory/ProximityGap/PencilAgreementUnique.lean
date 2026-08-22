/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots

/-!
# The agreement set determines the monomial pencil (#407, Action–Orbit machinery)

A brick for the orbit-count route to δ*. The far-line incidence `I(δ)` counts monomial-pencil
parameters `α` for which `x^a + α x^b` is δ-close to `RS[k]`; each such `α` has a maximal
*agreement set* `A = {x ∈ μ_n : x^a + α x^b = g(x)}` for a best degree-`< k` codeword `g`. The
Action–Orbit bad set is `⟨ω^{b−a}⟩`-orbit-closed, and the orbit count `N` is the number of distinct
agreement sets mod rotation.

For that count to be well-defined as a count of *pencils*, a sufficiently large agreement set must
determine `(α, g)` uniquely. This file proves exactly that — **pencil rigidity**:

> if `x^a + α x^b − g` and `x^a + α' x^b − g'` (with `deg g, deg g' < k ≤ b`) both vanish on a set
> `A` with `|A| > b`, then `α = α'` and `g = g'`.

The proof is elementary: the difference `(α − α')·X^b − (g − g')` has degree `≤ b < |A|` yet vanishes
on `|A|` distinct points, hence is the zero polynomial; reading off the `X^b` coefficient gives
`α = α'`, and then `g = g'`. This is the injectivity `agreement set ↦ pencil` underlying the
orbit-count crossing law (`docs/kb/deltastar-orbit-count-reformulation-2026-06-14.md`), validated
numerically (`probe_orbit_count_prize_regime`: n=8 had 40 bad `α` ↔ 40 distinct agreement sets).
-/

open Polynomial

namespace ArkLib.ProximityGap.PencilRigidity

variable {F : Type*} [Field F] [DecidableEq F]

/-- A polynomial with `natDegree < A.card` vanishing on every point of a finite set `A` is `0`. -/
theorem eq_zero_of_eval_zero_on_card_gt
    {p : F[X]} {A : Finset F} (hdeg : p.natDegree < A.card)
    (hroot : ∀ x ∈ A, p.eval x = 0) : p = 0 := by
  by_contra hp
  have hsub : A ⊆ p.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots']
    exact ⟨hp, hroot x hx⟩
  have h1 : A.card ≤ p.roots.toFinset.card := Finset.card_le_card hsub
  have h2 : p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
  have h3 : Multiset.card p.roots ≤ p.natDegree := card_roots' p
  omega

/-- **Pencil rigidity.** If two monomial pencils `x^a + α x^b` and `x^a + α' x^b` agree with
degree-`< k` codewords `g`, `g'` on a common set `A` of size `> b` (with `k ≤ b`), then the pencils
coincide: `α = α'` and `g = g'`. Hence a large agreement set determines the pencil parameter. -/
theorem pencil_unique_of_large_agreement
    {a b k : ℕ} (hkb : k ≤ b)
    {α α' : F} {g g' : F[X]} (hg : g.natDegree < k) (hg' : g'.natDegree < k)
    {A : Finset F} (hA : b < A.card)
    (hvanish : ∀ x ∈ A, x ^ a + α * x ^ b - g.eval x = 0)
    (hvanish' : ∀ x ∈ A, x ^ a + α' * x ^ b - g'.eval x = 0) :
    α = α' ∧ g = g' := by
  set D : F[X] := C (α - α') * X ^ b - (g - g') with hD
  -- `g - g'` has degree `< b`.
  have hgdeg : (g - g').natDegree < b :=
    lt_of_le_of_lt (natDegree_sub_le g g')
      (Nat.max_lt.mpr ⟨lt_of_lt_of_le hg hkb, lt_of_lt_of_le hg' hkb⟩)
  -- `D` vanishes on `A`.
  have hDeval : ∀ x ∈ A, D.eval x = 0 := by
    intro x hx
    have h1 := hvanish x hx
    have h2 := hvanish' x hx
    simp only [hD, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    have hrw : (α - α') * x ^ b - (eval x g - eval x g')
        = (x ^ a + α * x ^ b - eval x g) - (x ^ a + α' * x ^ b - eval x g') := by ring
    rw [hrw, h1, h2, sub_zero]
  -- `D` has degree `≤ b < |A|`, hence is `0`.
  have hdegD : D.natDegree ≤ b := by
    rw [hD]
    refine le_trans (natDegree_sub_le _ _) (Nat.max_le.mpr ⟨?_, le_of_lt hgdeg⟩)
    exact le_trans (natDegree_C_mul_le _ _) (le_of_eq (natDegree_X_pow b))
  have hD0 : D = 0 := eq_zero_of_eval_zero_on_card_gt (lt_of_le_of_lt hdegD hA) hDeval
  -- Read off the `X^b` coefficient: `α - α' = 0`.
  have hα : α = α' := by
    have h := congrArg (fun p => Polynomial.coeff p b) hD0
    rw [hD] at h
    simp only [coeff_sub, coeff_C_mul, coeff_X_pow,
      coeff_eq_zero_of_natDegree_lt hgdeg, coeff_zero, if_true, mul_one, sub_zero] at h
    exact sub_eq_zero.mp h
  refine ⟨hα, ?_⟩
  -- With `α = α'`, `D = -(g - g') = 0`, so `g = g'`.
  have hgg : g' - g = 0 := by
    have h := hD0
    rw [hD, sub_eq_zero.mpr hα] at h
    simpa using h
  exact (sub_eq_zero.mp hgg).symm

end ArkLib.ProximityGap.PencilRigidity
