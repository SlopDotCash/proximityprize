/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.GoodCoeffs
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Roots

/-!
# Bivariate Lagrange lift: coefficient-polynomial extraction ([BCIKS20] §6 mechanism)

This file formalizes the *interpolation half* of the strict-Johnson correlated-agreement
argument for parameterized curves. Given a family `P : F → F[X]` of decoded polynomials along
the degree-`k` curve word `w z = ∑ t, z^t • u t`, the key structural claim of [BCIKS20] §6 is
that the coefficients of `P z`, viewed as functions of the curve parameter `z`, are themselves
polynomials of degree `≤ k`.

The headline lemma `coeffPolys_of_largeCommonAgreement` proves exactly this *from a single
geometric hypothesis*: that at every good parameter `z`, the decoding `P z` and `k+1` sampled
decodings `P (s 0), …, P (s k)` share a common agreement set of `≥ deg` domain points. The
construction is Lagrange interpolation of `P (s i)` through the sample parameters `s i`, followed
by the observation that the interpolated bivariate object agrees with `P z` on the common
agreement set, hence (being degree `< deg` in `X`) equals it.

`RS_coeffPolys_of_commonAgreement` instantiates this at the Reed–Solomon good-coefficient curve
set `RS_goodCoeffsCurve`, reproducing the exact conclusion shape of
`Curves.StrictCoeffPolysResidual`.

## Status / relationship to the strict-Johnson residual

This discharges the *interpolation/algebra* content of the strict coefficient-polynomial
extraction. The genuinely deep remaining content of `StrictCoeffPolysResidual` is precisely the
hypothesis `hCommon`: that in the regime `δ < 1 - √ρ` with probability above `k · errorBound`,
the decoded family is forced onto a single global low-degree structure (so that the agreement
sets of different parameters overlap on `≥ deg` points). A naive union bound only yields a
common agreement of size `≥ (1 - (k+2)δ)·|ι|`, which is `≥ deg` only when `(k+2)δ ≤ 1 - ρ` —
disjoint from the list-decoding regime `δ > (1-ρ)/2`. Establishing the common agreement at the
Johnson radius is the deep BCIKS counting argument; this file isolates and discharges everything
*downstream* of it.

## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]
-/

namespace ProximityGap

set_option linter.unusedSectionVars false

open Polynomial Finset Code
open scoped NNReal BigOperators

variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Evaluation of a Lagrange interpolant is the basis-weighted sum of the node values. -/
lemma eval_interpolate [DecidableEq ι] (s : Finset ι) (v : ι → F) (c : ι → F) (z : F) :
    (Lagrange.interpolate s v c).eval z = ∑ i ∈ s, c i * (Lagrange.basis s v i).eval z := by
  rw [Lagrange.interpolate_apply, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C]

/-- **Bivariate Lagrange lift / coefficient-polynomial extraction** ([BCIKS20] §6 mechanism).

Words `u 0 … u k : ι → F`, the degree-`k` curve word `w z = ∑ t, z^t • u t`, a "good set"
`G ⊆ F` of curve parameters, a family `P : F → F[X]` of decoded polynomials (degree `< deg`),
and `k+1` distinct sample parameters `s 0 … s k ∈ G`. If, at every `z ∈ G`, `P z` and *all* the
sampled `P (s i)` simultaneously agree with their curve words on a common set `S` of `≥ deg`
domain points, then the coefficients of `P z` are, as functions of `z`, the evaluations of fixed
polynomials `B j` of degree `≤ k`.

This is the exact mechanism by which BCIKS lift agreement on lines/curves to a global low-degree
bivariate structure: the coefficient functions are themselves low-degree polynomials in the curve
parameter, recovered by Lagrange interpolation through any `k+1` sample parameters. -/
theorem coeffPolys_of_largeCommonAgreement
    (domain : ι ↪ F) {k deg : ℕ} [NeZero deg]
    (u : Fin (k + 1) → ι → F)
    (P : F → F[X])
    (G : Finset F)
    (s : Fin (k + 1) → F)
    (hs_inj : Function.Injective s)
    (hPdeg : ∀ z ∈ G, (P z).natDegree < deg)
    (hsG : ∀ i, s i ∈ G)
    (hCommon : ∀ z ∈ G, ∃ S : Finset ι, deg ≤ S.card ∧
      (∀ x ∈ S, (P z).eval (domain x) = ∑ t : Fin (k + 1), (z ^ (t : ℕ)) * u t x) ∧
      (∀ i : Fin (k + 1), ∀ x ∈ S, (P (s i)).eval (domain x)
          = ∑ t : Fin (k + 1), ((s i) ^ (t : ℕ)) * u t x)) :
    ∃ B : ℕ → F[X], (∀ j, (B j).natDegree < k + 1) ∧
      ∀ z ∈ G, ∀ j < deg, (P z).coeff j = (B j).eval z := by
  classical
  set B : ℕ → F[X] :=
    fun j => Lagrange.interpolate Finset.univ s (fun i => (P (s i)).coeff j) with hB
  have hsinj_on : Set.InjOn s (Finset.univ : Finset (Fin (k + 1))) := hs_inj.injOn
  have hcard_univ : (Finset.univ : Finset (Fin (k + 1))).card = k + 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hBdeg : ∀ j, (B j).natDegree < k + 1 := by
    intro j
    have hlt := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin (k + 1))))
      (v := s) (r := fun i => (P (s i)).coeff j) hsinj_on
    rw [hcard_univ] at hlt
    by_cases hz0 : B j = 0
    · rw [hz0, Polynomial.natDegree_zero]; omega
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz0).2 (by simpa [hB] using hlt)
  refine ⟨B, hBdeg, ?_⟩
  intro z hz j hj
  obtain ⟨S, hScard, hPz, hPsi⟩ := hCommon z hz
  set Qz : F[X] := ∑ j' ∈ Finset.range deg, Polynomial.monomial j' ((B j').eval z) with hQz
  set β : Fin (k + 1) → F := fun i => (Lagrange.basis Finset.univ s i).eval z with hβ
  have hQzcoeff : ∀ i, Qz.coeff i = if i < deg then (B i).eval z else 0 := by
    intro i
    rw [hQz, Polynomial.finset_sum_coeff]
    simp_rw [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range deg) i (fun j' => (B j').eval z)]
    simp [Finset.mem_range]
  have hQzdeg : Qz.natDegree < deg := by
    have hdpos : 0 < deg := Nat.pos_of_ne_zero (NeZero.ne deg)
    have hle : Qz.natDegree ≤ deg - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      have hmd : ¬ m < deg := by omega
      rw [hQzcoeff m]; simp [hmd]
    omega
  have hbridge : ∀ x : ι, Qz.eval (domain x)
      = (Lagrange.interpolate Finset.univ s (fun i => (P (s i)).eval (domain x))).eval z := by
    intro x
    have hLHS : Qz.eval (domain x) = ∑ i, (P (s i)).eval (domain x) * β i := by
      rw [hQz, Polynomial.eval_finset_sum]
      simp_rw [Polynomial.eval_monomial]
      have e1 : ∀ j' ∈ Finset.range deg,
          (B j').eval z * domain x ^ j'
            = ∑ i, (P (s i)).coeff j' * β i * domain x ^ j' := by
        intro j' _
        rw [show (B j').eval z = ∑ i, (P (s i)).coeff j' * β i from
          by rw [hB]; exact eval_interpolate Finset.univ s (fun i => (P (s i)).coeff j') z,
          Finset.sum_mul]
      rw [Finset.sum_congr rfl e1, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Polynomial.eval_eq_sum_range' (hPdeg (s i) (hsG i)), Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      ring
    rw [hLHS, eval_interpolate]
  have hagree : ∀ x ∈ S, (P z).eval (domain x) = Qz.eval (domain x) := by
    intro x hx
    rw [hbridge x]
    set gx : F[X] := ∑ t : Fin (k + 1), Polynomial.monomial (t : ℕ) (u t x) with hgx
    have hgx_eval : ∀ w : F, gx.eval w = ∑ t : Fin (k + 1), w ^ (t : ℕ) * u t x := by
      intro w
      rw [hgx, Polynomial.eval_finset_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [Polynomial.eval_monomial]; ring
    have hgx_deg : gx.degree < ((Finset.univ : Finset (Fin (k + 1))).card : WithBot ℕ) := by
      rw [hcard_univ]
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro t _
      exact lt_of_le_of_lt (Polynomial.degree_monomial_le _ _) (by exact_mod_cast t.2)
    have hinterp_eq :
        Lagrange.interpolate Finset.univ s (fun i => (P (s i)).eval (domain x)) = gx := by
      have hvals : ∀ i ∈ (Finset.univ : Finset (Fin (k + 1))),
          (P (s i)).eval (domain x) = gx.eval (s i) := by
        intro i _
        rw [hPsi i x hx, hgx_eval]
      rw [Lagrange.interpolate_eq_of_values_eq_on (s := Finset.univ) (v := s)
          (r := fun i => (P (s i)).eval (domain x)) (r' := fun i => gx.eval (s i)) hvals]
      exact (Lagrange.eq_interpolate hsinj_on hgx_deg).symm
    rw [hinterp_eq, hgx_eval, hPz x hx]
  have hPeq : P z = Qz := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq' (P z) Qz (S.image domain) ?_ ?_
    · intro y hy
      obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
      exact hagree x hxS
    · rw [Finset.card_image_of_injective _ domain.injective]
      have hmx : max (P z).natDegree Qz.natDegree < deg := max_lt (hPdeg z hz) hQzdeg
      omega
  rw [hPeq, hQzcoeff j]; simp [hj]

/-- **RS-curve coefficient extraction.** Instantiation of `coeffPolys_of_largeCommonAgreement`
at the Reed–Solomon good-coefficient curve set `RS_goodCoeffsCurve`: this is exactly the
conclusion shape of `Curves.StrictCoeffPolysResidual`, derived from the transparent geometric
hypothesis that the decoded family has a common `≥ deg`-size agreement set with the sampled
decodings at every good parameter. See the module docstring for the relationship to the deep
remaining content of the strict-Johnson residual. -/
theorem RS_coeffPolys_of_commonAgreement
    [DecidableEq ι] {domain : ι ↪ F} {k deg : ℕ} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin (k + 1)) ι)
    (P : F → F[X])
    (s : Fin (k + 1) → F)
    (hs_inj : Function.Injective s)
    (hPdeg : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).natDegree < deg)
    (hsG : ∀ i, s i ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (hCommon : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ∃ S : Finset ι, deg ≤ S.card ∧
        (∀ x ∈ S, (P z).eval (domain x) = ∑ t : Fin (k + 1), (z ^ (t : ℕ)) * u t x) ∧
        (∀ i : Fin (k + 1), ∀ x ∈ S, (P (s i)).eval (domain x)
            = ∑ t : Fin (k + 1), ((s i) ^ (t : ℕ)) * u t x)) :
    ∃ B : ℕ → Polynomial F, (∀ j < deg, (B j).natDegree < k + 1) ∧
      ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        ∀ j < deg, (P z).coeff j = (B j).eval z := by
  obtain ⟨B, hBdeg, hBeval⟩ :=
    coeffPolys_of_largeCommonAgreement domain (fun t => u t) P
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
      s hs_inj hPdeg hsG hCommon
  exact ⟨B, fun j _ => hBdeg j, hBeval⟩

end ProximityGap
