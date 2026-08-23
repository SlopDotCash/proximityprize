/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The Gauss-period parallelogram tower (#407) — the exact L^∞/phase-alignment backbone

The proximity prize reduces to square-root cancellation of incomplete character sums (Gauss
periods) over the dyadic subgroup `μ_{2^μ} ⊂ F_p*` at depth `r ≍ log p` (regime `n = |μ_n| ~
p^{1/4}`) — the recognized open BGK/Bourgain problem.  The L² (moment/energy) hierarchy is proven
to stop at Johnson (the `n^{1/2}` deficit).  This file provides the EXACT backbone of the live
L^∞/phase-alignment route: the dyadic Gauss period `η_b(μ_n)` and its quadratic twist satisfy a
parallelogram recursion onto the level-`(n/2)` coset periods, turning the depth-`log p` estimate
into a single per-level descent inequality (the remaining open input).

Numerics (`probe_gauss_period_{parallelogram,bstar}.py`, `p ≈ n^4`, `n = 8,16,32`): at `b*` the two
coset periods are `cos = 1.0000` aligned EXACTLY — because for `4 ∣ n`, `−1 = ζ^{n/2} ∈ μ_{n/2}`, each
coset is negation-symmetric, so `A, B` are **real for every `b`** (`η_b(μ_n)` is a real Gaussian
period); the alignment is just *same sign* at `b*` (NOT `A = B`: `n=8`, `A=−3.70 ≠ B=−3.86`).  Maxima
balanced (`M_untw ≈ M_tw`).  So `‖η_{b*}(μ_n)‖ = A_{b*}+B_{b*}` and the √2-descent reduces to the real
two-term inequality `A_{b*}+B_{b*} ≤ √2·M_{n/2}·(1+log-corr)`.
-/
open Finset

namespace ArkLib.ProximityGap.GaussPeriodTower

/-- **The Gauss-period parallelogram recursion** — the exact tool for the L^∞/phase-alignment
descent of the proximity prize.

For a dyadic subgroup `μ_n = μ_{n/2} ⊔ ζ·μ_{n/2}` (`n = 2^μ`) and additive character value
function `f := (x ↦ ψ(b·x))`, write `A = ∑_{x∈μ_{n/2}} f x` (period of the squares-coset) and
`B = ∑_{x∈ζμ_{n/2}} f x` (period of the other coset). Then the level-`n` Gauss period is `A + B`
and its quadratic twist (`+1` on `μ_{n/2}`, `−1` on `ζμ_{n/2}`) is `A − B`, and the parallelogram
law gives the EXACT recursion

> `‖η_b(μ_n)‖² + ‖η^χ_b(μ_n)‖² = 2·(‖A‖² + ‖B‖²)`.

Taking `max_b` and using that `A, B` are values of the level-`(n/2)` subgroup period, this reduces
the prize bound `max_b‖η_b(μ_n)‖ ≲ √(n·log(q/n))` to a **per-level descent**: at the level-`n`
maximizer `b*` the two cosets are *aligned* (`cos = 1.0000` exactly — `A, B` real for `4 ∣ n`, same
sign at `b*`; not `A = B`) so `‖η_{b*}(μ_n)‖ = A_{b*}+B_{b*}`, and the √2-descent needs the
*sub-maximality* of `‖A‖ = ‖η_{b*}(μ_{n/2})‖` (with its same-sign partner `B`) relative to the level-`(n/2)` max — the structural (open) core, now stated as one
recursive inequality rather than a depth-`log q` moment estimate. This lemma is the exact, reusable
backbone; the descent inequality is the single remaining (open) input. -/
theorem gaussPeriod_parallelogram_recursion {V : Type*} (S0 S1 : Finset V) (f : V → ℂ) :
    ‖(∑ x ∈ S0, f x) + (∑ x ∈ S1, f x)‖ ^ 2 + ‖(∑ x ∈ S0, f x) - (∑ x ∈ S1, f x)‖ ^ 2
      = 2 * (‖∑ x ∈ S0, f x‖ ^ 2 + ‖∑ x ∈ S1, f x‖ ^ 2) := by
  exact parallelogram_law_with_norm ℝ (∑ x ∈ S0, f x) (∑ x ∈ S1, f x)

/-- **The twist is the difference of coset periods** (the identity that makes the recursion concrete):
when `S = S0 ⊔ S1` and the twist colours `S0` by `+1`, `S1` by `−1`, the twisted period is
`(∑_{S0} f) − (∑_{S1} f)`, i.e. the second slot of the parallelogram. -/
theorem twistedPeriod_eq_sub {V : Type*} [DecidableEq V] (S0 S1 : Finset V) (hdisj : Disjoint S0 S1)
    (f : V → ℂ) :
    (∑ x ∈ S0 ∪ S1, (if x ∈ S0 then (1 : ℂ) else -1) * f x)
      = (∑ x ∈ S0, f x) - (∑ x ∈ S1, f x) := by
  classical
  rw [Finset.sum_union hdisj]
  have h0 : (∑ x ∈ S0, (if x ∈ S0 then (1 : ℂ) else -1) * f x) = ∑ x ∈ S0, f x :=
    Finset.sum_congr rfl (fun x hx => by rw [if_pos hx, one_mul])
  have h1 : (∑ x ∈ S1, (if x ∈ S0 then (1 : ℂ) else -1) * f x) = - ∑ x ∈ S1, f x := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [if_neg (fun hx0 => (Finset.disjoint_left.mp hdisj) hx0 hx), neg_one_mul]
  rw [h0, h1, sub_eq_add_neg]

/-- **The untwisted period is the sum of coset periods.** -/
theorem period_eq_add {V : Type*} [DecidableEq V] (S0 S1 : Finset V) (hdisj : Disjoint S0 S1)
    (f : V → ℂ) :
    (∑ x ∈ S0 ∪ S1, f x) = (∑ x ∈ S0, f x) + (∑ x ∈ S1, f x) :=
  Finset.sum_union hdisj


/-- Conjugation of a finite-group additive-character value is the negation pullback (root of unity). -/
private theorem addChar_conj_aux {V : Type*} [AddCommGroup V] [Fintype V] (ψ : AddChar V ℂ) (a : V) :
    (starRingEnd ℂ) (ψ a) = ψ (-a) := by
  have hca : (Fintype.card V) • a = 0 :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).mp addOrderOf_dvd_card
  have hpow : ψ a ^ (Fintype.card V) = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, hca, ψ.map_zero_eq_one]
  have hnorm : ‖ψ a‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow (by positivity)
  rw [AddChar.map_neg_eq_inv]; exact (Complex.inv_eq_conj hnorm).symm

/-- **The period of a negation-closed set is real (conjugation-fixed).** If `S = −S`, the Gauss
period `∑_{x∈S} ψ(x)` is fixed by complex conjugation.  This is why the dyadic Gauss period
`η_b(μ_n)` is real for every `b` (n even ⟹ `−1 ∈ μ_n` ⟹ `bμ_n` negation-closed): the structural
handle that turns the prize's per-level descent into a *real-variable* extremal problem on a
self-similar tower of real Gaussian periods. -/
theorem period_conj_eq_of_neg_closed {V : Type*} [AddCommGroup V] [Fintype V]
    (S : Finset V) (hS : ∀ x ∈ S, -x ∈ S) (ψ : AddChar V ℂ) :
    (starRingEnd ℂ) (∑ x ∈ S, ψ x) = ∑ x ∈ S, ψ x := by
  rw [map_sum]
  simp only [addChar_conj_aux]
  refine Finset.sum_nbij' (fun x => -x) (fun x => -x) ?_ ?_ ?_ ?_ ?_
  · intro x hx; exact hS x hx
  · intro x hx; exact hS x hx
  · intro x _; exact neg_neg x
  · intro x _; exact neg_neg x
  · intro x _; rfl

/-- The period of a negation-closed set has zero imaginary part — it is a real number. -/
theorem period_im_zero_of_neg_closed {V : Type*} [AddCommGroup V] [Fintype V]
    (S : Finset V) (hS : ∀ x ∈ S, -x ∈ S) (ψ : AddChar V ℂ) :
    (∑ x ∈ S, ψ x).im = 0 := by
  have h := period_conj_eq_of_neg_closed S hS ψ
  rw [Complex.conj_eq_iff_im] at h; exact h

end ArkLib.ProximityGap.GaussPeriodTower

#print axioms ArkLib.ProximityGap.GaussPeriodTower.gaussPeriod_parallelogram_recursion
#print axioms ArkLib.ProximityGap.GaussPeriodTower.twistedPeriod_eq_sub
#print axioms ArkLib.ProximityGap.GaussPeriodTower.period_eq_add
#print axioms ArkLib.ProximityGap.GaussPeriodTower.period_conj_eq_of_neg_closed
#print axioms ArkLib.ProximityGap.GaussPeriodTower.period_im_zero_of_neg_closed
