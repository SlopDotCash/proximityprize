/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Chapter 5 scaffold — the Bounded-Conductor Depth Transform (#444)

SELF-CONTAINED scaffold (Mathlib-only imports) for the *depth-graded conductor* `c_d(r)`
proposed in Chapter 5 of "New Mathematics".  This file does NOT consume the heavy
ProximityGap substrate (so `lake env lean` checks it without a warm cone build); it states
the new object as an honest abstract structure and proves the ONE arithmetic gluing lemma
that the proposal turns on: a *budget telescoping* showing that IF the depth-graded pieces
each carry an `O(1)` conductor (the new conjecture), THEN the total deviation is `≤ C·√q`
with a SINGLE geometric loss `C`, escaping the `√rank = n^{r-1/2}` Weil-II deficit of the
monolithic moment sheaf.

## Honest status (tags as in the chapter)
* DEFINED here: `DepthGraded`, `BoundedDepthConductor`, `depthTotalDeviation`.
* PROVEN here (axiom-clean, pure arithmetic): `bounded_depth_telescopes` — the gluing lemma.
* CONJECTURED (named, NOT proven): `BoundedDepthConductor` holds at the prize point.  This is
  the new conjecture isolated by the chapter; it is STRICTLY WEAKER than asking the monolithic
  `cond(M^{*r}) = O(1)` (proven FALSE: rank-driven `~ n^{2r-1}`), because it only asks each
  fixed-depth piece — whose rank is bounded INDEPENDENTLY of `r` — to be Weil-clean.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.DepthGradedConductor

/-- **DEFINED.** A *depth-graded deviation profile*: the cumulant excess at moment order `r`,
`Δ(r) := q·E_r − |G|^{2r} − q·(2r−1)‼·n^r` (deviation from the Wick/real-Gaussian value),
is split into `D` depth pieces `δ d r`, `d = 0,…,D−1`, summing to `Δ(r)`.

The depth index `d` filters the `r`-fold convolution sheaf by *carrier complexity* — the
number of distinct ramified points engaged.  Depth `0` is the diagonal (the Wick skeleton);
higher depth carries the off-diagonal Frobenius-correlation mass. -/
structure DepthGraded (D : ℕ) where
  /-- the deviation contributed by depth-`d` carriers at moment order `r`. -/
  piece : ℕ → ℕ → ℝ
  /-- depth never exceeds the grading bound. -/
  depthBound : ℕ → ℕ
  depthBound_le : ∀ r, depthBound r ≤ D

/-- **DEFINED.** The total deviation reconstructed from the depth grading at order `r`:
`Δ(r) = ∑_{d < D} δ d r`. -/
def depthTotalDeviation {D : ℕ} (P : DepthGraded D) (r : ℕ) : ℝ :=
  ∑ d ∈ Finset.range D, P.piece d r

/-- **CONJECTURED (named hypothesis).** *Bounded depth conductor.*  Each depth-`d` piece is
Weil-clean with a conductor base `κ` that is bounded UNIFORMLY in the depth `d` and the
moment order `r`:  `|δ d r| ≤ κ · √q`.

This is the chapter's new conjecture.  It is the precise weakening that escapes the no-go:
the monolithic conductor `cond(M^{*r}) ~ n^{2r-1}` blows up in `r`, but each fixed-depth
slice — being a convolution of a *bounded* number of Kummer sheaves — has rank bounded by a
constant depending only on `d` (not on `r`), so Weil-II over it loses only `O(1)·√q`. -/
def BoundedDepthConductor {D : ℕ} (P : DepthGraded D) (κ q : ℝ) : Prop :=
  ∀ r, ∀ d ∈ Finset.range D, |P.piece d r| ≤ κ * Real.sqrt q

/-- **PROVEN (axiom-clean, pure arithmetic) — the gluing lemma.**  If the depth grading is
bounded-conductor with base `κ` over `D` depths, then the TOTAL deviation at every order `r`
is controlled by a SINGLE geometric loss `D·κ·√q` — crucially, the bound is *independent of
`r`*: there is no `√rank = n^{r−1/2}` blow-up, because the rank that enters is the bounded
depth count `D`, not the moment-sheaf dimension `n^{2r−1}`.

This is the entire provable content of the Bounded-Conductor Depth Transform: it converts the
conjectured per-depth `O(1)` cleanliness into a uniform-in-`r` total bound, which is exactly
the input the effective-Katz consumer needs (and which monolithic Weil-II cannot supply). -/
theorem bounded_depth_telescopes {D : ℕ} (P : DepthGraded D) {κ q : ℝ}
    (hκ : 0 ≤ κ) (hq : 0 ≤ q) (h : BoundedDepthConductor P κ q) (r : ℕ) :
    |depthTotalDeviation P r| ≤ (D : ℝ) * (κ * Real.sqrt q) := by
  unfold depthTotalDeviation
  calc |∑ d ∈ Finset.range D, P.piece d r|
      ≤ ∑ d ∈ Finset.range D, |P.piece d r| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.range D, κ * Real.sqrt q := by
        apply Finset.sum_le_sum
        intro d hd
        exact h r d hd
    _ = (D : ℝ) * (κ * Real.sqrt q) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **PROVEN corollary.**  The total deviation is `≤ C·√q` with the SINGLE geometric constant
`C = D·κ` — the bounded-conductor escape from the `n^{r−1/2}` Weil-II deficit, stated in the
exact shape the effective conductor consumer expects (`deviation ≤ C·√q`, `C = O(1)`). -/
theorem total_deviation_le_const_sqrt {D : ℕ} (P : DepthGraded D) {κ q : ℝ}
    (hκ : 0 ≤ κ) (hq : 0 ≤ q) (h : BoundedDepthConductor P κ q) (r : ℕ) :
    |depthTotalDeviation P r| ≤ ((D : ℝ) * κ) * Real.sqrt q := by
  have := bounded_depth_telescopes P hκ hq h r
  calc |depthTotalDeviation P r| ≤ (D : ℝ) * (κ * Real.sqrt q) := this
    _ = ((D : ℝ) * κ) * Real.sqrt q := by ring

end ArkLib.ProximityGap.Frontier.DepthGradedConductor

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.DepthGradedConductor.bounded_depth_telescopes
#print axioms ArkLib.ProximityGap.Frontier.DepthGradedConductor.total_deviation_le_const_sqrt
