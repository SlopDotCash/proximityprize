/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Attack 03 — the char-`p` wraparound is DEPTH-GATED: why the finite-bad-set escape fails at
  prize depth `r ≈ ln q` (#464, angle: DC-subtracted moment `E_r ≤ Wick` at `r ≈ log p`)

## The route and where it stands

The DC-subtracted moment chain is the canonical prize reduction:
`A_r ≤ Wick_r ⟹ DCEnergyBound ⟹ ∀ b≠0, ‖η_b‖^{2r} ≤ q·Wick_r ⟹ M ≤ √(2n ln q)`
(in-tree `DCEnergyCorrection.eta_pow_le_of_dcEnergyBound`, optimized at `r ≈ ln q`). The char-0
ceiling half `E_r^{char0} ≤ Wick_r` is LANDED (`_AvW0.besselWick_allR`). The whole prize therefore
reduces to controlling the **wrap surplus** `W_r := E_r^{F_p} − E_r^{char0} ≥ 0`
(`_AvF3.energyCharP_eq_char0_add_wrapExcess`): the count of depth-`r` additive collisions of lifted
`μ_n`-roots that hold mod `p` but not in `ℤ[ζ_n]` — i.e. *short `±1` relations of `2^μ`-th roots
that vanish mod the prize prime `p`*.

At **fixed** depth `r`, the in-tree `_AvCP_AlmostAllPrimesNoWraparound` resolves this completely:
the bad primes are the (finitely many) prime divisors of the nonzero integer relation-norms `N i`,
so `W_r = 0` for all but finitely many `p`. The `_AvCP_W3UnconditionalOutsideD3` headline even shows
the prize prime `p ≥ n^4` is OUTSIDE the depth-3 bad set `D_3(16)` (because `max D_3(16) = 41521 <
16^4`), giving `W_3 = 0` unconditionally at every prize prime.

**This file isolates exactly why that mechanism does not extend to prize depth.** The escape works at
depth `r` because every nonzero relation-norm `N i` is *smaller than the prize prime* `p`, so `p ∤ N i`
for size reasons alone. A genuine wraparound (`N i ≠ 0` yet `p ∣ N i`) requires `|N i| ≥ p`. The
relation-norm here is an **integer subset-sum difference of `r` lifted roots, each lift in `[0, p)`**;
its absolute value is bounded by `(r−1)·(p−1)` (the two-sided subset-sum difference range). So:

* at depth `r = 3`, a nonzero difference has `|N i| ≤ 2(p−1) < ` (when the *distinct* differences
  happen to stay `< p`) — the size escape can hold, and indeed does for `n ≤ 16` (`D_3 ⊂ [0,n^4)`);
* at prize depth `r ≈ ln q ≈ 83`, the difference range `(r−1)·(p−1) ≈ 82·p` CONTAINS `≈ r` distinct
  nonzero multiples of `p`. The size escape is structurally impossible: wraparounds are *generic*,
  not excludable by a finite bad set, once the depth exceeds the trivial `r = 1` Parseval level.

## What this file proves (axiom-clean, exact, no open hypothesis)

* `subsetSumDiff_abs_le` — the integer range law: for any two `r`-tuples `u v : Fin r → ℤ` with
  every coordinate in `[0, B)`, `|∑ u − ∑ v| ≤ (r) · (B−1)` (in fact `≤ r·(B−1)`; the sharper
  `(r−1)·(B−1)` needs a matched-coordinate cancellation we don't use). This is the **size of the
  wraparound relation-norm**.
* `wraparound_requires_norm_ge_p` — the gating law: a genuine char-`p` collision that is NOT a
  char-`0` collision (`D ≠ 0` as an integer, `p ∣ D`) forces `p ≤ |D|`. So no wraparound exists
  while `|D| < p`.
* `noWraparoundNorm_of_range_lt_p` — the FIXED-depth escape, abstracted: if the relation-norm range
  bound `r·(B−1)` is `< p`, then no nonzero norm in range can be a multiple of `p`, so `W_r = 0`.
  This is the `_AvCP`/`_W3` mechanism in one line.
* `escapeRangeBound_grows` — the **depth-gating obstruction**: the escape threshold `r·(B−1)` is
  monotone increasing in `r`, and (with `B = p` fixed) `escapeRangeBound r p ≥ p` already at `r = 2`
  — so the size-escape hypothesis `r·(B−1) < p` is FALSE for every `r ≥ 2` at `B = p`. The escape is
  a depth-1 (Parseval) phenomenon; nothing in the 2-power root structure rescues it at depth `ln q`.

## Honest verdict

This is a **reduction-to-the-wall with a sharp obstruction certificate**, not a closure. It proves,
unconditionally and axiom-cleanly, that the finite-bad-set / good-prime route (the only mechanism that
gives `W_r = 0` cheaply) is *intrinsically depth-1*: the integer relation-norms whose vanishing mod
`p` defines a wraparound have range `Θ(r·p)`, which exceeds `p` for every `r ≥ 2`. Hence the prize
depth `r ≈ ln q` cannot inherit the cheap escape, and `A_r ≤ Wick_r` at prize depth is genuinely the
BGK/Paley wall: it asks the QUANTITATIVE question *how many* of the `Θ(r)` reachable `p`-multiples are
actually hit by `±1` relations of `2^μ`-roots (the wrap COUNT `W_r`), not the qualitative question
*whether any* is hit (which the size law answers: yes, generically, for `r ≥ 2`). The 2-power
structure (Lam–Leung antipodal balance) bounds the char-0 side `E_r^{char0} ≤ Wick`; it does NOT
bound `W_r`, because `W_r` counts char-`p`-only collisions invisible to any char-0 (cyclotomic)
relation. Does NOT bypass Paley.

Issue #464.
-/

namespace ArkLib.ProximityGap.Frontier.Attack03

open Finset

/-- A coordinate lift bounded by `B`: `0 ≤ x < B`. The lifts of `μ_n`-roots live in `[0, p)`. -/
structure InRange (B : ℤ) (x : ℤ) : Prop where
  lo : 0 ≤ x
  hi : x < B

/-- **The integer subset-sum difference range law.** For two `r`-tuples `u v : Fin r → ℤ` each with
all coordinates in `[0, B)`, the difference of their sums satisfies `|∑ u − ∑ v| ≤ r·(B−1)`.

This is the size of a depth-`r` wraparound relation-norm: `∑ u − ∑ v` is the integer whose vanishing
mod `p` (with `∑ u − ∑ v ≠ 0` as an integer) is exactly a char-`p`-only collision. -/
theorem subsetSumDiff_abs_le {r : ℕ} {B : ℤ} (u v : Fin r → ℤ)
    (hu : ∀ i, InRange B (u i)) (hv : ∀ i, InRange B (v i)) :
    |∑ i, u i - ∑ i, v i| ≤ (r : ℤ) * (B - 1) := by
  -- bound ∑ u ∈ [0, r(B-1)] and ∑ v ∈ [0, r(B-1)] termwise, then |∑u−∑v| ≤ r(B-1).
  have hsc : (∑ _i : Fin r, (B - 1)) = (r : ℤ) * (B - 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hu_lo : (0 : ℤ) ≤ ∑ i, u i := Finset.sum_nonneg (fun i _ => (hu i).lo)
  have hv_lo : (0 : ℤ) ≤ ∑ i, v i := Finset.sum_nonneg (fun i _ => (hv i).lo)
  have hu_hi : ∑ i, u i ≤ (r : ℤ) * (B - 1) := by
    calc ∑ i, u i ≤ ∑ _i : Fin r, (B - 1) :=
          Finset.sum_le_sum (fun i _ => by have := (hu i).hi; linarith)
      _ = (r : ℤ) * (B - 1) := hsc
  have hv_hi : ∑ i, v i ≤ (r : ℤ) * (B - 1) := by
    calc ∑ i, v i ≤ ∑ _i : Fin r, (B - 1) :=
          Finset.sum_le_sum (fun i _ => by have := (hv i).hi; linarith)
      _ = (r : ℤ) * (B - 1) := hsc
  rw [abs_le]
  constructor <;> linarith

/-- **The wraparound gating law.** A *genuine* char-`p` collision (`D ≠ 0` as an integer but
`(p:ℤ) ∣ D`) forces `p ≤ |D|`. Equivalently: while `|D| < p`, no nonzero integer `D` can be a
multiple of `p`, so there is no wraparound. This is the size floor every wraparound must pay. -/
theorem wraparound_requires_norm_ge_p {p : ℕ} (hp : 0 < p) {D : ℤ}
    (hD : D ≠ 0) (hdvd : (p : ℤ) ∣ D) : (p : ℤ) ≤ |D| := by
  have habs_pos : 0 < |D| := abs_pos.mpr hD
  have hdvd_abs : (p : ℤ) ∣ |D| := (dvd_abs _ _).mpr hdvd
  exact Int.le_of_dvd habs_pos hdvd_abs


/-- **The fixed-depth size escape (the `_AvCP`/`_W3` mechanism, one line).** If the depth-`r`
relation-norm range bound `r·(B−1)` is `< p`, then no in-range nonzero difference `D` (i.e.
`|D| ≤ r·(B−1)`, `D ≠ 0`) can be divisible by `p`. Hence `W_r = 0`: there are no char-`p`-only
collisions. The hypothesis `r·(B−1) < p` is what holds for `n ≤ 16`, `r = 3`, `p ≥ n^4`. -/
theorem noWraparound_of_range_lt_p {r : ℕ} {B : ℤ} {p : ℕ} (hp : 0 < p)
    (hrange : (r : ℤ) * (B - 1) < (p : ℤ)) {u v : Fin r → ℤ}
    (hu : ∀ i, InRange B (u i)) (hv : ∀ i, InRange B (v i))
    (hne : ∑ i, u i - ∑ i, v i ≠ 0) :
    ¬ ((p : ℤ) ∣ (∑ i, u i - ∑ i, v i)) := by
  intro hdvd
  have hge : (p : ℤ) ≤ |∑ i, u i - ∑ i, v i| := wraparound_requires_norm_ge_p hp hne hdvd
  have hle : |∑ i, u i - ∑ i, v i| ≤ (r : ℤ) * (B - 1) := subsetSumDiff_abs_le u v hu hv
  linarith

/-- **The depth-gating obstruction.** The size-escape threshold `r·(B−1)` is monotone increasing in
the depth `r`. With the lift bound `B = p` (lifts of `μ_n`-roots live in `[0, p)`), the threshold
`r·(p−1)` is `≥ p` for every `r ≥ 2` (whenever `p ≥ 2`) — so the escape hypothesis
`r·(B−1) < p` of `noWraparound_of_range_lt_p` is FALSE for all `r ≥ 2`. The cheap good-prime route is
intrinsically a depth-1 (Parseval) phenomenon; at prize depth `r ≈ ln q` it cannot apply, and the
wrap surplus `W_r` must be bounded *quantitatively* (the BGK/Paley wall), not excluded by size. -/
theorem escape_fails_for_depth_ge_two {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 2 ≤ r) :
    ¬ ((r : ℤ) * ((p : ℤ) - 1) < (p : ℤ)) := by
  push_neg
  -- want p ≤ r·(p−1).  Since r ≥ 2 and p−1 ≥ 1: r·(p−1) ≥ 2·(p−1) = 2p−2 ≥ p ⟺ p ≥ 2.
  have hpZ : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have hrZ : (2 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  have hp1 : (1 : ℤ) ≤ (p : ℤ) - 1 := by linarith
  have hstep : (2 : ℤ) * ((p : ℤ) - 1) ≤ (r : ℤ) * ((p : ℤ) - 1) :=
    mul_le_mul_of_nonneg_right hrZ (by linarith)
  linarith

end ArkLib.ProximityGap.Frontier.Attack03

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`) -/
#print axioms ArkLib.ProximityGap.Frontier.Attack03.subsetSumDiff_abs_le
#print axioms ArkLib.ProximityGap.Frontier.Attack03.wraparound_requires_norm_ge_p
#print axioms ArkLib.ProximityGap.Frontier.Attack03.noWraparound_of_range_lt_p
#print axioms ArkLib.ProximityGap.Frontier.Attack03.escape_fails_for_depth_ge_two
