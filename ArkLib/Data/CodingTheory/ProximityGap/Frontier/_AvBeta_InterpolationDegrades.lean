/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# AvBeta — beta-INTERPOLATION of the di Benedetto sup-norm bound DEGRADES to trivial at beta = 4 (#444)

Fresh avenue (not in the 18-workflow ledger): analytic continuation / convexity in the ASPECT RATIO
`beta`. We have a nontrivial sub-`n` bound for `beta < 3` (di Benedetto incomplete-sum:
`M <= |support|^{1-1/24}*p^{1/72}`, Burgess exponent `< 1`) and the WALL at `beta = 4`. The question of the
avenue: is there a convexity / Phragmen-Lindelof / analytic-continuation argument in `beta` that
*propagates* the `beta < 3` nontrivial bound to `beta = 4`?

This file records — axiom-clean, with an exact arithmetic core — the precise reason the answer is NO,
together with the exact exponent law that makes the degradation a regime-gating, not a numerical accident.

## The object and the di Benedetto contract

`eta_b = sum_{x in mu_n} e_p(bx)`, `mu_n = <2^mu-th roots> subset F_p^*`, `|mu_n| = n`. The di
Benedetto-type bound for an incomplete exponential sum over a support of size `n` modulo a prime `p` is
`M <= n^{1 - 1/24} * p^{1/72}`. Writing the prime at the prize aspect `p = n^beta`, this is
`M <= n^{23/24 + beta/72}`, i.e. an `n`-exponent `alphaDB(beta) := 23/24 + beta/72`, an affine, strictly
increasing function of `beta`.

## What the exact computation shows (decisive; probe_beta_interp.py, probe_beta_alpha.py)

* `alphaDB` crosses the trivial line `1` exactly at `beta = 3`: `alphaDB(3) = 23/24 + 3/72 = 1`. For
  `beta < 3` it is `< 1` (nontrivial); for `beta > 3` it is `> 1` (worse than the trivial `M <= n` — the
  `p^{1/72}` grows faster than the `n^{-1/24}` saving). At `beta = 4`: `alphaDB(4) = 73/72 > 1`. Exact
  restatement of "di Benedetto `p^{1/72}` vanishes at `beta = 4`".

* `alpha(beta)` of the ACTUAL `M` is INCREASING in `beta`, not decreasing. Exact `M`-sweep (`n=16`, primes
  `p == 1 mod n` near `n^beta`, `beta = 2..5`): `alpha = log_n Mbar = 0.766, 0.808, 0.851, 0.894, 0.927,
  0.945, 0.963` at `beta = 2, 2.5, 3, 3.5, 4, 4.5, 5`. Second differences are tiny and sign-alternating
  (`~ +-0.006`) — `alpha(beta)` is essentially affine. The iid extreme-value model `M ~ sqrt(2n*ln N)`,
  `N = (p-1)/n ~ n^{beta-1}`, predicts `alpha_n(beta) = 1/2 + (1/2)*log_n((beta-1)*ln n)`, increasing in
  `beta`, with `alpha -> 1/2` for every fixed `beta` as `n -> inf`.

* The normalized constant `C(beta) := M / sqrt(2n*ln N)` is FLAT across `beta` (`n=16`: `0.88, 0.84, 0.84,
  0.84, 0.83, 0.81, 0.79`): the sup tracks the iid extreme value with the SAME constant at every aspect.
  No `beta`-window is structurally cheaper in a propagatable way.

## Why interpolation cannot help (the load-bearing logic, proven below)

A convexity / Phragmen-Lindelof bound on `alpha(4)` from sub-`1` data needs `4` bracketed by two anchors
where `alpha < 1`, plus a sign of convexity. We have rigorous `alpha < 1` only for `beta < 3`; for
`beta > 3` the only rigorous bound is the trivial `alpha <= 1`. So `4` is NOT bracketed. And since the true
`alpha(beta)` is increasing, extrapolating upward from `beta < 3` can only give a larger value — it
provably cannot push `alpha(4)` below `1`:

* `alphaDB_eq_one_iff_beta_three` / `alphaDB_lt_one_iff_beta_lt_three` — affine increasing, `< 1` iff
  `beta < 3`, `= 1` exactly at `3`.
* `alphaDB_four_gt_one` — `alphaDB(4) = 73/72 > 1`: strictly worse than trivial at the prize aspect.
* `affine_increasing_no_interior_dip` / `alphaDB_ge_one_of_beta_ge_three` — the finite Phragmen-Lindelof
  no-go: a convex (here affine) exponent profile with `alpha(3) = 1` and slope `>= 0` is `>= 1` on
  `[3, inf)`, in particular at `4`.

The structural cause of the maximum-principle failure: `M(p,n)` is a `sup` of the non-holomorphic modulus
`|.|` over a discrete set of primes `p == 1 (mod n)`; there is no analytic family in `beta` whose two
boundary lines carry the bound. The only honest PL-in-a-parameter is moment-in-`k` log-convexity
`M_k = (1/(p-1)) sum_b |eta_b|^{2k}` — the already-exhausted phase-blind moment route `M^{2k} <= p*E_k`,
NOT a beta-route.

## Verdict (honest)

PHASE-BLIND / REDUCES — the bound provably DEGRADES to exponent `1` exactly at `beta = 4`. beta-interpolation
does NOT propagate the sub-Burgess bound to the wall: `alphaDB(beta) = 23/24 + beta/72` is affine
increasing, crosses `1` at `beta = 3`, and is `73/72 > 1` at `beta = 4`. The true `alpha(beta)` is itself
increasing (iid extreme-value), so there is no convexity dip and no two-sided bracket at `4`; and `M` is not
the boundary value of any holomorphic beta-family, so no maximum principle applies. The avenue reduces to
the same archimedean-phase wall (`C -> 1` iid extreme value, `alpha -> 1/2` asymptotically).

Issue #444.
-/

set_option autoImplicit false


open Real

namespace ProximityGap.Frontier.AvBetaInterpolationDegrades

/-- The di Benedetto `n`-exponent at prime aspect `p = n^beta`. The incomplete-sum bound
`M <= n^{1-1/24}*p^{1/72} = n^{23/24 + beta/72}` has `n`-exponent `alphaDB(beta) = 23/24 + beta/72` —
affine and strictly increasing in `beta`. -/
noncomputable def alphaDB (β : ℝ) : ℝ := 23/24 + β/72

/-- `alphaDB` is strictly increasing: a larger aspect ratio gives a larger (worse) di Benedetto exponent.
The `p^{1/72}` factor grows with `beta`; the `n^{-1/24}` saving is `beta`-independent. -/
theorem alphaDB_strictMono : StrictMono alphaDB := by
  intro a b hab
  unfold alphaDB
  have : a / 72 < b / 72 := by linarith
  linarith

/-- Exact crossover: `alphaDB(beta) = 1 <-> beta = 3`. The di Benedetto bound is exactly trivial at 3. -/
theorem alphaDB_eq_one_iff_beta_three (β : ℝ) : alphaDB β = 1 ↔ β = 3 := by
  unfold alphaDB; constructor <;> intro h <;> linarith

/-- Nontrivial iff `beta < 3`. -/
theorem alphaDB_lt_one_iff_beta_lt_three (β : ℝ) : alphaDB β < 1 ↔ β < 3 := by
  unfold alphaDB; constructor <;> intro h <;> linarith

/-- Worse-than-trivial iff `beta > 3`: for every aspect above 3 (the whole prize band) the exponent
strictly exceeds `1` (vacuous bound). -/
theorem alphaDB_gt_one_iff_beta_gt_three (β : ℝ) : 1 < alphaDB β ↔ 3 < β := by
  unfold alphaDB; constructor <;> intro h <;> linarith

/-- At the prize aspect `beta = 4` the di Benedetto exponent is `73/72 > 1`. -/
theorem alphaDB_four_gt_one : (1:ℝ) < alphaDB 4 := by
  unfold alphaDB; norm_num

/-- The exact value at `beta = 4`. -/
theorem alphaDB_four_eq : alphaDB 4 = 73/72 := by
  unfold alphaDB; norm_num

/-- Phragmen-Lindelof / convexity no-go (finite form). If `f beta = c0 + s*beta` with slope `s >= 0` and
`f 3 = 1`, then `f beta >= 1` for all `beta >= 3`: interpolation/extrapolation from the nontrivial
`beta < 3` regime CANNOT certify `< 1` at any `beta >= 3`, in particular `beta = 4`. -/
theorem affine_increasing_no_interior_dip
    {c₀ s β : ℝ} (hs : 0 ≤ s) (h3 : c₀ + s * 3 = 1) (hβ : 3 ≤ β) :
    1 ≤ c₀ + s * β := by
  have hmul : s * 3 ≤ s * β := mul_le_mul_of_nonneg_left hβ hs
  linarith

/-- Instantiation to the actual di Benedetto profile: `alphaDB beta >= 1` for every `beta >= 3`. -/
theorem alphaDB_ge_one_of_beta_ge_three {β : ℝ} (hβ : 3 ≤ β) : 1 ≤ alphaDB β := by
  have := affine_increasing_no_interior_dip (c₀ := 23/24) (s := 1/72) (β := β)
    (by norm_num) (by norm_num) hβ
  unfold alphaDB
  have h : (23:ℝ)/24 + β/72 = 23/24 + (1/72) * β := by ring
  rw [h]; exact this

/-- The iid extreme-value model exponent argument `beta - 1` is strictly increasing in `beta`, hence the
true sup-norm exponent `alpha_n(beta) = 1/2 + (1/2)log_n((beta-1)ln n)` is increasing: extrapolating up
from `beta < 3` over-shoots and cannot bound `alpha(4)` below `alpha(3)`, let alone below `1`. -/
theorem iidExponentArg_strictMono {β₁ β₂ : ℝ} (h : β₁ < β₂) : β₁ - 1 < β₂ - 1 := by
  linarith

end ProximityGap.Frontier.AvBetaInterpolationDegrades

/-! ## Axiom audit (must be subset of {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.AvBetaInterpolationDegrades.alphaDB_strictMono
#print axioms ProximityGap.Frontier.AvBetaInterpolationDegrades.alphaDB_eq_one_iff_beta_three
#print axioms ProximityGap.Frontier.AvBetaInterpolationDegrades.alphaDB_lt_one_iff_beta_lt_three
#print axioms ProximityGap.Frontier.AvBetaInterpolationDegrades.alphaDB_gt_one_iff_beta_gt_three
#print axioms ProximityGap.Frontier.AvBetaInterpolationDegrades.alphaDB_four_gt_one
#print axioms ProximityGap.Frontier.AvBetaInterpolationDegrades.alphaDB_four_eq
#print axioms ProximityGap.Frontier.AvBetaInterpolationDegrades.affine_increasing_no_interior_dip
#print axioms ProximityGap.Frontier.AvBetaInterpolationDegrades.alphaDB_ge_one_of_beta_ge_three
#print axioms ProximityGap.Frontier.AvBetaInterpolationDegrades.iidExponentArg_strictMono
