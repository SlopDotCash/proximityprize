/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum

/-!
# P1 rate-quarter predecessor: multi-core quotient-budget ledger (FSMG)

Exact arithmetic backbone for the miniature/extremal landscape analysis of the
predecessor residual `CanonicalUniformPredecessorBadCount` (P1: `N = 2^30`,
`K = 2^28`, `T = 592794966`).

A pencil core `D` of size `z` on which a received row is Reed--Solomon
restricted imposes `z - K` linear conditions, but the global code `RS_K`
satisfies all of them, so the honest degrees-of-freedom budget for multi-core
constructions lives in the quotient `F^N / RS_K` of dimension `N - K`.  The
generic "one fresh coordinate per scalar" mechanism (the exact mechanism of
the 2026-07-10 rate-half three-core radix counterexample) requires cores of
size `T - 1`, each costing `T - 1 - K` quotient dimensions.

This file pins, kernel-checked:

* the three-core budget at rate quarter is **negative**
  (`N - K = 805306368 < 973078527 = 3 (T - 1 - K)`), so the rate-half
  refutation mechanism is closed at the rate-quarter predecessor;
* the two-core budget is positive (`156587350` quotient dimensions);
* the generic two-core scalar cap is `2 (N - T + 1) = 961893718 < N`, with
  exact margin `N - 2 (N - T + 1) = 2 T - N - 2 = 2 (r + d + 1) = 111848106`;
* the rate-half contrast (`n - k - 3 (t - 1 - k) = 29 m' > 0` at
  `m' = 2^24`), explaining why the same mechanism refuted the rate-half
  predecessor pin;
* the `m = 2` miniature (`[N=32, K=8, T=18]`) shows the identical signs, so
  the exact miniature censuses (probe `probe_fsmg_miniature_extremal.py`:
  three-core spline space collapses onto the global code and has zero bad
  scalars; two-core stacks reach exactly `30 = 2(N-T+1) < 32` bad scalars,
  complete multiplicity-one Guruswami--Sudan census) are structurally
  faithful to P1.

These are arithmetic facts supporting a landscape no-go, not a geometric
theorem about arbitrary stacks: coincidence-structured (coset) constructions
with cores below `T - 1` are *not* bounded by this ledger and remain the open
content of the residual, which must beat the margin `111848106` to fail.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.FSMGRateQuarterMultiCoreQuotientLedger

/-! ## P1 parameters (matching `_P1RateQuarterCommonFactorArithmetic`) -/

abbrev m : ℕ := 2 ^ 26
abbrev N : ℕ := 16 * m
abbrev K : ℕ := 4 * m
abbrev r : ℕ := (m - 1) / 3
abbrev d : ℕ := (m - 2) / 2

/-- The predecessor agreement threshold `T = 8m + r + d + 2 = 592794966`. -/
abbrev T : ℕ := 8 * m + r + d + 2

theorem T_value : T = 592794966 := by norm_num [T, r, d, m]

theorem N_value : N = 1073741824 := by norm_num [N, m]

/-! ## Quotient budgets for cores of size `T - 1` -/

/-- Cost of one generic `(T-1)`-core in the quotient `F^N / RS_K`. -/
theorem core_cost : (T - 1) - K = 324359509 := by norm_num [T, K, r, d, m]

/-- Two `(T-1)`-cores fit: the quotient budget `N - K` exceeds their cost by
exactly `156587350`. -/
theorem two_core_budget : (N - K) = 2 * ((T - 1) - K) + 156587350 := by
  norm_num [N, K, T, r, d, m]

/-- **Three-core no-go (arithmetic core).**  Three generic `(T-1)`-cores
overrun the quotient budget: `N - K < 3 ((T-1) - K)`.  This is the exact sign
that flips relative to the rate-half predecessor, where the identical
mechanism produced the 2026-07-10 counterexample. -/
theorem three_core_budget_negative : N - K < 3 * ((T - 1) - K) := by
  norm_num [N, K, T, r, d, m]

/-- Rate-half contrast (`n = 64m'`, `k = 32m'`, `t = 33m' + 1`, `m' = 2^24`):
the three-core budget is positive there, `n - k = 3 (t - 1 - k) + 29 m'`. -/
theorem rate_half_three_core_budget_positive :
    (64 * 2 ^ 24 - 32 * 2 ^ 24 : ℕ)
      = 3 * ((33 * 2 ^ 24 + 1 - 1) - 32 * 2 ^ 24) + 29 * 2 ^ 24 := by
  norm_num

/-- Rate-half slot count exceeds the domain (`93 m' > 64 m'`), the refuted
side of the contrast. -/
theorem rate_half_slots_exceed :
    (64 * 2 ^ 24 : ℕ) < 3 * (64 * 2 ^ 24 - (33 * 2 ^ 24 + 1) + 1) := by
  norm_num

/-! ## The generic two-core cap and its exact margin -/

/-- Generic two-core scalar cap: `2 (N - T + 1) = 961893718`. -/
theorem two_core_cap : 2 * (N - T + 1) = 961893718 := by
  norm_num [N, T, r, d, m]

/-- The cap is below the domain size with exact margin `2 (r + d + 1)`:
`N = 2 (N - T + 1) + 2 (r + d + 1)`. -/
theorem two_core_margin : N = 2 * (N - T + 1) + 2 * (r + d + 1) := by
  norm_num [N, T, r, d, m]

theorem margin_value : 2 * (r + d + 1) = 111848106 := by norm_num [r, d, m]

/-! ## The `m = 2` miniature `[N=32, K=8, T=18]` shows the same signs -/

theorem miniature_three_core_budget_negative :
    (32 - 8 : ℕ) < 3 * (17 - 8) := by norm_num

theorem miniature_two_core_budget : (32 - 8 : ℕ) = 2 * (17 - 8) + 6 := by
  norm_num

/-- Miniature two-core cap `30 < 32` with margin `2`, matched exactly by the
complete Guruswami--Sudan census of the probe (30 bad scalars attained over
`F_97` and `F_1153`). -/
theorem miniature_two_core_cap : 2 * (32 - 18 + 1) = 30 ∧ (30 : ℕ) + 2 = 32 := by
  norm_num

/-- Miniature threshold matches the P1 formula at `m = 2`
(`r = d = 0` there): `T = 8*2 + 0 + 0 + 2 = 18`. -/
theorem miniature_threshold : 8 * 2 + (2 - 1) / 3 + (2 - 2) / 2 + 2 = 18 := by
  norm_num

end ArkLib.ProximityGap.Frontier.FSMGRateQuarterMultiCoreQuotientLedger

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.FSMGRateQuarterMultiCoreQuotientLedger

#print axioms T_value
#print axioms core_cost
#print axioms two_core_budget
#print axioms three_core_budget_negative
#print axioms rate_half_three_core_budget_positive
#print axioms rate_half_slots_exceed
#print axioms two_core_cap
#print axioms two_core_margin
#print axioms margin_value
#print axioms miniature_three_core_budget_negative
#print axioms miniature_two_core_budget
#print axioms miniature_two_core_cap
#print axioms miniature_threshold
