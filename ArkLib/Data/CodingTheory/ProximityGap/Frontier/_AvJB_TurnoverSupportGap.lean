/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvJB_JacobiEdgeBoundedSupportCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvJB_HermiteTurnoverReduction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-!
# The early-turnover GAP: free turnover depth is `O(n)`, the prize needs `O(log p)` (#444, form (D))

**Lane-2 bridge brick (connects the two PROVEN Jacobi modules; honest gap, NOT a closure).**

This file bridges the two unconditional/conditional facts of Shaw's new Jacobi tool already in-tree:

* `_AvJB_JacobiEdgeBoundedSupportCeiling` — the char-`p` Jacobi spectral edge is bounded by the
  support radius: `M ≤ 3S` (with `S = n`, `M ≤ 3n`), and `3S` is support-trivial.
* `_AvJB_HermiteTurnoverReduction` — under the edge–turnover model `M² = 2 n k*`, the prize bound
  `M ≤ √2·√(n L)` is exactly equivalent to `k* ≤ L`.

Combining them yields, **unconditionally on the support side** (given only the edge–turnover model),
a *free* upper bound on the turnover depth:

> `2 n k* = M² ≤ (3n)² = 9 n²  ⟹  k* ≤ (9/2)·n`.

So the recurrence-coefficient turnover always happens by depth `k* ≤ (9/2)n` — an `O(n)` bound,
free from any deep arithmetic.  The prize asks for the *far stronger* **early turnover**
`k* ≤ log p`.  Whenever `log p < (9/2)n` (the prize regime `q ≈ n^β`, `β = O(1)`, so
`log p = O(log n) ≪ n`), the prize target is strictly below the free ceiling — there is a genuine
`O(n) → O(log p)` gap that the support bound cannot close.  This file certifies that gap, kernel-checked.

## Honesty contract

The free ceiling `k* ≤ (9/2)n` is the *trivial* turnover bound (it only uses `M ≤ 3n`, i.e. the
support radius).  It does NOT approach the prize target `k* ≤ log p`; the missing input is exactly
the fine sub-Gaussian decay of the `b_k` (the early turnover) = the wall.  No CORE/cancellation/
completion/moment-saving/anti-concentration/capacity claim.  CORE remains OPEN.
-/

namespace ProximityGap.Frontier.HermiteTurnover

open Real
open ProximityGap.Frontier.JacobiBounded

/-- **The free `O(n)` turnover ceiling.**  Under the edge–turnover model `M² = 2 n k*` and the
support bound `M ≤ 3n` (the char-`p` Jacobi support radius `S = n`), the turnover depth satisfies
`k* ≤ (9/2)·n`.  Unconditional on the support side; the only model input is the edge–turnover
relation. -/
theorem turnover_le_free_ceiling {n M kstar : ℝ} (h : EdgeTurnover n M kstar)
    (hMle : M ≤ 3 * n) : kstar ≤ (9 / 2) * n := by
  have hn := h.hn
  have hM := h.hM
  -- M² = 2 n k*  and  0 ≤ M ≤ 3n  ⟹  2 n k* ≤ 9 n²  ⟹  k* ≤ (9/2) n
  have hsq : M ^ 2 ≤ (3 * n) ^ 2 := by
    have h0 : 0 ≤ 3 * n := by positivity
    nlinarith [hM, hMle, h0]
  rw [h.rel] at hsq
  -- 2 n k* ≤ 9 n²  with n > 0  ⟹  k* ≤ (9/2) n
  nlinarith [hsq, hn, mul_pos hn hn]

/-- **The gap as a witness of insufficiency.**  Under the model, the free ceiling gives `k* ≤ (9/2)n`,
but this does NOT certify the prize unless additionally `(9/2)n ≤ log p`.  Since in the prize regime
`log p ≪ n`, the free ceiling is *never* good enough: the prize requires an independent early-turnover
input.  Stated as: if the free ceiling were tight (`k* = (9/2)n`) and `log p < (9/2)n`, the prize
FAILS at scale `L = log p`. -/
theorem free_ceiling_insufficient_for_prize {n M kstar : ℝ} (h : EdgeTurnover n M kstar)
    (htight : (9 / 2) * n ≤ kstar) {L : ℝ} (hLnn : 0 ≤ L) (hLgap : L < (9 / 2) * n) :
    ¬ (M ≤ Real.sqrt 2 * Real.sqrt (n * L)) := by
  intro hp
  have hk : kstar ≤ L := turnover_le_of_prize h hLnn hp
  -- (9/2)n ≤ k* ≤ L < (9/2)n  : contradiction
  exact absurd (lt_of_le_of_lt (le_trans htight hk) hLgap) (lt_irrefl _)

end ProximityGap.Frontier.HermiteTurnover

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.HermiteTurnover.turnover_le_free_ceiling
#print axioms ProximityGap.Frontier.HermiteTurnover.free_ceiling_insufficient_for_prize
