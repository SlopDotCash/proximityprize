/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-!
# The Hermite-turnover reduction: prize `⟺` turnover depth `k* = O(log p)` (#444, form (D))

**Lane-2 reduction capstone (CONDITIONAL on the measured Jacobi-matrix model; honest, NOT a closure).**

Form (D) of the number-theorists' problem statement (commit `e1f04a449`,
`docs/kb/deltastar-444-JACOBI-RECURRENCE-TOOL-2026-06-21.md`) restates the wall via the orthogonal-
polynomial recurrence coefficients `b_k` of the empirical `η`-measure:

> `M =` top of the Jacobi matrix of `μ_η` (exact, no `L^{2r}` overshoot); the `b_k` follow the
> Hermite law `b_k² = n·k` until a **turnover depth `k*`**, after which they fall (sub-Hermite,
> bounded support). The spectral edge is realized at the turnover: **`M = √(2 n k*)`**.
> **Wall `⟺` `k* = O(log p)`** (early turnover — long before the trivial support cutoff `k = n/4`).

This file formalizes the **reduction algebra** of form (D): taking the measured edge–turnover
relation `M² = 2 n k*` as an explicit hypothesis (NOT asserted — it is the empirical Jacobi-matrix
model, verified by probe), the prize bound `M ≤ √2·√(n·L)` is *exactly equivalent* to the
turnover-depth bound `k* ≤ L`. So the open content of the prize is concentrated into ONE scalar:
the turnover depth `k*` of the recurrence coefficients, and the prize asks whether it stays `O(log p)`.

## Honesty contract

* The relation `M² = 2 n k*` is the **measured Jacobi-matrix model** (probe
  `scripts/probes/probe_444_jacobi_hermite_turnover.py`: ratio `M/√(2 n k*) = 1.09, 1.09` at
  n=16,32; argmax `b_k` at `k* = 5, 7 ≈ (log p)/2 = 5.5, 6.9`). It is taken here as a **hypothesis**,
  never as a proven fact — the reduction is conditional on it. We do NOT larp it as theorem.
* The reduction is a pure scalar equivalence; it contains **no** cancellation / completion /
  moment-saving / anti-concentration / capacity claim. It does NOT prove `k* = O(log p)` (that IS
  the wall). It only certifies that the prize is *equivalent* to that single bounded-turnover fact.
* CORE (the upper bound) remains OPEN: an unconditional bound on `k*` is exactly the missing input.
-/

namespace ProximityGap.Frontier.HermiteTurnover

open Real

/-- The **edge–turnover model** of form (D): the spectral edge `M` of the `η`-measure's Jacobi
matrix is realized at the turnover depth `k*` of the recurrence coefficients, with
`M² = 2 · n · k*`.  (Empirical Jacobi-matrix model; an explicit hypothesis, not a proven fact.) -/
structure EdgeTurnover (n M kstar : ℝ) : Prop where
  hn : 0 < n
  hM : 0 ≤ M
  hk : 0 ≤ kstar
  /-- The measured edge–turnover relation `M² = 2 n k*`. -/
  rel : M ^ 2 = 2 * n * kstar

/-- **THE REDUCTION (form (D)).**  Under the edge–turnover model, the prize bound
`M ≤ √2 · √(n · L)` holds **iff** the turnover depth is bounded by `L`: `k* ≤ L`.
So the prize `M ≤ √2·√(n log p)` is exactly the statement `k* ≤ log p`. -/
theorem prize_iff_turnover_le {n M kstar L : ℝ} (h : EdgeTurnover n M kstar) (hL : 0 ≤ L) :
    M ≤ Real.sqrt 2 * Real.sqrt (n * L) ↔ kstar ≤ L := by
  have hn := h.hn
  have hM := h.hM
  -- Compare squares (both sides nonnegative).
  have hRHSnonneg : 0 ≤ Real.sqrt 2 * Real.sqrt (n * L) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq hM, ← Real.sqrt_sq hRHSnonneg]
  rw [Real.sqrt_le_sqrt_iff (by positivity)]
  have hsq : (Real.sqrt 2 * Real.sqrt (n * L)) ^ 2 = 2 * (n * L) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
        Real.sq_sqrt (by positivity : (0:ℝ) ≤ n * L)]
  rw [hsq, h.rel]
  constructor
  · intro hle
    -- 2 n k* ≤ 2 n L  ⟹  k* ≤ L  (cancel 2n > 0)
    have h2n : (0:ℝ) < 2 * n := by positivity
    nlinarith [hle, h2n, mul_pos h2n hn]
  · intro hle
    nlinarith [hle, hn]

/-- **Prize ⟹ bounded turnover.**  If the prize bound holds at scale `L`, the turnover depth is
`≤ L`.  (Forward half of the equivalence, packaged for citation.) -/
theorem turnover_le_of_prize {n M kstar L : ℝ} (h : EdgeTurnover n M kstar) (hL : 0 ≤ L)
    (hp : M ≤ Real.sqrt 2 * Real.sqrt (n * L)) : kstar ≤ L :=
  (prize_iff_turnover_le h hL).mp hp

/-- **Bounded turnover ⟹ prize.**  If the turnover depth is `≤ L`, the prize bound holds at scale
`L`.  (Backward half — the *constructive* direction: an `O(log p)` turnover yields the prize.) -/
theorem prize_of_turnover_le {n M kstar L : ℝ} (h : EdgeTurnover n M kstar) (hL : 0 ≤ L)
    (ht : kstar ≤ L) : M ≤ Real.sqrt 2 * Real.sqrt (n * L) :=
  (prize_iff_turnover_le h hL).mpr ht

/-- **The exact turnover at the prize scale.**  Specializing `L = log p`, the prize bound
`M ≤ √2·√(n log p)` is equivalent to `k* ≤ log p`: the wall is the single scalar inequality
`turnover ≤ log p`. -/
theorem prize_iff_turnover_le_logp {n M kstar p : ℝ} (h : EdgeTurnover n M kstar)
    (hp1 : 1 ≤ p) :
    M ≤ Real.sqrt 2 * Real.sqrt (n * Real.log p) ↔ kstar ≤ Real.log p :=
  prize_iff_turnover_le h (Real.log_nonneg hp1)

end ProximityGap.Frontier.HermiteTurnover

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.HermiteTurnover.prize_iff_turnover_le
#print axioms ProximityGap.Frontier.HermiteTurnover.turnover_le_of_prize
#print axioms ProximityGap.Frontier.HermiteTurnover.prize_of_turnover_le
#print axioms ProximityGap.Frontier.HermiteTurnover.prize_iff_turnover_le_logp
