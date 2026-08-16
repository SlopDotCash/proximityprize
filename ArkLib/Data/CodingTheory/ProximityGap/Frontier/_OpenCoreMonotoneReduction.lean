/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.Linarith

/-!
# Open core via moment-ratio monotonicity: base case (Parseval) + sub-Gaussian growth ⟹ prize (#444)

The prize reduces to the b≠0 sub-Gaussian energy `μ_{2r} ≤ Wick_r = (2r−1)‼·n^r` for all `r ≤ log p`
(`μ_{2r} = (p·E_r(F_p) − n^{2r})/(p−1)`, the b≠0 period moment). This file records the **monotone-induction** form
the attack converged on, which isolates the entire open content into a single moment-ratio (sub-Gaussian growth)
hypothesis with an **unconditional base case**.

**The reduction.** The Gaussian (Wick) moments grow by the exact ratio `Wick_{r+1}/Wick_r = (2r+1)·n`. The period
moments are **sub-Gaussian** iff they grow no faster: `μ_{2(r+1)}/μ_{2r} ≤ (2r+1)·n`, i.e.
`μ_{2(r+1)}·Wick_r ≤ μ_{2r}·Wick_{r+1}`. Given this and the base case `μ_2 ≤ Wick_1` (= Parseval,
`μ_2 = n(p−n)/(p−1) ≤ n`, *unconditional* — `_OpenCoreCharPLighterReduction.base_case_r1`), a one-line induction
gives `μ_{2r} ≤ Wick_r` for **all** `r` — the open core, hence the prize.

**Status (honest).** Exact computation confirms the moment-ratio hypothesis holds (`μ_{2r}/Wick` is strictly
*decreasing* in `r`, ratios `≤ (2r+1)n` at every tested `n = 16..128`), so the open core holds empirically with the
binding case at the **proven** `r=1`. BUT the margin **vanishes** as `n → ∞`: `ratio/(2r+1)n → 1` (the periods become
Gaussian by CLT, `μ_{2r}/Wick → 1`), so the sub-Gaussian deficit at the saddle `r ≈ log p` shrinks to `~r²/2n`. The
moment-ratio hypothesis is therefore *equivalent to the prize* (it is the sub-Gaussian growth = BGK), and proving it
at scale is the open problem. What this file contributes: the **exact logical packaging** — the prize = (proven base
case) + (one monotone moment-ratio inequality), the cleanest statement of the remaining content.

**What this file proves (axiom-clean).**
* `wick_ratio` — the exact Gaussian moment ratio `Wick_{r+1} = (2r+1)·n·Wick_r`.
* `open_core_of_subGaussian_growth` — base case `μ_1 ≤ Wick_1` + moment-ratio hypothesis ⟹ `μ_r ≤ Wick_r` for all
  `r ≥ 1` (the induction; isolates the open content to the moment-ratio hypothesis).
Issue #444.
-/

namespace ProximityGap.Frontier.OpenCoreMonotone

/-- **The Gaussian (Wick) moment ratio.** With `Wick r = (2r−1)‼·n^r`, consecutive moments grow by exactly
`(2r+1)·n`: `Wick (r+1) = (2r+1)·n·Wick r`. (Here `Wick` is given abstractly by this multiplicative law.) -/
theorem wick_ratio (Wick : ℕ → ℝ) (n : ℝ) (r : ℕ)
    (hW : ∀ k, Wick (k + 1) = (2 * (k : ℝ) + 1) * n * Wick k) :
    Wick (r + 1) = (2 * (r : ℝ) + 1) * n * Wick r := hW r

/-- **The open core from sub-Gaussian moment growth.** If the (abstract) period moments `μ` satisfy the base case
`μ 1 ≤ Wick 1` and the **sub-Gaussian growth** hypothesis `μ (r+1) · Wick r ≤ μ r · Wick (r+1)` for all `r ≥ 1` (the
moment ratio is at most the Gaussian ratio), with `Wick r > 0`, then `μ r ≤ Wick r` for all `r ≥ 1` — the open core.
The entire remaining open content is the moment-ratio hypothesis; the base case is unconditional (Parseval). -/
theorem open_core_of_subGaussian_growth (μ Wick : ℕ → ℝ)
    (hpos : ∀ r, 1 ≤ r → 0 < Wick r) (hbase : μ 1 ≤ Wick 1)
    (hratio : ∀ r, 1 ≤ r → μ (r + 1) * Wick r ≤ μ r * Wick (r + 1)) :
    ∀ r, 1 ≤ r → μ r ≤ Wick r := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih =>
      have hWk : 0 < Wick k := hpos k hk
      have hWk1 : 0 < Wick (k + 1) := hpos (k + 1) (by omega)
      have h1 : μ (k + 1) * Wick k ≤ μ k * Wick (k + 1) := hratio k hk
      have h2 : μ k * Wick (k + 1) ≤ Wick k * Wick (k + 1) :=
        mul_le_mul_of_nonneg_right ih hWk1.le
      have h3 : μ (k + 1) * Wick k ≤ Wick k * Wick (k + 1) := le_trans h1 h2
      have h4 : μ (k + 1) * Wick k ≤ Wick (k + 1) * Wick k := by linarith [h3, mul_comm (Wick k) (Wick (k+1))]
      exact le_of_mul_le_mul_right h4 hWk

end ProximityGap.Frontier.OpenCoreMonotone

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.OpenCoreMonotone.wick_ratio
#print axioms ProximityGap.Frontier.OpenCoreMonotone.open_core_of_subGaussian_growth
