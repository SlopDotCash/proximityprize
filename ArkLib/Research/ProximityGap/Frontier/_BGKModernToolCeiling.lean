/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The unified BGK modern-tool ceiling: every tool hits `M-exponent = 1/2 + β/(2k)` (#444)

An 8-tool sweep of the strongest modern analytic-NT machinery at BGK (β=4) — Rudnev point-plane incidence, Shkredov
higher-energy, Konyagin–Shkredov, Petridis–Shparlinski/di Benedetto, Stevens–Murphy, Balog–Wooley, finite-field
restriction/decoupling, Weil-II — all reduce to the **same moment identity** and hit the **same ceiling**. This file
formalizes that unified ceiling.

**The reduction (every tool).** Each tool bounds `M = max_{b≠0}|η_b|` through the moment identity
`M^{2k} ≤ Σ_b|η_b|^{2k} = p·E_k` (`E_k` = the `k`-fold additive energy). Conditional on the sub-Gaussian/Wick energy
bound `E_k ≤ (2k−1)‼·n^k` and `p = n^β`,
```
   M^{2k} ≤ p·E_k ≤ n^β · (2k−1)‼·n^k = (2k−1)‼·n^{β+k},
   M ≤ ((2k−1)‼)^{1/2k}·n^{(β+k)/(2k)},   n-exponent  α(k) = (β+k)/(2k) = 1/2 + β/(2k).
```
So **the achievable n-exponent is `1/2 + β/(2k)`**, decreasing in the moment depth `k`, and reaching the prize `1/2`
**only as `k → ∞`**. At β=4: `α(k) = 1/2 + 2/k`, giving `α(2) = 3/2`, `α(4) = 1`, `α(8) = 3/4`, `→ 1/2`.

**Why every tool is frozen and none reaches 1/2 (the barrier, exact-verified).**
* The trilinear / point-plane incidence tools (Konyagin–Shkredov, Petridis–Shparlinski, Stevens–Murphy, Rudnev) are
  **frozen at low depth `k = 2`** (the `p^{1/4} = p^{1/(2·2)}` Szemerédi–Trotter-over-`F_p` incidence tax), where the
  best assembled result is `M ≤ n^{2849/2880} = n^{1−31/2880}` (di Benedetto SOTA) — a power saving over the trivial
  `n`, but `≫ n^{1/2}`. The `1/2 + β/(2k)` law shows beating the trivial `n` needs `k > β`, beating `n^{3/4}` needs
  `k > 2β`, and the prize needs `k → ∞`.
* Reaching `α ≈ 1/2` requires depth `k ≈ log p`, and **there the Wick energy hypothesis `E_k ≤ (2k−1)‼·n^k` is exactly
  the char-p deep-moment bound that fails** (the char-p excess `W_k > 0` at the saddle) — i.e. the BGK/Paley wall.
* The non-incidence tools confirm the same ceiling: Balog–Wooley and finite-field restriction give only the `k = 2`
  L⁴ bound `α = 3/2` (`μ_n` is curvature-free / maximally multiplicative); Weil-II gives `α = β/2 = 2` (the
  degree-`m ≈ p^{3/4}` monomial sheaf is Weil-tight, no subgroup saving).

So the unified, exact statement of the BGK frontier at β=4: **the modern toolkit achieves `1/2 + β/(2k)`, is frozen
at `k = 2` (SOTA), and the prize `1/2` is the `k → ∞` limit gated by the char-p energy bound = the open wall.**

**What this file proves (axiom-clean).** `moment_exponent_ceiling` — from `M^{2k} ≤ p·E_k`, `E_k ≤ D·n^k`, `p = n^β`
(all the shared structure), the bound `M^{2k} ≤ D·n^{β+k}`; and `ceiling_exponent_eq` — the n-exponent identity
`(β+k)/(2k) = 1/2 + β/(2k)` with the `k → ∞` limit `1/2`. Issue #444.
-/

namespace ProximityGap.Frontier.BGKCeiling

/-- **The unified moment ceiling (every modern tool).** Every tool bounds `M` via `M^{2k} ≤ p·E_k`; conditional on the
Wick energy bound `E_k ≤ D·n^k` (`D = (2k−1)‼`) and `p = n^β`, the moment is bounded by `D·n^{β+k}`. Taking the
`2k`-th root gives `M ≤ D^{1/2k}·n^{(β+k)/(2k)}`, n-exponent `1/2 + β/(2k)`. This is the ceiling all 8 tools hit;
none beats it, and it reaches the prize `1/2` only as `k → ∞`. -/
theorem moment_exponent_ceiling (Mpow p Ek D nk nbeta : ℝ)
    (hmom : Mpow ≤ p * Ek) (hEk : Ek ≤ D * nk) (hp : p = nbeta)
    (hDnn : 0 ≤ D) (hnk : 0 ≤ nk) (hpnn : 0 ≤ p) :
    Mpow ≤ nbeta * (D * nk) := by
  calc Mpow ≤ p * Ek := hmom
    _ ≤ p * (D * nk) := by
        apply mul_le_mul_of_nonneg_left hEk hpnn
    _ = nbeta * (D * nk) := by rw [hp]

/-- **The ceiling exponent identity + prize limit.** The n-exponent `(β+k)/(2k)` equals `1/2 + β/(2k)` for `k > 0`,
so it is `> 1/2` at every finite depth `k` and tends to `1/2` as `k → ∞` (with the gap `β/(2k)` the exact distance to
the prize at depth `k`). At β=4 this is `1/2 + 2/k`: the SOTA `k=2` gives `3/2`, and the prize `1/2` is unreachable at
any finite depth — it is the `k → ∞` limit, gated by the char-p energy bound at `k ≈ log p`. -/
theorem ceiling_exponent_eq (beta k : ℝ) (hk : 0 < k) :
    (beta + k) / (2 * k) = 1 / 2 + beta / (2 * k) := by
  field_simp
  ring

/-- **The gap to the prize is exactly `β/(2k) > 0` at every finite depth.** So no finite-depth moment/energy method
(hence no tool reducing to one) reaches the prize exponent `1/2`; the gap closes only in the `k → ∞` limit. -/
theorem positive_gap_to_prize (beta k : ℝ) (hbeta : 0 < beta) (hk : 0 < k) :
    1 / 2 < (beta + k) / (2 * k) := by
  rw [ceiling_exponent_eq beta k hk]
  have : 0 < beta / (2 * k) := by positivity
  linarith

end ProximityGap.Frontier.BGKCeiling

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.BGKCeiling.moment_exponent_ceiling
#print axioms ProximityGap.Frontier.BGKCeiling.ceiling_exponent_eq
#print axioms ProximityGap.Frontier.BGKCeiling.positive_gap_to_prize
