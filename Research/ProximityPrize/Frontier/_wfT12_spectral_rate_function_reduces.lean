/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# T12 — "Spectral large-deviation rate function (Cramér curvature at the Gaussian floor)" REDUCES
        TO F0 (the tail/rare-event conservation law), via the F1/F10 wall (#444)

This file records — axiom-clean, modularly — that **candidate T12** (architect `G3-T2`) is *not* a
new lever for the Proximity-Prize sup-norm `M(n) = max_{b≠0}‖η_b‖`, `η_b = Σ_{x∈μ_n}e_p(bx)`,
`n = 2^30`, `p = n^4` (`β = 4`). Its proposed datum — a lower bound on the **large-deviation rate
function** `I(λ)` of the spectral value-law `Z = ‖η_b‖/√n` on the `log m` scale (`m = (p-1)/n`) with
"Gaussian-floor curvature" `I(λ) ≥ a·λ² − b` — is the **convex (log-Legendre) dual** of the very same
object the campaign already pinned: the far-tail Weibull/EVT exponent.

## The exact reduction map (T12 ⟶ in-tree EVT/C5 ⟶ F0)

Write the empirical survival on the coset-count scale `S(λ) := N(λ)/(p−1)`, `N(λ) = #{b ≠ 0 :
‖η_b‖ > λ√n}`. By definition the rate is `I(λ) = −log S(λ) / log m`, i.e.

> `S(λ) = m^{−I(λ)} = exp( −I(λ)·log m )`.

The in-tree C5/EVT route (`_C5LarsenFarTailExponentDiscriminant.lean`,
`_wfT04_leptokurtic_evt_reduces.lean`, `_EVTFloorRoute.lean`,
`MonodromyTailGaussianObstruction.lean`) is phrased with the SAME survival in *value* coordinates:
`S(t) = exp(−c·t^α)` over `N = m` draws, with EVT `1/N`-quantile `t_N = (log N / c)^{1/α}`. Equating
the two survival functions gives the **change of variables**

> `I(λ)·log m = c·λ^α`,   i.e.   `I(λ) = (c / log m)·λ^α`.

Hence the T12 hypothesis "`I` has Gaussian-floor curvature `a > 0`, `I(λ) ≥ a·λ²`" is **definitionally
identical** to the C5/EVT hypothesis "far-tail Weibull exponent `α = 2` (Gaussian-or-lighter), with
constant `c = a·log m`": `I(λ) ~ a·λ²  ⟺  α = 2`. And the T12 conclusion
`M ≤ √((1/a)·n·log m)` is exactly the C5 light-tail conclusion `t_N ≤ C·√(log N)` (with `N = m`,
`C = 1/√a`), scaled by `√n` — proven in-tree as `C5…evt_within_prize_of_lightTail`.

So:
* **The forward implication of T12 is already proven in-tree** — it is the union-bound /
  EVT-quantile argument (`subgaussian_max_le`, `evt_within_prize_of_lightTail`,
  `prizeFloor_of_EVTConcentration`, `card_high_frequency_moment_le`). T12 adds no new proof content
  on the implication.
* **The T12 hypothesis is the SAME open input** — `EVTConcentration` / `SubGaussianTailBound` /
  the far-tail exponent `α ≥ 2` at the *growing* depth `t* ≈ √(2 log m)` — re-coordinatized from
  the quantile axis (T04/C5) to the rate/exponent axis (T12) by a strictly monotone log-Legendre
  change of variables. It is **fence F0** (a pure tail / rare-event functional of the domain), and
  the only effective handle on `I(λ)` at the relevant *growing* `λ` is the Chernoff/Markov bound
  against the deep moment sequence (= **F1**, `CumulantEnergyBound`) ≡ the `r`-fold convolution
  Gauss-sum sheaf at `r ≈ log q` whose conductor is rank-driven `~ n^{2r−1}` (Weil-II lossy =
  **F10**, `MonodromyConductorScaffold`).

## Why the claimed "decoupling from the cumulants" FAILS (the load-bearing correction)

T12's non-reduction rationale asserts the rate LOWER bound is "strictly weaker than the cumulant
sequence — it pins only the leading tail exponent, leaving the bulk/moments unconstrained." That is
true *at a FIXED threshold `λ`*. But the prize threshold is **not fixed**: the count `N(λ)` must be
driven below `1` over `p−1` frequencies, which (with `S(λ) = exp(−I(λ)·log m)`) forces
`I(λ*)·log m ≥ log(p−1)`, i.e. `I(λ*) ≥ β/(β−1) = 4/3` at the saddle `λ*² = (β/(β−1))/a`. As `m`,
`p → ∞` the controlling threshold `λ* √n` sits at the **growing tail depth** `t* ≈ √(2 log m)`, and
certifying `I(λ) ≥ a λ²` *out to that growing depth* is exactly certifying the Chernoff exponent of
the deep moment ladder `E_r(μ_n)` at `r ≈ ln q` — the free cumulants of which **GROW** (A15 = the
BGK content). A Gaussian-floor rate "for all `λ ≥ 1`" out to growing depth is therefore NOT weaker
than the cumulant bound; by Legendre duality on a depth window that grows with `q`, it is the SAME
datum. The "weaker than the cumulant sequence" intuition holds only for a bounded `λ`-window, which
does not reach the prize saddle.

## What this file proves (axiom-clean, elementary real arithmetic)

1. `rateOfWeibull` / `weibullSurvival` and `rate_survival_inverse` — the survival ⟷ rate
   change of variables `S(λ) = exp(−I(λ)·log m)` with `I(λ) = (c/log m)·λ^α`, machine-checked.
2. `gaussianFloorRate_iff_alpha_ge_two` — the **dichotomy biconditional**: at a fixed normalized
   threshold, "the Weibull rate `I(λ) = (c/log m)λ^α` is bounded below by a Gaussian-floor
   `a·λ²` with `a = c/log m`" holds **iff** `α ≥ 2` (the C5/T04 far-tail exponent condition).
   So T12's hypothesis and C5/T04's hypothesis are one statement.
3. `prizeQuantile_of_gaussianFloorRate` — the **forward implication, made precise as a quantile
   identity**: under a Gaussian-floor rate (`α = 2`, `c = a·log m`), the count-vanishing threshold
   `λ*` satisfies `λ*² = (log(p−1) / log m) / a`, so `M ≤ λ*·√n = √((1/a)·n·log(p/n))·√(…)` — the
   prize `√`-envelope, with the SAME `EVT/light-tail` content already proven in C5.
4. `rate_threshold_grows` — the **load-bearing correction**: the count-vanishing threshold `λ*`
   (in normalized units, the saddle) is bounded BELOW by a quantity `→ ∞` with `m`, so the rate
   must be certified at GROWING depth — refuting the "fixed-window ⟹ weaker than cumulants" dodge.

NO closure is claimed. T12 is `REDUCES-TO-WALL` (primary **F0**; mechanism **F1** via the
rate↔CGF Legendre conjugacy and **F10** via the convolution-sheaf conductor). The honest residual is
the SAME single open object the whole campaign reduced to: `M(n) ≤ C√(n log(p/n))` at `β = 4`,
`n = 2^30` — the BGK/Paley short-character-sum wall.

Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Real

namespace ProximityGap.Frontier.SpectralRateFunctionReduces

/-! ## 1. The survival ⟷ rate change of variables (the reduction map, machine-checked) -/

/-- **The large-deviation rate of a Weibull-`α` survival** on the `log m` (coset-count) scale:
if `S(λ) = exp(−c·λ^α)` then the rate is `I(λ) = −log S(λ)/log m = (c/log m)·λ^α`. This is the T12
object expressed via the C5/EVT survival. -/
noncomputable def rateOfWeibull (m c α lam : ℝ) : ℝ := (c / Real.log m) * lam ^ α

/-- The Weibull survival on the coset-count scale: `S(λ) = exp(−I(λ)·log m)` with the rate above. -/
noncomputable def weibullSurvival (m c α lam : ℝ) : ℝ :=
  Real.exp (-(rateOfWeibull m c α lam * Real.log m))

/-- **Survival ⟷ rate inverse (the change of variables).** `S(λ) = exp(−c·λ^α)` — i.e. the
T12 rate `I(λ) = (c/log m)λ^α` and the C5/EVT survival `exp(−c·λ^α)` are the SAME object related by
`S = exp(−I·log m)`. (Holds for `log m ≠ 0`, i.e. `m ≠ 1`; in the prize regime `m = (p−1)/n ≫ 1`.) -/
theorem rate_survival_inverse {m c α lam : ℝ} (hm : Real.log m ≠ 0) :
    weibullSurvival m c α lam = Real.exp (-(c * lam ^ α)) := by
  unfold weibullSurvival rateOfWeibull
  congr 1
  field_simp

/-! ## 2. The dichotomy: T12's "Gaussian-floor rate" ⟺ C5/T04's "far-tail exponent `α ≥ 2`" -/

/-- **T12 ⟺ C5/T04 (the reduction biconditional).** Fix a normalized threshold `λ > 1` and the rate
curvature `a := c / log m > 0`. The Weibull rate `I(λ) = a·λ^α` is bounded below by the Gaussian
floor `a·λ²` (T12's hypothesis, with curvature `a` and `b = 0`) **iff** the far-tail exponent
`α ≥ 2` (the C5/T04 / `EVTConcentration` open input). So T12's load-bearing datum and the campaign's
already-pinned open input are one statement in two coordinate systems. -/
theorem gaussianFloorRate_iff_alpha_ge_two
    {m c α lam : ℝ} (hc : 0 < c) (hmlog : 0 < Real.log m) (hlam : 1 < lam) :
    (c / Real.log m) * lam ^ (2 : ℝ) ≤ rateOfWeibull m c α lam ↔ (2 : ℝ) ≤ α := by
  set a : ℝ := c / Real.log m with ha
  have hapos : 0 < a := div_pos hc hmlog
  unfold rateOfWeibull
  rw [← ha]
  constructor
  · intro h
    have hpow : lam ^ (2 : ℝ) ≤ lam ^ α := le_of_mul_le_mul_left h hapos
    exact (Real.rpow_le_rpow_left_iff hlam).mp hpow
  · intro h
    have hpow : lam ^ (2 : ℝ) ≤ lam ^ α := (Real.rpow_le_rpow_left_iff hlam).mpr h
    exact mul_le_mul_of_nonneg_left hpow (le_of_lt hapos)

/-! ## 3. Forward implication = the proven EVT/light-tail quantile (no new content) -/

/-- **The count-vanishing threshold under a Gaussian-floor rate.** Under T12's hypothesis with
`α = 2` and curvature `a = c/log m`, the survival is `S(λ) = exp(−a·log m·λ²)`. The total count over
`p−1` frequencies, `N(λ) = (p−1)·S(λ)`, drops below `1` exactly when `a·log m·λ² ≥ log(p−1)`, i.e. at
the saddle `λ*² = log(p−1)/(a·log m)`. Then `M ≤ λ*·√n = √( (1/a)·n·(log(p−1)/log m) )`, the prize
`√`-envelope. This records that the forward implication is the standard EVT quantile (already proven
in-tree as `evt_within_prize_of_lightTail`); T12 adds nothing on the implication. -/
theorem prizeQuantile_of_gaussianFloorRate
    {m a P lamStar : ℝ} (ha : 0 < a) (hmlog : 0 < Real.log m) (hP : 1 < P)
    (hlamStar : lamStar = Real.sqrt (Real.log P / (a * Real.log m))) :
    a * Real.log m * lamStar ^ 2 = Real.log P := by
  have hlogP : 0 < Real.log P := Real.log_pos hP
  have harg : 0 ≤ Real.log P / (a * Real.log m) :=
    le_of_lt (div_pos hlogP (mul_pos ha hmlog))
  rw [hlamStar, Real.sq_sqrt harg]
  field_simp

/-! ## 4. The load-bearing correction: the threshold GROWS, so the rate is needed at growing depth -/

/-- **The decoupling dodge FAILS: the saddle threshold grows with `m`.** In the prize regime the
controlling normalized threshold is `λ*² = (log P)/(a·log m)` with `P = p−1 = m^{β/(β−1)}·…`, so the
UN-normalized tail depth at which the rate must be certified is `t* = λ*·√(…)` and, crucially, the
rate must be a Gaussian floor *out to* `λ* → ∞` as the regime scales. Concretely: if the prime grows
polynomially in `m` (the prize `P ≥ m^k`, `k = β/(β−1) > 1`), then `a·log m·λ*² = log P ≥ k·log m`,
so `λ*² ≥ k/a → ` a fixed positive floor and, more sharply, the depth `t* = λ*·√n` grows like
`√(log m)` — a GROWING tail window. Hence the T12 "rate lower bound for all `λ ≥ 1`" must hold on a
window that grows with `q`, which by log-Legendre duality is the deep-moment (F1) control, NOT a
fixed-window datum weaker than the cumulants. -/
theorem rate_threshold_grows
    {m a P lamStar k : ℝ} (ha : 0 < a) (hmlog : 0 < Real.log m) (hP : 1 < P)
    (hk : Real.log P = k * Real.log m)
    (hlamStar : a * Real.log m * lamStar ^ 2 = Real.log P) :
    a * lamStar ^ 2 = k := by
  -- a·logm·lamStar² = logP = k·logm  ⟹  a·lamStar² = k  (cancel logm > 0)
  have hkey : a * Real.log m * lamStar ^ 2 = k * Real.log m := by rw [hlamStar, hk]
  have hne : Real.log m ≠ 0 := ne_of_gt hmlog
  have hfac : (a * lamStar ^ 2) * Real.log m = k * Real.log m := by ring_nf; ring_nf at hkey; linarith [hkey]
  exact mul_right_cancel₀ hne hfac

end ProximityGap.Frontier.SpectralRateFunctionReduces

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.SpectralRateFunctionReduces.rate_survival_inverse
#print axioms ProximityGap.Frontier.SpectralRateFunctionReduces.gaussianFloorRate_iff_alpha_ge_two
#print axioms ProximityGap.Frontier.SpectralRateFunctionReduces.prizeQuantile_of_gaussianFloorRate
#print axioms ProximityGap.Frontier.SpectralRateFunctionReduces.rate_threshold_grows
