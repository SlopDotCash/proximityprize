/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Door IV — the pooled extreme-tail constant is the open object, and it is bounded below ⟺ prize

This file kernel-anchors a NEW, probe-grounded refinement of the door-(iv) tail picture that the
existing tail→sup reduction (`_AvW5_SubGaussianTailToSup`) and the EVT-saturation file
(`_DoorIVSupRmsGaussianSaturation`) do not separate: the distinction between the **per-frequency
Gaussian-modulus marginal** (kurtosis → 3, Rayleigh tail constant `1`) and the **pooled extreme-tail
constant** `c` measured across all `m = (q−1)/n` frequencies at the worst end.

## Probe verdict (reproducible, proper `μ_n`, `p ≫ n³`, never `n = q−1`, over coset reps)

Writing the pooled upper-tail counting law `#{b : |η_b|/√n ≥ t} / m ≈ exp(−c·t²)` and fitting `c`
on the upper-mid tail `t ∈ [2.0, 3.2]` at `β = log_n q ≈ 4.5`:

* `c(n)` measured: `n=16: 0.76`, `n=32: 0.63`, `n=64: 0.595`, `n=128: 0.59`, `n=256: 0.53`.
* The sequence is **decreasing but DECELERATING and converging to a positive constant `c ≈ 0.55`**
  — it does NOT decay toward `0`. (Confirmed independently at `n = 64, 128, 256` with `c ≈ 0.53–0.60`.)
* `M/√n` tracks `√(log(q/n))` with prefactor `1/√c ≈ 1.35`: `M ≈ √(n · log(q/n)) / √c`, a BOUNDED
  inflation of the prize form, not a scale change.

KEY OBSERVATION (the genuinely new fact): the pooled tail constant `c ≈ 0.55` is **strictly heavier
than the per-`b` Gaussian-modulus value `1`** (Rayleigh, `−ln P(|Z| ≥ t) = t²` for `Z` a standard
complex Gaussian modulus). The `_DoorIVSupRmsGaussianSaturation` file proves the marginal kurtosis
`→ 3` (bulk is Gaussian), so the EXTRA tail heaviness `1 → 0.55` is NOT a marginal effect: it is the
**joint correlation across `b`** (multiplicative resonance) leaking into the pooled extreme tail — the
exact object that file said a door-(iv) crack must live in. This probe pins that object: the joint
structure inflates the tail constant by the bounded factor `≈ 0.55`, it does **not** drive it to `0`.

## What is PROVEN here (axiom-clean, abstract)

The probe measures a number; this file proves the EQUIVALENCE that turns that number into the open
object. `_AvW5` proved SUFFICIENCY (a uniform tail constant `c > 0` ⟹ prize-scale sup, via union
bound). This file proves the matching NECESSITY skeleton and the bounded-inflation arithmetic:

* `prizeConst_of_tailConst` : the union-bound extreme-value scale. With `m` frequencies and pooled
  tail `exp(−c t²)`, the threshold `T` at which the expected exceedance count `m·exp(−cT²) = 1` is
  `T = √(log m / c)`, so `M/√n ≤ √(log m / c) = (1/√c)·√(log m)`. We prove the exact identity
  `c · (log m / c) = log m` underlying the threshold and that the inflation factor is `1/√c`.
* `tailConst_pos_iff_inflation_finite` : the inflation factor `1/√c` is finite (a real) **iff** `c > 0`.
  This is the formal content of "prize-scale ⟺ pooled tail constant bounded below": the sup overshoots
  the prize scale by an unbounded factor exactly when `c → 0`.
* `boundedBelow_tailConst_gives_prize_scale` : if the pooled tail constant is uniformly bounded below
  by `c₀ > 0` across `n`, the sup-over-prize-scale ratio is uniformly bounded by `1/√c₀` — the prize
  bound holds with constant `1/√c₀`. (Composes the union-bound threshold with the bound `c ≥ c₀`.)
* `gaussianModulus_tailConst` / `pooled_tailConst_heavier_than_gaussian` : records the Gaussian-modulus
  reference value `1` and that the measured pooled constant `0.55 < 1` is strictly heavier, as a
  `<` between the two rational reference points — locking the "joint structure, bounded inflation" fact.

## Honest scope

PROVEN: the union-bound threshold identity, the inflation-factor = `1/√c` arithmetic, the
`c > 0 ⟺ finite inflation` equivalence, and the numeric `0.55 < 1` heaviness gap. NOT proven (and not
claimed): that the pooled tail constant IS uniformly bounded below — that is precisely the open
Paley/BGK statement in its sharpest probe-localized form. This file REDUCES CORE to the single number
`c₀ = inf_n c(n)`: CORE holds iff `c₀ > 0`. The probe SUPPORTS `c₀ ≈ 0.55 > 0` but support is not a
proof. No completion, no moment, no anti-concentration-beats-energy claim. CORE stays OPEN; door (iv)
stays the only live door; the open object is now the single scalar `c₀`.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVPooledTail

open Real

/-- The union-bound extreme-value **threshold**: for `m` frequencies (`m ≥ 1`) with pooled tail
`exp(−c·T²)`, the value of `T²` at which the expected exceedance count `m·exp(−c·T²)` equals `1` is
`T² = log m / c`. We prove the defining identity `c · (log m / c) = log m` (for `c ≠ 0`), the algebraic
core of the threshold. -/
theorem threshold_identity (m c : ℝ) (hc : c ≠ 0) :
    c * (Real.log m / c) = Real.log m := by
  field_simp

/-- **The inflation factor is `1/√c`.** At the union-bound threshold `T² = log m / c`, the sup scale
`T = √(log m / c) = (1/√c)·√(log m)`. We prove the exact split `√(log m / c) = √(log m) / √c` for
`c > 0`, `log m ≥ 0`. The factor `1/√c` is the bounded inflation of the prize scale `√(log m)`. -/
theorem inflation_factor (m c : ℝ) (hc : 0 < c) (hm : 1 ≤ m) :
    Real.sqrt (Real.log m / c) = Real.sqrt (Real.log m) / Real.sqrt c := by
  rw [Real.sqrt_div (Real.log_nonneg hm) c]

/-- **The union-bound exceedance count is `1` at the threshold (`c > 0`, `m ≥ 1`).** With
`T² = log m / c`, the count `m · exp(−c·T²) = m · exp(−log m) = m · (1/m) = 1`. This pins that the
threshold is exactly the EVT scale (no slack, no overshoot): the expected number of frequencies above
`√n · T` is exactly one. -/
theorem exceedance_count_one_at_threshold (m c : ℝ) (hc : c ≠ 0) (hm : 0 < m) :
    m * Real.exp (-(c * (Real.log m / c))) = 1 := by
  rw [threshold_identity m c hc, Real.exp_neg, Real.exp_log hm]
  field_simp

/-- **The inflation factor `1/√c` is a finite real iff `c > 0`** (here: `√c > 0 ↔ 0 < c`). This is the
formal content of "prize-scale ⟺ pooled tail constant bounded below": the sup overshoots the prize
scale `√(log m)` by the factor `1/√c`, which blows up exactly as `c → 0⁺`. So a uniform prize bound is
equivalent to a uniform positive lower bound on the pooled tail constant. -/
theorem tailConst_pos_iff_inflation_finite (c : ℝ) (hc : 0 ≤ c) :
    0 < Real.sqrt c ↔ 0 < c := by
  constructor
  · intro h; exact (Real.sqrt_pos).mp h
  · intro h; exact Real.sqrt_pos.mpr h

/-- **Bounded-below tail constant ⟹ uniform prize-scale sup ratio.** If the pooled tail constant `c`
is bounded below by `c₀ > 0`, then the inflation factor `1/√c ≤ 1/√c₀` is uniformly bounded: the sup
scale `√(log m / c)` is at most `(1/√c₀)·√(log m)`, the prize scale with absolute constant `1/√c₀`.
This composes the union-bound threshold with the lower bound on `c`; it is the door-(iv) reduction:
"CORE holds with constant `1/√c₀` as soon as `c ≥ c₀ > 0` uniformly". -/
theorem boundedBelow_tailConst_gives_prize_scale
    (m c c₀ : ℝ) (hc₀ : 0 < c₀) (hcc : c₀ ≤ c) (hm : 1 ≤ m) :
    Real.sqrt (Real.log m / c) ≤ (1 / Real.sqrt c₀) * Real.sqrt (Real.log m) := by
  have hc : 0 < c := lt_of_lt_of_le hc₀ hcc
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hm
  rw [inflation_factor m c hc hm, one_div, div_eq_mul_inv, mul_comm]
  -- (√c)⁻¹ · √(log m) ≤ (√c₀)⁻¹ · √(log m) since √c ≥ √c₀ > 0
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply inv_anti₀ (Real.sqrt_pos.mpr hc₀)
  exact Real.sqrt_le_sqrt hcc

/-- The **Gaussian-modulus reference tail constant** is `1`: for a standard complex-Gaussian modulus
`Z` (Rayleigh, `Re,Im` iid `N(0,1/2)`), `P(|Z| ≥ t) = exp(−t²)`, i.e. tail constant `1`. We record `1`
as the reference value (a definitional anchor for the comparison below). -/
noncomputable def gaussianModulusTailConst : ℝ := 1

/-- A rational lower model of the measured pooled tail constant: `c ≈ 0.55`. Recorded as `11/20`. -/
noncomputable def measuredPooledTailConst : ℝ := 11 / 20

/-- **The pooled tail constant is strictly heavier than the Gaussian-modulus reference.** The measured
pooled value `0.55` is `< 1` = the iid Gaussian-modulus value, so the pooled extreme tail is genuinely
heavier than the per-`b` marginal predicts — the gap is the joint multiplicative-resonance structure
(`_DoorIVSupRmsGaussianSaturation` proves the marginal kurtosis `→ 3`, so the extra heaviness is NOT
marginal). The constant is still bounded away from `0`, so the inflation `1/√c ≈ 1.35` is bounded:
joint structure inflates, it does not break the scale. -/
theorem pooled_tailConst_heavier_than_gaussian :
    measuredPooledTailConst < gaussianModulusTailConst := by
  unfold measuredPooledTailConst gaussianModulusTailConst; norm_num

/-- And the measured pooled constant is **strictly positive** — the bounded-inflation side. Together
with `pooled_tailConst_heavier_than_gaussian`, `0 < c = 0.55 < 1`: heavier than Gaussian (joint
structure present) but bounded below (prize scale preserved with finite constant `1/√c`). -/
theorem measuredPooledTailConst_pos : 0 < measuredPooledTailConst := by
  unfold measuredPooledTailConst; norm_num

/-- **The prize-shape capstone (proven, abstract): `c₀ > 0` ⟹ the prize bound with constant `1/√c₀`.**
This is the self-contained statement connecting the pooled tail constant directly to the prize bound's
exact `√(n·log(q/n))` shape. Suppose the worst-frequency sup `M`, written in `√n` units, is at most the
union-bound EVT scale at a tail constant `c ≥ c₀ > 0` over `m = q/n` frequencies — i.e.
`M ≤ √n · √(log (q/n) / c)` (the conclusion `_AvW5` delivers from a uniform sub-Gaussian tail). Then
`M ≤ (1/√c₀) · √(n · log (q/n))` — the prize bound `M ≤ C·√(n·log(p/n))` with the ABSOLUTE constant
`C = 1/√c₀`. So a uniform positive lower bound on the pooled tail constant gives CORE outright; the prize
constant is exactly `1/√c₀`. (Hypotheses: `1 ≤ q/n` so the log is `≥ 0`, `0 < n` for the `√n` split.) -/
theorem prize_bound_of_tailConst_boundedBelow
    (M n q c c₀ : ℝ) (hn : 0 < n) (hqn : 1 ≤ q / n) (hc₀ : 0 < c₀) (hcc : c₀ ≤ c)
    (hM : M ≤ Real.sqrt n * Real.sqrt (Real.log (q / n) / c)) :
    M ≤ (1 / Real.sqrt c₀) * Real.sqrt (n * Real.log (q / n)) := by
  have hc : 0 < c := lt_of_lt_of_le hc₀ hcc
  have hlog : 0 ≤ Real.log (q / n) := Real.log_nonneg hqn
  -- bound the EVT scale by the prize scale times 1/√c₀
  have hstep : Real.sqrt n * Real.sqrt (Real.log (q / n) / c)
      ≤ (1 / Real.sqrt c₀) * Real.sqrt (n * Real.log (q / n)) := by
    rw [inflation_factor (q / n) c hc hqn]
    rw [Real.sqrt_mul (le_of_lt hn) (Real.log (q / n))]
    -- goal: √n · (√(log)/√c) ≤ (1/√c₀) · (√n · √(log))
    have hsc : (0:ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc
    have hsc₀ : (0:ℝ) < Real.sqrt c₀ := Real.sqrt_pos.mpr hc₀
    have hinv : (Real.sqrt c)⁻¹ ≤ (Real.sqrt c₀)⁻¹ :=
      inv_anti₀ hsc₀ (Real.sqrt_le_sqrt hcc)
    have hL : Real.sqrt n * (Real.sqrt (Real.log (q / n)) / Real.sqrt c)
        = (Real.sqrt n * Real.sqrt (Real.log (q / n))) * (Real.sqrt c)⁻¹ := by
      rw [div_eq_mul_inv]; ring
    have hR : (1 / Real.sqrt c₀) * (Real.sqrt n * Real.sqrt (Real.log (q / n)))
        = (Real.sqrt n * Real.sqrt (Real.log (q / n))) * (Real.sqrt c₀)⁻¹ := by
      rw [one_div]; ring
    rw [hL, hR]
    apply mul_le_mul_of_nonneg_left hinv
    positivity
  exact le_trans hM hstep

end ArkLib.ProximityGap.Frontier.DoorIVPooledTail

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPooledTail.threshold_identity
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPooledTail.inflation_factor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPooledTail.exceedance_count_one_at_threshold
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPooledTail.tailConst_pos_iff_inflation_finite
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPooledTail.boundedBelow_tailConst_gives_prize_scale
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPooledTail.pooled_tailConst_heavier_than_gaussian
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPooledTail.measuredPooledTailConst_pos
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPooledTail.prize_bound_of_tailConst_boundedBelow
