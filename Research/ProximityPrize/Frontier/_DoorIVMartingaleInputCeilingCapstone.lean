/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier._DoorIVQVCauchySchwarzCircular

/-!
# Door-(iv) Lane-3 capstone: three deterministic tower envelopes give only the trivial drift (#444)

**Scope.** This file is entirely **deterministic**. It works with a positive real sequence `Mtow`
satisfying `Mtow (i+1) ≤ 2·Mtow i` (and, for the quadratic route, the extra monotonicity
hypothesis `Mtow i ≤ Mtow (i+1)`), and the log-ratio tower
`S_a := log(Mtow a) − log(Mtow 0) = Σ_{i<a} Δ_i`. It defines no probability space, filtration,
martingale differences or conditional expectations, so it proves no concentration (Azuma/Freedman)
statement and no theorem about all martingale methods. The monotonicity hypothesis
(`Δ_i ≥ 0`) is an entered assumption, not a property of the actual worst-period tower maxima
(whose per-level ratios are reported to drop below `1` in the butterfly data); any use of it needs
its own justification for the actual model.

Three deterministic envelopes have been formalized:

1. the **bounded-increment sum** `S_a ≤ a·log 2`  (`logTower_le_card_mul_log2`);
2. the **centered-excess** linear ceiling `Σ_{i<a}(Δ_i − ½log 2) ≤ (a/2)·log 2`
   (`logTower_excess_le_half_card_mul_log2`), which is the same `S_a ≤ a·log 2`;
3. the **raw sum of squared increments** `Σ Δ_i² ≤ (log 2)·S_a` (`logTower_sq_le_log2_mul`), which
   through Cauchy–Schwarz returns `S_a ≤ a·log 2` (`qv_route_recovers_trivial_ceiling`). This raw
   deterministic sum is **not** the predictable quadratic variation of a martingale, which would
   be built from conditional second moments of *centered* random differences; no such bridge is
   formalized here.

**This file records that these three envelopes all give the same ceiling `S_a ≤ a·log 2`** — the
trivial drift ceiling (`Mtow a ≤ 2^a·Mtow 0`, the trivial `n`-ceiling). The prize shape is
`S_a ≤ ½·a·log 2 + O(log a)` (`logTower_excess_eq`), i.e. linear drift with half the slope; the
logarithmic remainder belongs to the **centered excess** `Σ_{i<a}(Δ_i − ½log 2) = O(log a)`. (The
uncentered sum `Σ Δ_i` is required to be `≤ ½·a·log 2 + O(log a)`, not `O(log a)`.) Hence:

> **These three specific deterministic envelopes do not reach the prize drift.** Each is
> consistent with the full trivial ceiling, so none of them, as entered, can force the prize. What
> is missing is control of the centered excess `Σ(Δ_i − ½log 2) = O(log a)` (the binding-frequency
> phase law), which these envelopes do not supply. This is a limitation of the entered envelopes,
> not an impossibility result for martingale/concentration methods in general.

Lane-3. Axiom-clean: `propext`, `Classical.choice`, `Quot.sound`. No CORE / cancellation /
completion / moment / anti-concentration / capacity claim. CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays
OPEN.
-/

set_option linter.style.longLine false


namespace ProximityGap.Frontier.DoorIVMartingaleInputCeilingCapstone

open ProximityGap.Frontier.LogRatioTowerBoundedIncrement
open ProximityGap.Frontier.DoorIVQVCauchySchwarzCircular

variable (Mtow : ℕ → ℝ)

/-- **The bounded-increment-sum envelope gives `S_a ≤ a·log 2`** (deterministic). Restatement of
`logTower_le_card_mul_log2` at the capstone namespace. -/
theorem boundedSum_ceiling (a : ℕ)
    (hpos : ∀ i, 0 < Mtow i)
    (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i) :
    Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * Real.log 2 :=
  logTower_le_card_mul_log2 (Mtow := Mtow) a hpos hdouble

/-- **The raw squared-increment envelope gives `S_a ≤ a·log 2`** (via Cauchy–Schwarz,
deterministic, under the entered monotonicity hypothesis `hmono`). Restatement of
`qv_route_recovers_trivial_ceiling`. The sum `Σ Δ_i²` used there is a deterministic sum of
squared log increments, not a martingale predictable quadratic variation. -/
theorem qv_ceiling (a : ℕ)
    (hpos : ∀ i, 0 < Mtow i)
    (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i)
    (hmono : ∀ i, Mtow i ≤ Mtow (i + 1)) :
    Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * Real.log 2 :=
  qv_route_recovers_trivial_ceiling Mtow a hpos hdouble hmono

/-- **Compatibility package: both deterministic envelopes give the same trivial ceiling.** The
bounded-increment-sum envelope and the raw squared-increment envelope both bound the tower drift
by `a·log 2`.

Note: the two conjuncts are the **identical proposition** (one proved by each route), so this
package carries no more information than `boundedSum_ceiling` alone; it is kept only for the
existing consumer in `CampaignProvenIndex`. New code should cite `boundedSum_ceiling` (or
`qv_ceiling`) directly. -/
theorem martingale_inputs_same_ceiling (a : ℕ)
    (hpos : ∀ i, 0 < Mtow i)
    (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i)
    (hmono : ∀ i, Mtow i ≤ Mtow (i + 1)) :
    (Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * Real.log 2) ∧
      (Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * Real.log 2) :=
  ⟨boundedSum_ceiling Mtow a hpos hdouble,
   qv_ceiling Mtow a hpos hdouble hmono⟩

/-- **The trivial ceiling does not certify a smaller target.** The prize requires the drift bound
`S_a ≤ R` with `R = ½·a·log 2 + O(log a)` (half-slope linear, not sublinear), which is `< a·log 2`
once the `O(log a)` slack is below the `½·a·log 2` gap. For any target `R < a·log 2`, the trivial
ceiling `a·log 2` is NOT `≤ R`. This is the literal statement `¬ (a·log 2 ≤ R)` from `R < a·log 2`:
it shows only that the two specific envelopes above, whose output is `a·log 2`, cannot by
themselves certify the prize drift. It is not a theorem about all concentration methods; the
missing input is control of the centered excess `Σ(Δ_i − ½log 2) = O(log a)`. -/
theorem no_martingale_input_reaches_sublinear (a : ℕ) (R : ℝ)
    (hR : R < (a : ℝ) * Real.log 2) :
    ¬ ((a : ℝ) * Real.log 2 ≤ R) :=
  qv_route_no_sublinear_saving a R hR

/-- **The `√n` gap (strict separation of the two ceilings).** The prize drift slope `½·a·log 2` is
STRICTLY below the trivial envelope ceiling `a·log 2` for every `a ≥ 1`, with gap exactly
`½·a·log 2`. Exponentiated, this gap is the factor `2^{a/2} = √(2^a) = √n` that the entered
deterministic envelopes do not remove: they land at `2^a` while the prize sits at
`√(2^a)·log-slack`. This is pure scalar arithmetic about those two ceilings. -/
theorem prize_ceiling_strictly_below_martingale_ceiling (a : ℕ) (ha : 1 ≤ a) :
    (a : ℝ) * (Real.log 2 / 2) < (a : ℝ) * Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hapos : (0 : ℝ) < (a : ℝ) := by linarith
  -- a·(log2/2) < a·log2  ⇺  log2/2 < log2  (a > 0)
  nlinarith [hlog2, hapos]

/-- **The gap is exactly `½·a·log 2`.** The difference between the trivial envelope ceiling and
the prize drift slope is `a·log2 − a·(log2/2) = ½·a·log 2`, i.e. exactly the prize slope itself —
an argument must halve the per-level average drift budget, the `√n` the BGK wall is about. -/
theorem martingale_minus_prize_ceiling_eq (a : ℕ) :
    (a : ℝ) * Real.log 2 - (a : ℝ) * (Real.log 2 / 2) = (a : ℝ) * (Real.log 2 / 2) := by
  ring

end ProximityGap.Frontier.DoorIVMartingaleInputCeilingCapstone
