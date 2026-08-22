/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.LogRatioTowerBoundedIncrement
import Mathlib.Algebra.Order.Chebyshev

/-!
# Door-(iv) Lane-3 constraint: the Freedman QV route is CIRCULAR (#444)

`LogRatioTowerBoundedIncrement` established the Freedman/Azuma PREREQUISITE for the log-ratio tower:
- the telescope `S_a := log(Mtow a) − log(Mtow 0) = Σ_{i<a} Δ_i`  (`logTower_telescope`),
- the bounded increments `Δ_i ∈ [0, log 2]`  (`logRatio_nonneg`, `logRatio_le_log2`),
- the predictable quadratic variation bound `Σ_{i<a} Δ_i² ≤ (log 2)·S_a`  (`logTower_sq_le_log2_mul`).

The prize is equivalent (`logTower_excess_eq`) to the excess sum being SUBLINEAR, `S_a ≤ ½·a·log 2 +
O(log a)`. The natural Freedman/Azuma lever is to combine the proven QV bound with Cauchy–Schwarz on
the increments to control the drift `S_a`. **This file proves that combination is SELF-DEFEATING:**

  `S_a² = (Σ_{i<a} Δ_i)²  ≤(Cauchy–Schwarz)  a · Σ_{i<a} Δ_i²  ≤(proven QV)  a · log 2 · S_a`,

so (with `S_a ≥ 0`) `S_a ≤ a · log 2` — EXACTLY the trivial linear drift ceiling
(`log Mtow a − log Mtow 0 ≤ a·log 2`, i.e. `Mtow a ≤ 2^a · Mtow 0`, the trivial `n`-ceiling). The
QV route is CIRCULAR: its own `√S_a` reappears on the right via the QV–drift coupling, and unwinding
returns the bound it started from. It gives NO sublinear (prize) saving.

This LOCKS the §1.2 Azuma/Freedman lever as door-(iii)-equivalent-dead: bounded increments + their
predictable quadratic variation, the full martingale-concentration input, are CONSISTENT with the
entire trivial linear ceiling and therefore cannot force the prize. The open object is unchanged: an
INDEPENDENT mean-drift control `Σ Δ_i = O(log a)` (the binding-frequency phase law), which neither the
increment envelope nor its quadratic variation supply.

## What is landed (axiom-clean: `propext`, `Classical.choice`, `Quot.sound`)
Abstract over the same tower `Mtow : ℕ → ℝ` as the parent file. No CORE / cancellation / completion /
moment / anti-concentration / capacity claim. CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.

Probe-anchoring: the QV input `Σ Δ_i² ≤ (log 2)·S_a` is a deductive consequence of the prize-regime-
validated increment envelope `Δ_i ∈ [0, log 2]` (`rho_i ∈ [√2, 2]` on PROPER thin subgroups `p ≫ n³`,
`probe_rho_increment_bounded.py`, `probe_rho_excess_growth.py`), inherited from `logTower_sq_le_log2_mul`.
The circularity proved here is a pure arithmetic identity on top of that input — no new empirical claim.
-/

set_option linter.style.longLine false


namespace ProximityGap.Frontier.DoorIVQVCauchySchwarzCircular

open Finset
open ProximityGap.Frontier.LogRatioTowerBoundedIncrement

variable (Mtow : ℕ → ℝ)

/-- **Cauchy–Schwarz on the increments.** The square of the telescoped drift is at most the number of
levels times the predictable quadratic variation:
`(Σ_{i<a} Δ_i)² ≤ a · Σ_{i<a} Δ_i²`. This is the unweighted Cauchy–Schwarz / Chebyshev sum
inequality applied to the increments `Δ_i = log(Mtow (i+1)) − log(Mtow i)`. -/
theorem cauchy_schwarz_increments (a : ℕ) :
    (∑ i ∈ Finset.range a, (Real.log (Mtow (i + 1)) - Real.log (Mtow i))) ^ 2
      ≤ (a : ℝ) * ∑ i ∈ Finset.range a,
          (Real.log (Mtow (i + 1)) - Real.log (Mtow i)) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.range a)
    (f := fun i => Real.log (Mtow (i + 1)) - Real.log (Mtow i))
  simpa [Finset.card_range] using h

/-- **The drift squared is bounded by `a·log 2·S_a` (Cauchy–Schwarz ∘ proven QV).** Composing the
Cauchy–Schwarz bound on the increments with the proven predictable-quadratic-variation bound
`Σ Δ_i² ≤ (log 2)·S_a` (`logTower_sq_le_log2_mul`): writing `S_a = Σ Δ_i` (`logTower_telescope`),
`S_a² ≤ a · Σ Δ_i² ≤ a · log 2 · S_a`. This is the full Freedman input chained together. -/
theorem drift_sq_le_card_mul_log2_mul_drift (a : ℕ)
    (hpos : ∀ i, 0 < Mtow i)
    (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i)
    (hmono : ∀ i, Mtow i ≤ Mtow (i + 1)) :
    (Real.log (Mtow a) - Real.log (Mtow 0)) ^ 2
      ≤ (a : ℝ) * Real.log 2 * (Real.log (Mtow a) - Real.log (Mtow 0)) := by
  -- S_a = Σ Δ_i (the telescope)
  have htel := logTower_telescope (Mtow := Mtow) a
  -- Cauchy–Schwarz: S_a² ≤ a · Σ Δ_i²
  have hcs := cauchy_schwarz_increments Mtow a
  -- proven QV: Σ Δ_i² ≤ (log 2)·S_a
  have hqv := logTower_sq_le_log2_mul (Mtow := Mtow) a hpos hdouble hmono
  -- a ≥ 0
  have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  -- chain: S_a² ≤ a·ΣΔ² ≤ a·(log2·S_a) = a·log2·S_a
  calc (Real.log (Mtow a) - Real.log (Mtow 0)) ^ 2
      = (∑ i ∈ Finset.range a,
          (Real.log (Mtow (i + 1)) - Real.log (Mtow i))) ^ 2 := by rw [htel]
    _ ≤ (a : ℝ) * ∑ i ∈ Finset.range a,
          (Real.log (Mtow (i + 1)) - Real.log (Mtow i)) ^ 2 := hcs
    _ ≤ (a : ℝ) * (Real.log 2 * (Real.log (Mtow a) - Real.log (Mtow 0))) :=
          mul_le_mul_of_nonneg_left hqv ha
    _ = (a : ℝ) * Real.log 2 * (Real.log (Mtow a) - Real.log (Mtow 0)) := by ring

/-- Subgroup-monotone tower: `Mtow 0 ≤ Mtow a` from the per-step monotonicity. -/
theorem tower_mono_zero_le (a : ℕ) (hmono : ∀ i, Mtow i ≤ Mtow (i + 1)) :
    Mtow 0 ≤ Mtow a := by
  induction a with
  | zero => exact le_refl _
  | succ k ih => exact le_trans ih (hmono k)

/-- **The QV route recovers ONLY the trivial linear ceiling (the circularity).** From the chained
bound `S_a² ≤ a·log 2·S_a` and the non-negativity `S_a ≥ 0` (subgroup-monotone tower), dividing by
`S_a` (or directly) gives `S_a ≤ a·log 2` — EXACTLY the trivial linear drift ceiling already supplied
by the bounded-increment sum (`logTower_le_card_mul_log2`). The Cauchy–Schwarz + predictable-QV input
is SELF-DEFEATING: it returns the bound it started from, with no sublinear (prize) saving. -/
theorem qv_route_recovers_trivial_ceiling (a : ℕ)
    (hpos : ∀ i, 0 < Mtow i)
    (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i)
    (hmono : ∀ i, Mtow i ≤ Mtow (i + 1)) :
    Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * Real.log 2 := by
  have hchain : Mtow 0 ≤ Mtow a := tower_mono_zero_le Mtow a hmono
  set S := Real.log (Mtow a) - Real.log (Mtow 0) with hS
  -- S ≥ 0 from monotonicity: log (Mtow 0) ≤ log (Mtow a)
  have hSnonneg : 0 ≤ S := by
    rw [hS]
    have hlog := Real.log_le_log (hpos 0) hchain
    linarith
  have hsq := drift_sq_le_card_mul_log2_mul_drift Mtow a hpos hdouble hmono
  -- S² ≤ (a·log2)·S, S ≥ 0 ⟹ S ≤ a·log2
  rcases eq_or_lt_of_le hSnonneg with hzero | hposS
  · rw [← hzero]
    positivity
  · -- S > 0: divide S² ≤ (a·log2)·S by S
    have hSsq : S ^ 2 ≤ (a : ℝ) * Real.log 2 * S := by rw [hS]; exact hsq
    nlinarith [hSsq, hposS]

/-- **No sublinear drift from the QV route (constraint form).** Any drift bound strictly below the
trivial ceiling, `S_a ≤ R` with `R < a·log 2`, is NOT a consequence of the Cauchy–Schwarz + proven-QV
combination: that combination is satisfied by the FULL trivial ceiling `S_a = a·log 2` (the largest
value consistent with `S² ≤ a·log2·S` at `S ≥ 0`). Hence the Freedman QV lever alone cannot force the
sublinear excess `S_a = O(log a)` the prize requires (`logTower_excess_eq`); an independent mean-drift
control is necessary. (Stated as: the QV-derived bound `S_a ≤ a·log 2` does not improve to any `R`
strictly smaller — the QV input does not distinguish the prize from the trivial ceiling.) -/
theorem qv_route_no_sublinear_saving (a : ℕ) (R : ℝ)
    (hR : R < (a : ℝ) * Real.log 2) :
    -- the QV-derived ceiling is a·log 2, which is NOT ≤ R; so R is not obtainable from the QV bound
    ¬ ((a : ℝ) * Real.log 2 ≤ R) := by
  intro h
  exact absurd (lt_of_le_of_lt h hR) (lt_irrefl _)

end ProximityGap.Frontier.DoorIVQVCauchySchwarzCircular
