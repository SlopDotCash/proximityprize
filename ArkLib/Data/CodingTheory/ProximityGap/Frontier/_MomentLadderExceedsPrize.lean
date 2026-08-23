/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MomentMethodNoGo

/-!
# The entire moment ladder overshoots the prize target — at every depth (#407)

`_MomentMethodNoGo.moment_bound_ge_card` proves the depth-`r` additive-moment bound is `≥ n` for
*every* order `r` (`(q·E_r)^{1/2r} ≥ n`). This file adds the matching upper comparison: in the prize
regime the per-frequency target `√(n·log(q/n))` is *strictly below* `n` (because `log(q/n) ≈ 110 ≪
n = 2³⁰`). Composing, **the whole moment ladder lies strictly above the prize target, at every depth
`r`** — so no single-moment method, of any order, can reach the prize floor. Together with
`_MetaTheoremSecondOrderFloor` (no method below the ladder helps) this closes the "no tighter bound
from any *moment* direction" face: the only way below `n` is genuine cross-moment / BGK cancellation.

* `prize_target_lt_card` — `√(n·log(q/n)) < n` whenever `log(q/n) < n` (the prize regime).
* `moment_ladder_exceeds_prize` — for any `r ≥ 1`, the depth-`r` ladder bound exceeds the prize
  target: `√(n·log(q/n)) < (q·E_r)^{1/2r}`.

Axiom target: `[propext, Classical.choice, Quot.sound]`. Issue #407.
-/

open Finset

namespace ProximityGap.Frontier.MomentLadderExceedsPrize

/-- **The prize target is below the trivial count `n`.** Whenever `log(q/n) < n` (always, in the
prize regime `n = 2³⁰`, `log(q/n) = 128·ln 2 ≈ 89`), the per-frequency target `√(n·log(q/n))` is
strictly less than `n`. So any bound that only reaches `n` (every moment-method bound, by
`moment_bound_ge_card`) overshoots the target. -/
theorem prize_target_lt_card {n q : ℝ} (hn : 0 < n) (hreg : Real.log (q / n) < n) :
    Real.sqrt (n * Real.log (q / n)) < n := by
  rcases le_total (n * Real.log (q / n)) 0 with h | h
  · calc Real.sqrt (n * Real.log (q / n)) = 0 := Real.sqrt_eq_zero'.mpr h
      _ < n := hn
  · have hlt : n * Real.log (q / n) < n ^ 2 := by nlinarith [mul_lt_mul_of_pos_left hreg hn]
    calc Real.sqrt (n * Real.log (q / n)) < Real.sqrt (n ^ 2) := Real.sqrt_lt_sqrt h hlt
      _ = n := Real.sqrt_sq hn.le

/-- **The moment ladder overshoots the prize target at every depth.** For any count function `c`
with total mass `n^r` (the `r`-fold additive-energy count, `∑_s (c s)² = E_r`, `∑_b‖η_b‖^{2r} = q·E_r`
with `|σ| = q`), the depth-`r` moment bound `(q·E_r)^{1/2r}` is `≥ n` (`moment_bound_ge_card`), and in
the prize regime `n > √(n·log(q/n))`. Hence **every rung of the ladder strictly exceeds the prize
per-frequency target** — no single-moment method, at any order `r`, reaches it. -/
theorem moment_ladder_exceeds_prize {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ) (hr : 0 < r)
    (hcount : ∑ s, c s = (n : ℝ) ^ r) {q : ℝ} (hn : 0 < (n : ℝ))
    (hreg : Real.log (q / n) < n) :
    Real.sqrt ((n : ℝ) * Real.log (q / n))
      < ((Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) := by
  have hladder : (n : ℝ) ≤ ((Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) :=
    ProximityGap.Frontier.MomentMethodNoGo.moment_bound_ge_card c n r hr hcount
  have htarget : Real.sqrt ((n : ℝ) * Real.log (q / n)) < (n : ℝ) := prize_target_lt_card hn hreg
  linarith

end ProximityGap.Frontier.MomentLadderExceedsPrize

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.MomentLadderExceedsPrize.prize_target_lt_card
#print axioms ProximityGap.Frontier.MomentLadderExceedsPrize.moment_ladder_exceeds_prize
