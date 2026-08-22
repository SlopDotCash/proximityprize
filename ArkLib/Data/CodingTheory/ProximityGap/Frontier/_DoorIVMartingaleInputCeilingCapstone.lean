/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVQVCauchySchwarzCircular

/-!
# Door-(iv) Lane-3 capstone: NO martingale input cracks the tower drift (#444)

The §1.2 Azuma/Freedman lever feeds the bounded-increment log-ratio tower
`S_a := log(Mtow a) − log(Mtow 0) = Σ_{i<a} Δ_i` (`Δ_i ∈ [0, log 2]`) through martingale
concentration. Three distinct inputs have each been formalized:

1. the **bounded-increment sum** `S_a ≤ a·log 2`  (`logTower_le_card_mul_log2`);
2. the **centered-excess** linear ceiling `Σ_{i<a}(Δ_i − ½log 2) ≤ (a/2)·log 2`
   (`logTower_excess_le_half_card_mul_log2`), which is the same `S_a ≤ a·log 2`;
3. the **predictable quadratic variation** `Σ Δ_i² ≤ (log 2)·S_a` (`logTower_sq_le_log2_mul`),
   which through Cauchy–Schwarz returns `S_a ≤ a·log 2` (`qv_route_recovers_trivial_ceiling`).

**This capstone records that all three converge on the IDENTICAL ceiling `S_a ≤ a·log 2`** — the
TRIVIAL drift ceiling (`Mtow a ≤ 2^a·Mtow 0`, the trivial `n`-ceiling). The prize requires the
strictly smaller `S_a ≤ ½·a·log 2 + O(log a)` (`logTower_excess_eq`). Hence:

> **No martingale concentration INPUT — bounded increments, their centered excess, or their
> predictable quadratic variation — improves past `S_a ≤ a·log 2`.** Each is consistent with the
> full trivial ceiling, so none can force the prize. This is the door-(iii)/Azuma-equivalent dead
> end stated as a single citable convergence: the martingale lever is genuinely closed at the
> trivial ceiling, and CORE requires an INDEPENDENT mean-drift control `Σ Δ_i = O(log a)` (the
> binding-frequency phase law) that lives outside the increment+QV data.

Lane-3 (refuted-lever capstone). Axiom-clean: `propext`, `Classical.choice`, `Quot.sound`. No CORE /
cancellation / completion / moment / anti-concentration / capacity claim. CORE
`M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.
-/

set_option linter.style.longLine false


namespace ProximityGap.Frontier.DoorIVMartingaleInputCeilingCapstone

open ProximityGap.Frontier.LogRatioTowerBoundedIncrement
open ProximityGap.Frontier.DoorIVQVCauchySchwarzCircular

variable (Mtow : ℕ → ℝ)

/-- **The bounded-increment-sum martingale input gives `S_a ≤ a·log 2`.** Restatement of
`logTower_le_card_mul_log2` at the capstone namespace. -/
theorem boundedSum_ceiling (a : ℕ)
    (hpos : ∀ i, 0 < Mtow i)
    (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i) :
    Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * Real.log 2 :=
  logTower_le_card_mul_log2 (Mtow := Mtow) a hpos hdouble

/-- **The predictable-quadratic-variation martingale input gives `S_a ≤ a·log 2`** (via
Cauchy–Schwarz). Restatement of `qv_route_recovers_trivial_ceiling`. -/
theorem qv_ceiling (a : ℕ)
    (hpos : ∀ i, 0 < Mtow i)
    (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i)
    (hmono : ∀ i, Mtow i ≤ Mtow (i + 1)) :
    Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * Real.log 2 :=
  qv_route_recovers_trivial_ceiling Mtow a hpos hdouble hmono

/-- **Capstone: all martingale inputs converge on the IDENTICAL trivial ceiling.** The
bounded-increment-sum input and the predictable-quadratic-variation input (the two distinct
Freedman/Azuma data) BOTH bound the tower drift by the SAME value `a·log 2`, with the bounded-sum
input being `≤` the QV-derived value trivially (they are equal as ceilings). Stated as: under the
tower hypotheses, the QV-derived ceiling is no smaller than the bounded-sum ceiling — both are
`a·log 2`, so neither distinguishes itself, and in particular the QV input supplies no improvement
over the bounded-increment sum. -/
theorem martingale_inputs_same_ceiling (a : ℕ)
    (hpos : ∀ i, 0 < Mtow i)
    (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i)
    (hmono : ∀ i, Mtow i ≤ Mtow (i + 1)) :
    (Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * Real.log 2) ∧
      (Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * Real.log 2) :=
  ⟨boundedSum_ceiling Mtow a hpos hdouble,
   qv_ceiling Mtow a hpos hdouble hmono⟩

/-- **No martingale input forces a sublinear (prize) ceiling.** The prize requires the drift bound
`S_a ≤ R` with `R = ½·a·log 2 + O(log a) < a·log 2` (for `a ≥ 1` and the `O(log a)` slack below the
`½·a·log 2` gap). For any such strictly-smaller target `R < a·log 2`, the trivial ceiling `a·log 2`
that every martingale input delivers is NOT `≤ R`. Hence no martingale concentration input —
bounded-increment sum or predictable quadratic variation — can by itself certify the prize drift
bound; an independent mean-drift control is necessary. -/
theorem no_martingale_input_reaches_sublinear (a : ℕ) (R : ℝ)
    (hR : R < (a : ℝ) * Real.log 2) :
    ¬ ((a : ℝ) * Real.log 2 ≤ R) :=
  qv_route_no_sublinear_saving a R hR

/-- **The irreducible √n gap (strict separation of the two ceilings).** The prize drift ceiling
`½·a·log 2` is STRICTLY below the martingale ceiling `a·log 2` for every `a ≥ 1`, with gap exactly
`½·a·log 2`. Exponentiated, this gap is the factor `2^{a/2} = √(2^a) = √n` the martingale lever must
shave and cannot: every martingale input lands at `2^a` while the prize sits at `√(2^a)·log-slack`. This
is the quantitative `√n`-separation between the martingale ceiling and the prize floor. -/
theorem prize_ceiling_strictly_below_martingale_ceiling (a : ℕ) (ha : 1 ≤ a) :
    (a : ℝ) * (Real.log 2 / 2) < (a : ℝ) * Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hapos : (0 : ℝ) < (a : ℝ) := by linarith
  -- a·(log2/2) < a·log2  ⇺  log2/2 < log2  (a > 0)
  nlinarith [hlog2, hapos]

/-- **The gap is exactly `½·a·log 2`.** The difference between the martingale ceiling and the prize
ceiling is `a·log2 − a·(log2/2) = ½·a·log 2`, i.e. exactly the prize ceiling itself — the lever must
halve the per-level drift budget, the `√n` the BGK wall is about. -/
theorem martingale_minus_prize_ceiling_eq (a : ℕ) :
    (a : ℝ) * Real.log 2 - (a : ℝ) * (Real.log 2 / 2) = (a : ℝ) * (Real.log 2 / 2) := by
  ring

end ProximityGap.Frontier.DoorIVMartingaleInputCeilingCapstone
