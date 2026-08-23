/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Well-definedness of the MCA Johnson conjecture's errStar denominator.
The conjecture's errStar(δ) = (parℓ−1)·2^{2m} / (|F|·(2·min(1−√ρ−δ, √ρ/20))^7);
this file shows the min is strictly positive on the valid Johnson range, hence
errStar is a positive finite real (a prerequisite for the apex bound). -/

namespace MCAJohnson

open Real

/-- On the valid Johnson range `0 < δ < 1 − √ρ` with `0 < ρ`, the error-bound's
inner `min(1 − √ρ − δ, √ρ/20)` is strictly positive. -/
theorem min_val_pos {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 < δ) (hδ : δ < 1 - Real.sqrt ρ) :
    0 < min (1 - Real.sqrt ρ - δ) (Real.sqrt ρ / 20) := by
  apply lt_min
  · linarith
  · have : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
    linarith

/-- Consequently `(2 · min_val)^7 > 0`, so the errStar denominator is positive
whenever the field is nonempty. -/
theorem errStar_denom_pos {ρ δ : ℝ} (q : ℝ) (hq : 0 < q)
    (hρ : 0 < ρ) (hδ0 : 0 < δ) (hδ : δ < 1 - Real.sqrt ρ) :
    0 < q * (2 * min (1 - Real.sqrt ρ - δ) (Real.sqrt ρ / 20)) ^ 7 := by
  have hmin := min_val_pos hρ hδ0 hδ
  positivity

/-- The full errStar value is nonnegative (well-defined as an error probability
bound) on the valid range, for `parℓ ≥ 1`. -/
theorem errStar_nonneg {ρ δ : ℝ} (q : ℝ) (hq : 0 < q) (parℓ : ℕ) (m : ℕ)
    (hparℓ : 1 ≤ parℓ) (hρ : 0 < ρ) (hδ0 : 0 < δ) (hδ : δ < 1 - Real.sqrt ρ) :
    0 ≤ ((parℓ : ℝ) - 1) * 2 ^ (2 * m)
      / (q * (2 * min (1 - Real.sqrt ρ - δ) (Real.sqrt ρ / 20)) ^ 7) := by
  have hnum : 0 ≤ ((parℓ : ℝ) - 1) * 2 ^ (2 * m) := by
    have h1le : (1 : ℝ) ≤ (parℓ : ℝ) := by exact_mod_cast hparℓ
    have h1 : 0 ≤ (parℓ : ℝ) - 1 := by linarith
    positivity
  have hden := errStar_denom_pos q hq hρ hδ0 hδ
  exact div_nonneg hnum (le_of_lt hden)

end MCAJohnson
