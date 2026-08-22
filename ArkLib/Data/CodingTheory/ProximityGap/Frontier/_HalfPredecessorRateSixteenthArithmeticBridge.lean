/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R382HalfRadiusPinConnector
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateSixteenth

/-!
# Arithmetic bridge for the rate-1/16 half predecessor

This file supplies the exact numeric handoff between the operational radius
`halfPredecessorRadius n` and the rate-`1/16` rich-point argument.  At `n = 2h`, positive
dimension, and `16k <= n`, it proves:

* `halfPredecessorRadius n = (h-1)/(2h)`;
* the ceiling agreement threshold is exactly `h+1`;
* `h >= 8` and, for `d = k-1`, `8d+8 <= h`;
* the complement of the large-core branch is exactly the core hypothesis consumed by
  `line_card_le_four`;
* the corresponding rational degree and core-excess coefficient bounds.

No geometric or incidence claim is introduced here.
-/

set_option autoImplicit false

open scoped NNReal
open ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenth

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthArithmeticBridge

/-- At even length `n=2h`, the operational predecessor is the literal rational radius
`(h-1)/(2h)`. -/
theorem halfPredecessorRadius_eq_explicit {n h : ℕ} (hn : n = 2 * h) :
    halfPredecessorRadius n =
      ((h - 1 : ℕ) : ℝ≥0) / (((2 * h : ℕ) : ℝ≥0)) := by
  subst n
  unfold halfPredecessorRadius
  have hhalf : 2 * h / 2 = h := by omega
  rw [hhalf]

/-- The full arithmetic expression inside the bad-event ceiling is exactly `h+1`. -/
theorem one_sub_halfPredecessor_mul_length_eq {h : ℕ} (hh : 1 ≤ h) :
    (1 - halfPredecessorRadius (2 * h)) * (((2 * h : ℕ) : ℝ≥0)) =
      ((h + 1 : ℕ) : ℝ≥0) := by
  rw [halfPredecessorRadius_eq_explicit (n := 2 * h) (h := h) rfl]
  have hden : (((2 * h : ℕ) : ℝ≥0)) ≠ 0 := by
    exact_mod_cast (show 2 * h ≠ 0 by omega)
  calc
    (1 - ((h - 1 : ℕ) : ℝ≥0) / (((2 * h : ℕ) : ℝ≥0))) *
          (((2 * h : ℕ) : ℝ≥0)) =
        1 * (((2 * h : ℕ) : ℝ≥0)) -
          (((h - 1 : ℕ) : ℝ≥0) / (((2 * h : ℕ) : ℝ≥0))) *
            (((2 * h : ℕ) : ℝ≥0)) := by rw [tsub_mul]
    _ = (((2 * h : ℕ) : ℝ≥0)) - ((h - 1 : ℕ) : ℝ≥0) := by
          rw [one_mul, div_mul_cancel₀ _ hden]
    _ = ((h + 1 : ℕ) : ℝ≥0) := by
          exact_mod_cast (show 2 * h - (h - 1) = h + 1 by omega)

/-- The selected full-agreement threshold at the half predecessor is exactly `h+1`. -/
theorem halfPredecessor_ceiling_agreement_eq {n h : ℕ} (hn : n = 2 * h)
    (hh : 1 ≤ h) :
    ⌈(1 - halfPredecessorRadius n) * (n : ℝ≥0)⌉₊ = h + 1 := by
  subst n
  rw [one_sub_halfPredecessor_mul_length_eq hh, Nat.ceil_natCast]

/-- The same ceiling computation for an explicitly supplied radius `(h-1)/(2h)`. -/
theorem explicit_halfPredecessor_ceiling_agreement_eq {h : ℕ} (hh : 1 ≤ h) :
    ⌈(1 - ((h - 1 : ℕ) : ℝ≥0) / ((2 * h : ℕ) : ℝ≥0)) *
        ((2 * h : ℕ) : ℝ≥0)⌉₊ = h + 1 := by
  rw [← halfPredecessorRadius_eq_explicit (n := 2 * h) (h := h) rfl]
  exact halfPredecessor_ceiling_agreement_eq rfl hh

/-- Positive dimension and rate at most `1/16` force the minimum half-length `h>=8`. -/
theorem eight_le_half_of_rateSixteenth {n h k : ℕ} (hn : n = 2 * h)
    (hk : 1 ≤ k) (hrate : 16 * k ≤ n) :
    8 ≤ h := by
  omega

/-- With `d=k-1`, the rate hypothesis has exactly the form consumed by the line-size lemma. -/
theorem degree_pred_rate_bound {n h k : ℕ} (hn : n = 2 * h)
    (hk : 1 ≤ k) (hrate : 16 * k ≤ n) :
    8 * (k - 1) + 8 ≤ h := by
  omega

/-- Complete arithmetic handoff from the operational parameterization to the rich-point one. -/
theorem halfPredecessor_rateSixteenth_handoff {n h k : ℕ} (hn : n = 2 * h)
    (hk : 1 ≤ k) (hrate : 16 * k ≤ n) :
    halfPredecessorRadius n =
        ((h - 1 : ℕ) : ℝ≥0) / (((2 * h : ℕ) : ℝ≥0)) ∧
      ⌈(1 - halfPredecessorRadius n) * (n : ℝ≥0)⌉₊ = h + 1 ∧
      8 ≤ h ∧ 8 * (k - 1) + 8 ≤ h := by
  have hh : 8 ≤ h := eight_le_half_of_rateSixteenth hn hk hrate
  exact ⟨halfPredecessorRadius_eq_explicit hn,
    halfPredecessor_ceiling_agreement_eq hn (by omega), hh,
    degree_pred_rate_bound hn hk hrate⟩

/-- Under `h>=8`, negating the manuscript's strict large-core inequality is exactly the
non-strict core bound expected by `line_card_le_four`. -/
theorem not_largeCore_iff_lineCore_bound {h d z : ℕ} (hh : 8 ≤ h) :
    (¬ h + 4 * d - 3 < 2 * z) ↔ 2 * z + 3 ≤ h + 4 * d := by
  omega

/-- Direct line-size consumer on the complement of the large-core branch. -/
theorem line_card_le_four_of_not_largeCore {h d z L : ℕ} (hh : 8 ≤ h)
    (hrate : 8 * d + 8 ≤ h)
    (hnotLarge : ¬ h + 4 * d - 3 < 2 * z)
    (hcount : L * (h + 1 - z) + z ≤ 2 * h) :
    L ≤ 4 := by
  exact line_card_le_four hh hrate
    ((not_largeCore_iff_lineCore_bound hh).1 hnotLarge) hcount

/-- Fully parameterized rate-`1/16` line-size handoff with `d=k-1`. -/
theorem line_card_le_four_of_rateSixteenth {n h k z L : ℕ}
    (hn : n = 2 * h) (hk : 1 ≤ k) (hrate : 16 * k ≤ n)
    (hnotLarge : ¬ h + 4 * (k - 1) - 3 < 2 * z)
    (hcount : L * (h + 1 - z) + z ≤ 2 * h) :
    L ≤ 4 := by
  exact line_card_le_four_of_not_largeCore
    (eight_le_half_of_rateSixteenth hn hk hrate)
    (degree_pred_rate_bound hn hk hrate) hnotLarge hcount

/-- Rational form of `d <= h/8-1`, used as the cubic coefficient bound in `upperSix`. -/
theorem degree_coefficient_rational_le {h d : ℕ} (hrate : 8 * d + 8 ≤ h) :
    (d : ℚ) ≤ (h : ℚ) / 8 - 1 := by
  have hrateQ : (8 : ℚ) * (d : ℚ) + 8 ≤ (h : ℚ) := by
    exact_mod_cast hrate
  linarith

/-- Rational form of the line-core excess bound used in the collinear-triple correction. -/
theorem core_excess_rational_le {h d z : ℕ}
    (hrate : 8 * d + 8 ≤ h) (hcore : 2 * z + 3 ≤ h + 4 * d) :
    (z : ℚ) - (d : ℚ) ≤ 5 * (h : ℚ) / 8 - 5 / 2 := by
  have hrateQ : (8 : ℚ) * (d : ℚ) + 8 ≤ (h : ℚ) := by
    exact_mod_cast hrate
  have hcoreQ : (2 : ℚ) * (z : ℚ) + 3 ≤ (h : ℚ) + 4 * (d : ℚ) := by
    exact_mod_cast hcore
  linarith

/-- Both rational coefficient bounds, packaged for the third-moment upper estimate. -/
theorem rational_upper_coefficients {h d z : ℕ}
    (hrate : 8 * d + 8 ≤ h) (hcore : 2 * z + 3 ≤ h + 4 * d) :
    (d : ℚ) ≤ (h : ℚ) / 8 - 1 ∧
      (z : ℚ) - (d : ℚ) ≤ 5 * (h : ℚ) / 8 - 5 / 2 :=
  ⟨degree_coefficient_rational_le hrate,
    core_excess_rational_le hrate hcore⟩

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthArithmeticBridge

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthArithmeticBridge
#print axioms halfPredecessor_ceiling_agreement_eq
#print axioms halfPredecessor_rateSixteenth_handoff
#print axioms not_largeCore_iff_lineCore_bound
#print axioms line_card_le_four_of_rateSixteenth
#print axioms rational_upper_coefficients
