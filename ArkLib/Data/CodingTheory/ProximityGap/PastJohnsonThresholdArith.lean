/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# The past-Johnson threshold arithmetic for the `M → δ*` bridge (#444)

A clean, self-contained re-formalization of the threshold arithmetic that the (now-removed,
non-compiling) `_e04`/`_e09` Frontier scaffolds *claimed* but did not prove (`Real.logb` was
unimported there). This file proves only the real-analysis inequality; it has NO ProximityGap
dependency and reduces to nothing open.

The intended `M → δ*` bridge (governing law + the tracked primitive
`MCADeltaStarListReduction.mcaDeltaStar_ge_of_uniform_mcaBad`) would convert a worst-case far-line
list budget `B` (with `B/q ≤ ε*`) into a floor of the shape `δ* ≥ 1 − ρ − H₂(ρ)/log₂ B`, where
`H₂` is the binary entropy **in bits**.  That bridge is NOT proved here (see the scope note).

**Units (read before using these theorems).**  Mathlib's `Real.binEntropy` uses NATURAL
logarithms (`Real.binEntropy (1/2) = log 2`), while `Real.logb 2 B` is in bits.  So the
expression `Real.binEntropy ρ / Real.logb 2 B` used in the first four theorems below is a
**mixed-unit** quantity: it equals `(log 2) · H₂(ρ)/log₂ B`, not the bit-normalized
`H₂(ρ)/log₂ B`.  The mismatch changes threshold decisions: at `ρ = 1/2`, `B = 16` the mixed
expression `1 − ρ − Real.binEntropy ρ / Real.logb 2 B ≈ 0.326713` exceeds Johnson
`1 − √ρ ≈ 0.292893`, whereas the bit-normalized `1 − ρ − H₂(ρ)/log₂ B = 0.25` is below it.  The
consistently normalized form is `Real.binEntropy ρ / Real.log B` (nats over nats), which equals
`(Real.binEntropy ρ / log 2) / Real.logb 2 B = H₂(ρ)/log₂ B` (`binEntropy_div_log_eq_bits`); the
theorems `pastJohnson_threshold_nats` / `deltaStar_gt_johnson_of_budget_nats` state the threshold
in that form.

The real inequalities proved below are all correct for the expressions actually written:
* `pastJohnson_threshold_correct` : for `ρ ∈ (0,1)`, if
  `Real.binEntropy ρ/(√ρ − ρ) < logb 2 B` then `Real.binEntropy ρ / logb 2 B < √ρ − ρ`;
* `threshold_of_floorGap_lt_margin` : the converse, on the regime `0 < logb 2 B`;
* `pastJohnson_threshold_iff` : the two combined;
* `deltaStar_gt_johnson_of_budget` : `1 − √ρ < 1 − ρ − Real.binEntropy ρ / logb 2 B` under the
  same (mixed-unit) threshold;
* `pastJohnson_threshold_nats`, `deltaStar_gt_johnson_of_budget_nats` : the unit-consistent
  versions with `Real.log B` in place of `Real.logb 2 B`.

Honest scope: this is real *arithmetic* only; no `δ*` result is proved here, and none of these
right-hand sides is shown to be a lower bound on the actual `δ*`.  The bridge's inputs — a counting
reduction producing the entropy floor with consistent units, and a worst-case `M`-bound actually
supplying such a budget `B` at the Ramanujan exponent (the recognized open core, BGK/BCHKS 1.12) —
are NOT addressed here.  Note also that `PrizeEntropyPinRefuted` machine-checks finite
refutations of the prize entropy pin (even after fixing the code rate and the logarithm units);
those refute specific statements, not every qualified asymptotic entropy law.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.PastJohnsonThreshold

open Real

/-- For `ρ ∈ (0,1)`, `ρ < √ρ`, hence the Johnson margin `√ρ − ρ > 0`. -/
theorem johnson_margin_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : 0 < Real.sqrt ρ - ρ := by
  have hpos : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ0
  have hlt1 : Real.sqrt ρ < 1 := by
    have := Real.sqrt_lt_sqrt hρ0.le hρ1
    rwa [Real.sqrt_one] at this
  have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ0.le
  nlinarith [hsq, hlt1, hpos]

/-- **Past-Johnson threshold arithmetic (binding direction, mixed units).** For `ρ ∈ (0,1)`, if
`log₂ B > Real.binEntropy ρ/(√ρ − ρ)` then `Real.binEntropy ρ / log₂ B < √ρ − ρ`.  Here
`Real.binEntropy` is in nats and `log₂ B` in bits, so this is NOT the bit-normalized entropy
floor; see `pastJohnson_threshold_nats` for the unit-consistent version.  No `δ*` claim. -/
theorem pastJohnson_threshold_correct {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hbudget : Real.binEntropy ρ / (Real.sqrt ρ - ρ) < Real.logb 2 B) :
    Real.binEntropy ρ / Real.logb 2 B < Real.sqrt ρ - ρ := by
  have hc : 0 < Real.sqrt ρ - ρ := johnson_margin_pos hρ0 hρ1
  have hH : 0 < Real.binEntropy ρ := Real.binEntropy_pos hρ0 hρ1
  have hfrac : 0 < Real.binEntropy ρ / (Real.sqrt ρ - ρ) := div_pos hH hc
  have hlb : 0 < Real.logb 2 B := lt_trans hfrac hbudget
  -- H/(√ρ−ρ) < L  ⟹  H < L·(√ρ−ρ)
  have h1 : Real.binEntropy ρ < Real.logb 2 B * (Real.sqrt ρ - ρ) :=
    (div_lt_iff₀ hc).mp hbudget
  -- conclude H/L < √ρ−ρ
  rw [div_lt_iff₀ hlb]
  nlinarith [h1]

/-- **Past-Johnson threshold (converse direction).** For `ρ ∈ (0,1)`, if the implied floor gap is
below the Johnson margin (`H(ρ)/log₂ B < √ρ − ρ`) *and* the budget exponent is positive
(`0 < log₂ B`, automatic once any list at all is past trivial), then the budget exponent clears the
threshold `log₂ B > H(ρ)/(√ρ − ρ)`. Together with `pastJohnson_threshold_correct` this makes the
threshold an **iff** on the positive-exponent regime. -/
theorem threshold_of_floorGap_lt_margin {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hlb : 0 < Real.logb 2 B)
    (hgap : Real.binEntropy ρ / Real.logb 2 B < Real.sqrt ρ - ρ) :
    Real.binEntropy ρ / (Real.sqrt ρ - ρ) < Real.logb 2 B := by
  have hc : 0 < Real.sqrt ρ - ρ := johnson_margin_pos hρ0 hρ1
  -- H/L < √ρ−ρ  ⟹  H < (√ρ−ρ)·L
  have h1 : Real.binEntropy ρ < (Real.sqrt ρ - ρ) * Real.logb 2 B :=
    (div_lt_iff₀ hlb).mp hgap
  -- conclude H/(√ρ−ρ) < L
  rw [div_lt_iff₀ hc]
  nlinarith [h1]

/-- **The threshold equivalence (iff).** On the positive-budget-exponent regime `0 < log₂ B`, the
floor gap is below the Johnson margin **iff** the budget exponent clears the threshold. -/
theorem pastJohnson_threshold_iff {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hlb : 0 < Real.logb 2 B) :
    Real.binEntropy ρ / Real.logb 2 B < Real.sqrt ρ - ρ ↔
      Real.binEntropy ρ / (Real.sqrt ρ - ρ) < Real.logb 2 B :=
  ⟨threshold_of_floorGap_lt_margin hρ0 hρ1 hlb,
   pastJohnson_threshold_correct hρ0 hρ1⟩

/-- **Past-Johnson arithmetic, packaged (mixed units).** For `ρ ∈ (0,1)`, if
`log₂ B > Real.binEntropy ρ/(√ρ − ρ)`, then `1 − ρ − Real.binEntropy ρ / log₂ B` strictly exceeds
the Johnson radius `1 − √ρ`.  Because `Real.binEntropy` is in nats and `log₂ B` in bits, this
expression is NOT the bit-normalized entropy floor `1 − ρ − H₂(ρ)/log₂ B` (at `ρ = 1/2`, `B = 16`
it is past Johnson while the bit-normalized floor is not); see
`deltaStar_gt_johnson_of_budget_nats` for the unit-consistent version.  No `δ*` result is proved
here: the counting bridge to `δ*` and supplying such a `B` at the Ramanujan exponent (the
BGK/BCHKS 1.12 core) are NOT addressed. -/
theorem deltaStar_gt_johnson_of_budget {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hbudget : Real.binEntropy ρ / (Real.sqrt ρ - ρ) < Real.logb 2 B) :
    (1 : ℝ) - Real.sqrt ρ < 1 - ρ - Real.binEntropy ρ / Real.logb 2 B := by
  -- floor gap below margin
  have hgap : Real.binEntropy ρ / Real.logb 2 B < Real.sqrt ρ - ρ :=
    pastJohnson_threshold_correct hρ0 hρ1 hbudget
  -- 1 − √ρ < 1 − ρ − (gap)  ⟺  gap < √ρ − ρ
  linarith [hgap]

/-! ### Unit-consistent (bit-normalized) versions

`Real.binEntropy` is in nats, so the unit-consistent floor gap is `Real.binEntropy ρ / Real.log B`
(nats over nats), which equals the bit-normalized `H₂(ρ)/log₂ B` with
`H₂(ρ) = Real.binEntropy ρ / log 2`. -/

/-- The unit-consistent floor gap is the bit-normalized one:
`Real.binEntropy ρ / log B = (Real.binEntropy ρ / log 2) / log₂ B`. -/
theorem binEntropy_div_log_eq_bits (ρ B : ℝ) :
    Real.binEntropy ρ / Real.log B = (Real.binEntropy ρ / Real.log 2) / Real.logb 2 B := by
  have h2 : Real.log 2 ≠ 0 := by positivity
  rw [Real.logb, div_div_div_cancel_right₀ h2]

/-- **Past-Johnson threshold, unit-consistent form.**  For `ρ ∈ (0,1)`, if
`Real.binEntropy ρ / (√ρ − ρ) < log B` then `Real.binEntropy ρ / log B < √ρ − ρ`. -/
theorem pastJohnson_threshold_nats {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hbudget : Real.binEntropy ρ / (Real.sqrt ρ - ρ) < Real.log B) :
    Real.binEntropy ρ / Real.log B < Real.sqrt ρ - ρ := by
  have hc : 0 < Real.sqrt ρ - ρ := johnson_margin_pos hρ0 hρ1
  have hH : 0 < Real.binEntropy ρ := Real.binEntropy_pos hρ0 hρ1
  have hlb : 0 < Real.log B := lt_trans (div_pos hH hc) hbudget
  have h1 : Real.binEntropy ρ < Real.log B * (Real.sqrt ρ - ρ) :=
    (div_lt_iff₀ hc).mp hbudget
  rw [div_lt_iff₀ hlb]
  nlinarith [h1]

/-- **Unit-consistent past-Johnson arithmetic.**  For `ρ ∈ (0,1)`, if
`Real.binEntropy ρ / (√ρ − ρ) < log B`, then `1 − √ρ < 1 − ρ − Real.binEntropy ρ / log B`, where
`Real.binEntropy ρ / log B = H₂(ρ)/log₂ B` (`binEntropy_div_log_eq_bits`).  Real arithmetic only:
it is not shown here that this right-hand side is a lower bound on `δ*`. -/
theorem deltaStar_gt_johnson_of_budget_nats {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hbudget : Real.binEntropy ρ / (Real.sqrt ρ - ρ) < Real.log B) :
    (1 : ℝ) - Real.sqrt ρ < 1 - ρ - Real.binEntropy ρ / Real.log B := by
  have hgap := pastJohnson_threshold_nats hρ0 hρ1 hbudget
  linarith [hgap]

end ArkLib.ProximityGap.PastJohnsonThreshold

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.PastJohnsonThreshold.johnson_margin_pos
#print axioms ArkLib.ProximityGap.PastJohnsonThreshold.pastJohnson_threshold_correct
#print axioms ArkLib.ProximityGap.PastJohnsonThreshold.threshold_of_floorGap_lt_margin
#print axioms ArkLib.ProximityGap.PastJohnsonThreshold.pastJohnson_threshold_iff
#print axioms ArkLib.ProximityGap.PastJohnsonThreshold.deltaStar_gt_johnson_of_budget
#print axioms ArkLib.ProximityGap.PastJohnsonThreshold.binEntropy_div_log_eq_bits
#print axioms ArkLib.ProximityGap.PastJohnsonThreshold.pastJohnson_threshold_nats
#print axioms ArkLib.ProximityGap.PastJohnsonThreshold.deltaStar_gt_johnson_of_budget_nats
