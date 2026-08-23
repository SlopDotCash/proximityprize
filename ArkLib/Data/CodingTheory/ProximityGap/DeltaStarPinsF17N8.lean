/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RatioPigeonholeGoodSide
import ArkLib.Data.CodingTheory.ProximityGap.MCAListBracketInterpolation

/-!
# Two unconditional `delta*` pins on the eight-point smooth domain over `F_17`

The five-thirds ratio-pigeonhole theorem supplies field-size-free good sides on two
previously conditional bands in the exhaustive `F_17` census.  The pencil families from
`BadFamilyCensus` supply wider bad sides at the jump radii.  Together they give:

* degree at most `2`: `delta* = 1/4` for every budget in `[2/17, 4/17)`;
* degree at most `1`: `delta* = 3/8` for every budget in `[3/17, 8/17)`.

The first result discharges the second component of `CompleteEnvelopeF17` wherever that
component is used to pin the operational threshold.  Neither theorem uses the exhaustive
Python census or a named residual.
-/

set_option autoImplicit false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger
open ProximityGap.MCAListBracketInterpolation
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.BadFamilyCensus
open ArkLib.ProximityGap.RatioPigeonhole

namespace ArkLib.ProximityGap.DeltaStarPinsF17N8

local instance fact_prime_17_pin : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-! ## The degree-two pin -/

/-- Every radius below `1/4` is good at budget `2/17` for the degree-at-most-two code. -/
theorem epsMCA_d2_le_two_seventeenths_of_lt_quarter
    {delta : ℝ≥0} (hdelta : delta < 1 / 4) :
    epsMCA (F := ZMod 17) (evalCode (2 : ZMod 17) 8 2) delta
      ≤ (2 : ℝ≥0∞) / (17 : ℝ≥0∞) := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have hband :
      delta < (((8 - 7 + 1 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0)) := by
    norm_num at hdelta ⊢
    exact hdelta
  have h := fiveThirds_epsMCA_le_of_lt (p := 17) (n := 8) (d := 2) (t := 7)
    (g := (2 : ZMod 17)) orderOf_two_F17
    (by norm_num) (by norm_num) (by norm_num) hband
  norm_num at h ⊢
  exact h

/-- **Unconditional exact pin, degree at most two.**  For every
`epsilon* in [2/17, 4/17)`, the operational threshold is exactly `1/4`.

The good-below side is the five-thirds strip at agreement threshold `t = 7`.  The bad-at
side is the four-scalar `s = 2` pencil at agreement threshold `6`. -/
theorem mcaDeltaStar_d2_eq_quarter {epsilonStar : ℝ≥0∞}
    (hlo : (2 : ℝ≥0∞) / (17 : ℝ≥0∞) ≤ epsilonStar)
    (hhi : epsilonStar < (4 : ℝ≥0∞) / (17 : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod 17) (A := ZMod 17)
      (evalCode (2 : ZMod 17) 8 2) epsilonStar = 1 / 4 := by
  refine mcaDeltaStar_eq_of_jump _ epsilonStar
    (by rw [div_le_one (by norm_num : (0 : ℝ≥0) < 4)]; norm_num) ?_ ?_
  · intro delta hdelta
    exact le_trans (epsMCA_d2_le_two_seventeenths_of_lt_quarter hdelta) hlo
  · exact lt_of_lt_of_le hhi pencil2_epsMCA_F17

/-! ## The degree-one pin -/

/-- Every radius below `3/8` is good at budget `3/17` for the degree-at-most-one code. -/
theorem epsMCA_d1_le_three_seventeenths_of_lt_three_eighths
    {delta : ℝ≥0} (hdelta : delta < 3 / 8) :
    epsMCA (F := ZMod 17) (evalCode (2 : ZMod 17) 8 1) delta
      ≤ (3 : ℝ≥0∞) / (17 : ℝ≥0∞) := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have hband :
      delta < (((8 - 6 + 1 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0)) := by
    norm_num at hdelta ⊢
    exact hdelta
  have h := fiveThirds_epsMCA_le_of_lt (p := 17) (n := 8) (d := 1) (t := 6)
    (g := (2 : ZMod 17)) orderOf_two_F17
    (by norm_num) (by norm_num) (by norm_num) hband
  norm_num at h ⊢
  exact h

/-- The `s = 1` pencil gives eight bad scalars at radius `3/8` for the
degree-at-most-one code. -/
theorem pencil1_epsMCA_F17_d1 :
    (8 : ℝ≥0∞) / (17 : ℝ≥0∞)
      ≤ epsMCA (F := ZMod 17) (evalCode (2 : ZMod 17) 8 1) (3 / 8 : ℝ≥0) := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have h := pencil_rung_epsMCA_lower_bound (p := 17) (n := 8) (h := 4) (d := 1)
    (s := 1) (by norm_num) (by norm_num) (g := (2 : ZMod 17)) orderOf_two_F17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e1 : ((8 / 1 : ℕ) : ℝ≥0∞) = (8 : ℝ≥0∞) := by norm_num
  have e2 : ((17 : ℕ) : ℝ≥0∞) = (17 : ℝ≥0∞) := by norm_num
  have e3 :
      (1 : ℝ≥0) - ((4 + 1 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0) = 3 / 8 := by
    have hratio : ((4 + 1 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0) = 5 / 8 := by
      norm_num
    rw [hratio]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e1, e2, e3] at h
  exact h

/-- **Unconditional exact pin, degree at most one.**  For every
`epsilon* in [3/17, 8/17)`, the operational threshold is exactly `3/8`.

The good-below side is the five-thirds strip at agreement threshold `t = 6`.  The bad-at
side is the eight-scalar antipodal pencil at agreement threshold `5`. -/
theorem mcaDeltaStar_d1_eq_three_eighths {epsilonStar : ℝ≥0∞}
    (hlo : (3 : ℝ≥0∞) / (17 : ℝ≥0∞) ≤ epsilonStar)
    (hhi : epsilonStar < (8 : ℝ≥0∞) / (17 : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod 17) (A := ZMod 17)
      (evalCode (2 : ZMod 17) 8 1) epsilonStar = 3 / 8 := by
  refine mcaDeltaStar_eq_of_jump _ epsilonStar
    (by rw [div_le_one (by norm_num : (0 : ℝ≥0) < 8)]; norm_num) ?_ ?_
  · intro delta hdelta
    exact le_trans
      (epsMCA_d1_le_three_seventeenths_of_lt_three_eighths hdelta) hlo
  · exact lt_of_lt_of_le hhi pencil1_epsMCA_F17_d1

end ArkLib.ProximityGap.DeltaStarPinsF17N8

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.DeltaStarPinsF17N8.epsMCA_d2_le_two_seventeenths_of_lt_quarter
#print axioms ArkLib.ProximityGap.DeltaStarPinsF17N8.mcaDeltaStar_d2_eq_quarter
#print axioms
  ArkLib.ProximityGap.DeltaStarPinsF17N8.epsMCA_d1_le_three_seventeenths_of_lt_three_eighths
#print axioms ArkLib.ProximityGap.DeltaStarPinsF17N8.pencil1_epsMCA_F17_d1
#print axioms ArkLib.ProximityGap.DeltaStarPinsF17N8.mcaDeltaStar_d1_eq_three_eighths
