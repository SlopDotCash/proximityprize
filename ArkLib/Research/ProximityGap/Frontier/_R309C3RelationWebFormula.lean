/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# R309 (#466): algebraic socket for the `c = 3` relation-web histogram

R308 found that the dangerous `c = 3` binomial norm relation web at `n = 64, 128`
has exactly three positive collision-delta strata:

* `n` fibers with delta `24n - 18`;
* `2n` fibers with delta `90`;
* `n(n - 7)` fibers with delta `36`.

This file proves the algebraic consequence only: that this histogram gives excess
`60n^2 - 90n`, and that this excess is larger than the depth-3 exact-Wick headroom
`45n^2 - 40n` for every `n >= 4`.  The hard relation-web classification remains the
named conjectural input exposed by R308; this socket prevents future arithmetic drift in
that target.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R309C3RelationWebFormula

/-- The `c = 3` relation-web histogram mass as an integer expression. -/
def c3HistogramMass (n : ℤ) : ℤ :=
  n * (24 * n - 18) + (2 * n) * 90 + (n * (n - 7)) * 36

/-- The exact-Wick depth-3 headroom `45n² - 40n`. -/
def depth3Headroom (n : ℤ) : ℤ :=
  45 * n * n - 40 * n

/-- R308's three-stratum histogram simplifies to `60n² - 90n`. -/
theorem c3HistogramMass_eq (n : ℤ) :
    c3HistogramMass n = 60 * n * n - 90 * n := by
  unfold c3HistogramMass
  ring

/-- The `c = 3` histogram beats the exact-Wick headroom for every `n >= 4`. -/
theorem depth3Headroom_lt_c3HistogramMass {n : ℤ} (hn : 4 ≤ n) :
    depth3Headroom n < c3HistogramMass n := by
  rw [c3HistogramMass_eq]
  unfold depth3Headroom
  nlinarith

/-- Equivalent gap form: the excess over headroom is `5n(3n-10)`. -/
theorem c3HistogramMass_sub_headroom (n : ℤ) :
    c3HistogramMass n - depth3Headroom n = 5 * n * (3 * n - 10) := by
  rw [c3HistogramMass_eq]
  unfold depth3Headroom
  ring

end ArkLib.ProximityGap.Frontier.R309C3RelationWebFormula

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R309C3RelationWebFormula.c3HistogramMass_eq
#print axioms ArkLib.ProximityGap.Frontier.R309C3RelationWebFormula.depth3Headroom_lt_c3HistogramMass
#print axioms ArkLib.ProximityGap.Frontier.R309C3RelationWebFormula.c3HistogramMass_sub_headroom
