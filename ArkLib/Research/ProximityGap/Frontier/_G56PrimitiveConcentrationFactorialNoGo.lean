/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# G56: factorial obstruction to the G104 primitive-concentration ladder

The G104 `(2,s-2)` scoping calculation requires, at `s=13`, an ordered primitive
11-tuple sum-fiber cap equal to the displayed quotient below. This file kernel-checks
that the quotient is `14,207,588`, while the ordering multiplicity of one 11-element
primitive support is `11! = 39,916,800`. Thus any such support already exceeds the
actual sharp-envelope budget. The accompanying exact prize-field probe certifies one
such zero-sum-free support, namely the first eleven powers of the certified generator.

This is a numeric consumer/no-go, not a construction theorem and not prize closure.
-/

namespace ArkLib.ProximityGap.Frontier.G56PrimitiveConcentrationFactorialNoGo

set_option maxRecDepth 100000

/-- The exact G104 ordered primitive-fiber allowance at `s=13`, `r=110`, `n=2^30`. -/
def s13Threshold : ℕ :=
  Nat.doubleFactorial 219 /
    (((110).choose 13) ^ 2 * (97).factorial * (2 ^ 30) ^ 2)

/-- Exact evaluation of the sharp-envelope allowance. -/
theorem s13Threshold_eq : s13Threshold = 14207588 := by
  norm_num [s13Threshold, Nat.doubleFactorial, Nat.factorial, Nat.choose]

/-- One primitive 11-support's ordering orbit already exceeds the allowance. -/
theorem eleven_factorial_exceeds_s13Threshold : s13Threshold < (11).factorial := by
  norm_num [s13Threshold_eq, Nat.factorial]

/-- It also exceeds G104's proposed uniform `4 n^(2/3) = 4*2^20` cap. -/
theorem eleven_factorial_exceeds_uniformCap : 4 * 2 ^ 20 < (11).factorial := by
  norm_num [Nat.factorial]

#print axioms s13Threshold_eq
#print axioms eleven_factorial_exceeds_s13Threshold
#print axioms eleven_factorial_exceeds_uniformCap

end ArkLib.ProximityGap.Frontier.G56PrimitiveConcentrationFactorialNoGo
