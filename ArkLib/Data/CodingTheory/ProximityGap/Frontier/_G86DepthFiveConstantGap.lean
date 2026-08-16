/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic.NormNum

/-!
# G86: the depth-five frontier is an exact constant-factor ten gap

G83 proves that the crude free-scaling orbit universe `n^8` at primitive depth five exceeds the
factorial-corrected production Wick budget.  Quotienting the two ordered five-tuples by coordinate
permutations and swapping the two sides offers the natural symmetry factor

`2 * (5!)^2 = 28800`.

This file pins the remaining arithmetic exactly.  After that symmetry factor, an additional
factor `9` is insufficient, while factor `10` is sufficient.  Thus a depth-five closure through
the corrected-padding route needs only a genuine tenfold saving beyond the obvious ordering
symmetries—not another power of `n` and not a new asymptotic exponent.

No claim is made here that the permutation action is free on repeated-coordinate cores, nor that
the extra factor ten exists.  Those are the remaining combinatorial strata obligations.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G86DepthFiveConstantGap

/-- The factorial-corrected padding envelope used by the G81/G83 chain. -/
def correctedEnvelope (n r J s : ℕ) : ℕ :=
  J * (r.descFactorial s) ^ 2 * n ^ (r - s) * (r - s).factorial

/-- The evident ordering symmetry factor at depth five: left permutations, right permutations,
and side swap. -/
def depthFiveOrderingSymmetry : ℕ := 2 * ((5 : ℕ).factorial) ^ 2

theorem depthFiveOrderingSymmetry_eq : depthFiveOrderingSymmetry = 28800 := by
  norm_num [depthFiveOrderingSymmetry, Nat.factorial]

/-- **Nine is not enough.**  Even after the evident ordering symmetries and a further factor nine,
the crude depth-five universe still exceeds the production Wick budget. -/
theorem production_depth_five_factor_nine_insufficient :
    depthFiveOrderingSymmetry * 9 *
        (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110) <
      (2 ^ 30) ^ 8 * correctedEnvelope (2 ^ 30) 110 1 5 := by
  norm_num [depthFiveOrderingSymmetry, correctedEnvelope, Nat.descFactorial,
    Nat.factorial, Nat.doubleFactorial]

/-- **Ten is enough.**  A tenfold saving beyond coordinate permutations and side swap closes the
entire crude production depth-five universe. -/
theorem production_depth_five_factor_ten_sufficient :
    (2 ^ 30) ^ 8 * correctedEnvelope (2 ^ 30) 110 1 5 ≤
      depthFiveOrderingSymmetry * 10 *
        (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110) := by
  norm_num [depthFiveOrderingSymmetry, correctedEnvelope, Nat.descFactorial,
    Nat.factorial, Nat.doubleFactorial]

end ArkLib.ProximityGap.Frontier.G86DepthFiveConstantGap

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G86DepthFiveConstantGap.production_depth_five_factor_nine_insufficient
#print axioms
  ArkLib.ProximityGap.Frontier.G86DepthFiveConstantGap.production_depth_five_factor_ten_sufficient
