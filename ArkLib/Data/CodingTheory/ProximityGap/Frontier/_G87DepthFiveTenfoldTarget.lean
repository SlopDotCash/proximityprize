/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G83FreeOrbitEnergyBridge

/-!
# G87: the depth-five residual is an exact tenfold target

G83 shows that the elementary depth-five orbit universe, even after the free subgroup action,
does not fit the production Wick budget.  The next evident symmetry independently permutes the
five left core coordinates and the five right core coordinates and swaps the two sides.  Its
largest possible order is `2 * (5!)^2 = 28800`.

This file pins the arithmetic left after granting that entire symmetry.  Nine copies of the
symmetry-reduced Wick budget are still too small for the crude `n^8` orbit universe, while ten
copies suffice.  Thus any depth-five completion based on this universe needs one further factor
of ten (or a sharper sector count).  The theorem deliberately grants the full symmetry order:
it does not assert that the action is free on repeated-coordinate cores.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G87DepthFiveTenfoldTarget

open G81FactorialPaddingWickAbsorption

/-- The maximal order of independent left/right coordinate permutations and side swap at
primitive depth five. -/
theorem depthFiveObviousSymmetry_eq :
    2 * ((5 : ℕ).factorial) ^ 2 = 28800 := by
  norm_num

/-- Even after the full obvious depth-five symmetry, a further factor nine does not absorb the
crude production orbit universe. -/
theorem ninefold_symmetry_reduced_wick_lt_depthFiveOrbitUniverse :
    28800 * 9 *
        (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110) <
      (2 ^ 30) ^ 8 * correctedPadEnvelope (2 ^ 30) 110 1 5 := by
  norm_num [correctedPadEnvelope, Nat.doubleFactorial]

/-- A factor ten beyond the full obvious symmetry is arithmetically sufficient for the crude
production depth-five orbit universe. -/
theorem depthFiveOrbitUniverse_le_tenfold_symmetry_reduced_wick :
    (2 ^ 30) ^ 8 * correctedPadEnvelope (2 ^ 30) 110 1 5 ≤
      28800 * 10 *
        (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110) := by
  norm_num [correctedPadEnvelope, Nat.doubleFactorial]

/-- The least positive integral residual factor after granting the full order-`28800` symmetry
is exactly ten. -/
theorem depthFive_le_scaled_wick_iff_ten_le (c : ℕ) :
    (2 ^ 30) ^ 8 * correctedPadEnvelope (2 ^ 30) 110 1 5 ≤
        28800 * c *
          (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110) ↔
      10 ≤ c := by
  constructor
  · intro h
    by_contra hc
    have hc9 : c ≤ 9 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hc)
    have hle :
        28800 * c *
            (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110) ≤
          28800 * 9 *
            (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110) := by
      gcongr
    exact (not_lt_of_ge (h.trans hle))
      ninefold_symmetry_reduced_wick_lt_depthFiveOrbitUniverse
  · intro hc
    calc
      (2 ^ 30) ^ 8 * correctedPadEnvelope (2 ^ 30) 110 1 5 ≤
          28800 * 10 *
            (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110) :=
        depthFiveOrbitUniverse_le_tenfold_symmetry_reduced_wick
      _ ≤ 28800 * c *
            (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110) := by
        gcongr

/-- **All-depth calibration.**  G89 spends only one `111`th of the full Wick budget at each
depth.  Under that split, the least integral residual factor beyond the full obvious depth-five
symmetry is `1005`, not `10`.  This is the production-facing target for any refinement of the
crude `n^8` orbit universe. -/
theorem splitBudget_depthFive_le_scaled_wick_iff (c : ℕ) :
    111 * ((2 ^ 30) ^ 8 * correctedPadEnvelope (2 ^ 30) 110 1 5) ≤
        28800 * c *
          (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110) ↔
      1005 ≤ c := by
  norm_num [correctedPadEnvelope, Nat.doubleFactorial]
  omega

end ArkLib.ProximityGap.Frontier.G87DepthFiveTenfoldTarget

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G87DepthFiveTenfoldTarget.depthFiveObviousSymmetry_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G87DepthFiveTenfoldTarget.ninefold_symmetry_reduced_wick_lt_depthFiveOrbitUniverse
#print axioms
  ArkLib.ProximityGap.Frontier.G87DepthFiveTenfoldTarget.depthFiveOrbitUniverse_le_tenfold_symmetry_reduced_wick
#print axioms
  ArkLib.ProximityGap.Frontier.G87DepthFiveTenfoldTarget.depthFive_le_scaled_wick_iff_ten_le
#print axioms
  ArkLib.ProximityGap.Frontier.G87DepthFiveTenfoldTarget.splitBudget_depthFive_le_scaled_wick_iff
