/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Rate-quarter no-eight branch: the bare twelve-point syndrome bound is false

The source-core-seven no-eight reduction produces an affine line in the
five-dimensional syndrome quotient of a punctured `RS[9,4]`, with every
selected point represented on at most three coordinate columns.  Those data
alone do not imply the required ceiling of twelve.

Over `ZMod 17`, take nine points from the order-sixteen multiplicative domain.
The line below has thirteen distinct proper intersections with three-column
spans.  Every intersection comes with explicit coefficients.  An explicit
annihilator kills its three support columns but not the line direction, so no
listed support contains the whole affine line.

This is only a counterexample to the *bare* syndrome-line bound.  It does not
realize the source-root factorization or the global relevant-core constraints
of a no-eight residual; those couplings remain necessary in any closure.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightBareSyndromeRefuted

abbrev F := ZMod 17

/-- Five-dimensional Vandermonde syndrome column at `x`. -/
def column (x : F) : Fin 5 → F := fun j ↦ x ^ (j : Nat)

/-- A nine-point subset of the order-sixteen multiplicative domain in `F_17`. -/
def domain : Fin 9 → F := ![1, 3, 9, 10, 13, 5, 15, 11, 16]

def base : Fin 5 → F := ![(12 : F), 8, 5, 8, 10]
def direction : Fin 5 → F := ![(13 : F), 0, 14, 15, 4]
def linePoint (gamma : F) : Fin 5 → F := fun j ↦ base j + gamma * direction j

/-- The thirteen distinct affine parameters in the certificate. -/
def gamma : Fin 13 → F := ![0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 14, 15]

/-- Three support indices for every certified parameter. -/
def i0 : Fin 13 → Fin 9 := ![0, 0, 0, 0, 1, 3, 1, 1, 5, 2, 1, 0, 0]
def i1 : Fin 13 → Fin 9 := ![3, 2, 1, 1, 2, 6, 6, 5, 6, 5, 5, 3, 6]
def i2 : Fin 13 → Fin 9 := ![7, 4, 2, 4, 4, 7, 8, 8, 8, 7, 6, 6, 7]

def a0 : Fin 13 → F := ![7, 9, 6, 3, 7, 12, 9, 13, 7, 14, 12, 2, 15]
def a1 : Fin 13 → F := ![3, 14, 8, 16, 10, 4, 10, 12, 7, 5, 9, 7, 10]
def a2 : Fin 13 → F := ![2, 2, 7, 15, 13, 6, 16, 6, 13, 4, 11, 15, 12]

/-- A support annihilator for each of the thirteen witnesses. -/
def annihilator : Fin 13 → Fin 5 → F := ![
  ![(9 : F), 12, 12, 1, 0], ![(2 : F), 3, 11, 1, 0],
  ![(7 : F), 5, 4, 1, 0], ![(12 : F), 4, 0, 1, 0],
  ![(6 : F), 13, 9, 1, 0], ![(16 : F), 0, 15, 1, 0],
  ![(11 : F), 10, 0, 1, 0], ![(15 : F), 7, 10, 1, 0],
  ![(7 : F), 4, 15, 1, 0], ![(15 : F), 12, 9, 1, 0],
  ![(13 : F), 16, 11, 1, 0], ![(3 : F), 5, 8, 1, 0],
  ![(5 : F), 4, 7, 1, 0]]

def dot5 (v w : Fin 5 → F) : F := ∑ j, v j * w j

/-- The nine evaluation points are distinct. -/
theorem domain_injective : Function.Injective domain := by
  decide

/-- The thirteen advertised affine parameters are distinct. -/
theorem gamma_injective : Function.Injective gamma := by
  decide

/-- Every support consists of three distinct coordinates of the fixed domain. -/
theorem support_pairwise_ne (j : Fin 13) :
    i0 j ≠ i1 j ∧ i0 j ≠ i2 j ∧ i1 j ≠ i2 j := by
  fin_cases j <;> decide

/-- All three displayed coefficients are nonzero. -/
theorem coefficients_ne_zero (j : Fin 13) :
    a0 j ≠ 0 ∧ a1 j ≠ 0 ∧ a2 j ≠ 0 := by
  fin_cases j <;> decide

/-- All thirteen line points have explicit exact three-column representations. -/
theorem thirteen_three_column_representations (j : Fin 13) :
    linePoint (gamma j) = fun r ↦
      a0 j * column (domain (i0 j)) r +
      a1 j * column (domain (i1 j)) r +
      a2 j * column (domain (i2 j)) r := by
  fin_cases j <;> funext r <;> fin_cases r <;> decide

/-- The listed functional kills all three support columns. -/
theorem annihilator_support (j : Fin 13) :
    dot5 (annihilator j) (column (domain (i0 j))) = 0 ∧
      dot5 (annihilator j) (column (domain (i1 j))) = 0 ∧
      dot5 (annihilator j) (column (domain (i2 j))) = 0 := by
  fin_cases j <;> decide

/-- The same functional does not kill the line direction, proving properness. -/
theorem annihilator_direction_ne_zero (j : Fin 13) :
    dot5 (annihilator j) direction ≠ 0 := by
  fin_cases j <;> decide

/-- The certified proper-incidence count exceeds the desired bare ceiling. -/
theorem thirteen_gt_twelve : 12 < 13 := by omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightBareSyndromeRefuted

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightBareSyndromeRefuted
#print axioms thirteen_three_column_representations
#print axioms annihilator_support
#print axioms annihilator_direction_ne_zero
#print axioms gamma_injective
