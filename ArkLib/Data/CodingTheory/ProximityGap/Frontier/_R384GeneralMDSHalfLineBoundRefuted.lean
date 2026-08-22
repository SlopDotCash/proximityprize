/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# R384: the unrestricted half-radius MDS line bound is false

For the order-seven Vandermonde arc over `ZMod 29`, a line in the four-dimensional
syndrome space has twelve proper intersections with spans of three columns.  This
refutes the R382 conjecture under only `2e<n` and `e+k+1<=n`: here
`(n,k,e)=(7,3,3)` satisfies both inequalities but `12>7`.

The example lies at support codimension one, `D-e=1`.  It does not refute the prize
range `k<=n/4`, where `D-e=n/2-k+1` grows linearly.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R384GeneralMDSHalfLineBoundRefuted

abbrev F := ZMod 29

def column (x : F) : Fin 4 → F := fun j => x ^ (j : Nat)

def base : Fin 4 → F := ![(1 : F), 24, 25, 20]
def direction : Fin 4 → F := ![(16 : F), 6, 10, 13]
def linePoint (gamma : F) : Fin 4 → F := fun j => base j + gamma * direction j

def gamma : Fin 12 → F := ![0, 2, 3, 6, 12, 13, 16, 19, 20, 23, 26, 28]

def x0 : Fin 12 → F := ![1, 1, 16, 16, 16, 1, 1, 1, 1, 1, 1, 1]
def x1 : Fin 12 → F := ![16, 16, 25, 25, 7, 7, 23, 7, 16, 16, 16, 25]
def x2 : Fin 12 → F := ![24, 23, 20, 23, 20, 25, 20, 23, 25, 7, 20, 23]

def a0 : Fin 12 → F := ![0, 5, 23, 11, 11, 0, 0, 18, 26, 4, 13, 16]
def a1 : Fin 12 → F := ![0, 13, 28, 26, 14, 22, 28, 19, 4, 14, 28, 24]
def a2 : Fin 12 → F := ![1, 15, 27, 2, 23, 13, 26, 7, 1, 3, 28, 3]

def annihilator : Fin 12 → Fin 4 → F := ![
  ![(22 : F), 18, 17, 1], ![(9 : F), 1, 18, 1], ![(4 : F), 2, 26, 1],
  ![(22 : F), 9, 23, 1], ![(22 : F), 21, 15, 1], ![(28 : F), 4, 25, 1],
  ![(4 : F), 10, 14, 1], ![(13 : F), 17, 27, 1], ![(6 : F), 6, 16, 1],
  ![(4 : F), 19, 5, 1], ![(28 : F), 8, 21, 1], ![(5 : F), 14, 9, 1]]

def dot4 (v w : Fin 4 → F) : F := ∑ i, v i * w i

/-- All twelve advertised line points have explicit three-column representations. -/
theorem twelve_three_column_representations (j : Fin 12) :
    linePoint (gamma j) =
      fun i => a0 j * column (x0 j) i + a1 j * column (x1 j) i +
        a2 j * column (x2 j) i := by
  fin_cases j <;> funext i <;> fin_cases i <;> decide

/-- The listed annihilator kills all three support columns. -/
theorem annihilator_support (j : Fin 12) :
    dot4 (annihilator j) (column (x0 j)) = 0 ∧
      dot4 (annihilator j) (column (x1 j)) = 0 ∧
      dot4 (annihilator j) (column (x2 j)) = 0 := by
  fin_cases j <;> decide

/-- The same annihilator does not kill the line direction, so the whole line is not
contained in the selected three-column span. -/
theorem annihilator_direction_ne_zero (j : Fin 12) :
    dot4 (annihilator j) direction ≠ 0 := by
  fin_cases j <;> decide

/-- The certified proper-incidence numerator exceeds the block length. -/
theorem twelve_gt_seven : 7 < 12 := by omega

end ArkLib.ProximityGap.Frontier.R384GeneralMDSHalfLineBoundRefuted

#print axioms
  ArkLib.ProximityGap.Frontier.R384GeneralMDSHalfLineBoundRefuted.twelve_three_column_representations
#print axioms
  ArkLib.ProximityGap.Frontier.R384GeneralMDSHalfLineBoundRefuted.annihilator_direction_ne_zero
