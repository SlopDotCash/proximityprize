/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Half-radius conic secant boundary identities

For the affine conic column `v(t) = (1,t,t^2)`, these identities parameterize the
infinite boundary counterexample mechanism on the tangent line `Z=0`. Given
`s != 0` with `s^2 != 1`, every nonzero affine tangent point has a uniform
two-column certificate; in odd characteristic the point at infinity does as well.

This module supplies only the field-generic algebraic core. It deliberately does
not assert that a finite field contains a suitable `s`; that cardinality step is
left to finite-field consumers.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.HalfRadiusConicSecantBoundaryFamily

variable {F : Type*} [Field F]

def column (t : F) : Fin 3 → F := fun j => t ^ (j : Nat)

def tangentPoint (r : F) : Fin 3 → F := fun j =>
  if j = 0 then 1 else if j = 1 then r else 0

def tangentInfinity : Fin 3 → F := fun j => if j = 1 then 1 else 0

def chordLeftCoeff (s : F) : F := -(s ^ 2 - 1)⁻¹

def chordRightCoeff (s : F) : F := s ^ 2 * (s ^ 2 - 1)⁻¹

/-- One fixed `s` supplies a linear-combination identity for every affine tangent point. -/
theorem tangentPoint_eq_secant (r s : F) (hs0 : s ≠ 0)
    (hs1 : s ^ 2 ≠ 1) :
    tangentPoint r =
      chordLeftCoeff s • column (r * (1 + s)) +
        chordRightCoeff s • column (r * (1 + s⁻¹)) := by
  have hden : s ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hs1
  funext j
  fin_cases j <;>
    simp [tangentPoint, column, chordLeftCoeff, chordRightCoeff] <;>
    field_simp [hs0, hden] <;> ring

/-- For nonzero `r`, the two endpoints in `tangentPoint_eq_secant` are distinct. -/
theorem tangentPoint_secant_endpoints_ne (r s : F) (hr : r ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ^ 2 ≠ 1) :
    r * (1 + s) ≠ r * (1 + s⁻¹) := by
  intro h
  have hsum : 1 + s = 1 + s⁻¹ := mul_left_cancel₀ hr h
  have hsInv : s = s⁻¹ := add_left_cancel hsum
  apply hs1
  calc
    s ^ 2 = s * s := pow_two s
    _ = s * s⁻¹ := congrArg (fun z => s * z) hsInv
    _ = 1 := mul_inv_cancel₀ hs0

/-- The affine tangent point at parameter zero is the evaluated conic column `v(0)`. -/
theorem tangentPoint_zero : tangentPoint (0 : F) = column 0 := by
  funext j
  fin_cases j <;> simp [tangentPoint, column]

/-- In odd characteristic, the tangent-line point at infinity lies on the secant through
`v(t)` and `v(-t)`. -/
theorem tangentInfinity_eq_secant (t : F) (ht : t ≠ 0)
    (htwo : (2 : F) ≠ 0) :
    tangentInfinity =
      (2 * t)⁻¹ • column t + (-(2 * t)⁻¹) • column (-t) := by
  funext j
  fin_cases j <;>
    simp [tangentInfinity, column] <;>
    field_simp [ht, htwo] <;> ring

/-- The two endpoints in the infinity certificate are distinct in odd characteristic. -/
theorem tangentInfinity_secant_endpoints_ne (t : F) (ht : t ≠ 0)
    (htwo : (2 : F) ≠ 0) : t ≠ -t := by
  intro h
  apply ht
  apply mul_left_cancel₀ htwo
  linear_combination h

/-- The tangent line contains at most one affine conic column, so it cannot be a support
secant through two distinct evaluated columns. -/
theorem columns_on_tangent_imply_eq (x y : F)
    (hx : column x 2 = 0) (hy : column y 2 = 0) : x = y := by
  have hx0 : x = 0 := by
    simpa [column, pow_two] using
      (mul_self_eq_zero.mp (by simpa [column, pow_two] using hx))
  have hy0 : y = 0 := by
    simpa [column, pow_two] using
      (mul_self_eq_zero.mp (by simpa [column, pow_two] using hy))
  rw [hx0, hy0]

/-- The affine-conic family `(n,k,e) = (q,q-3,2)` lies on `e+k+1=n`. -/
theorem conic_family_numerics (q : Nat) (hq : 5 ≤ q) :
    2 * 2 < q ∧ 2 + (q - 3) + 1 = q := by
  omega

end ArkLib.ProximityGap.Frontier.HalfRadiusConicSecantBoundaryFamily

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms
  ArkLib.ProximityGap.Frontier.HalfRadiusConicSecantBoundaryFamily.tangentPoint_eq_secant
#print axioms
  ArkLib.ProximityGap.Frontier.HalfRadiusConicSecantBoundaryFamily.tangentInfinity_eq_secant
