/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Proximity Prize contributors
-/
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30
import Mathlib.Data.Fin.VecNotation

/-! # Four degree-seven heads on the sixteen fibers of the first sponsor domain

The first sponsor generator and modulus are imported from their certified owner.
The table below gives all pair equalities of the head values on the quotient.
The Hamming allocation and MCA witness construction are in
`docs/research/proximity-gap/rate-half-sixteen-fiber-ceiling.md`.
-/

namespace ProximityGap.RateHalfSixteenFiberClasses

open ArkLib.ProximityGap.PrizeShapePrimeP30 (P g)
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

private abbrev F := ZMod P
private instance : Fact P.Prime := ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

/-- The sixteenth root of unity obtained by taking the quotient of the source domain. -/
def omega : F := g ^ (2 ^ 26 : ℕ)

private abbrev omegaValue : F := 357111556877444407914257742635116754287240874648

theorem omega_eq : omega = omegaValue := by
  unfold omega
  rw [← binaryPow_eq_pow]
  decide

/-- Evaluate the monic polynomial with the indicated quotient roots. -/
def locator (z y : F) (roots : List ℕ) : F :=
  (roots.map fun r => y - z ^ r).prod

def rootsA : List ℕ := [0, 1, 2, 3, 4, 9, 11]
def rootsB : List ℕ := [0, 3, 5, 10, 11, 12, 13]
def rootsC : List ℕ := [1, 4, 5, 9, 12, 13, 14]

def scaleB : F := 125829621549097067457234094028236226857884909488
def scaleC : F := 125829621549097067457234094028236226857884909489

/-- The two constants implement the degree-seven normalizations in the construction. -/
theorem normalization_constants :
    scaleB = locator omega (omega ^ 6) rootsA / locator omega (omega ^ 6) rootsB ∧
    scaleC = locator omega (omega ^ 7) rootsA / locator omega (omega ^ 7) rootsC := by
  rw [omega_eq]
  constructor
  · apply (eq_div_iff (by decide : locator omegaValue (omegaValue ^ 6) rootsB ≠ 0)).2
    decide
  · apply (eq_div_iff (by decide : locator omegaValue (omegaValue ^ 7) rootsC ≠ 0)).2
    decide

/-- Univariate evaluations of the four heads on the quotient. -/
def head (z : F) (i : Fin 4) (y : F) : F :=
  ![0, locator z y rootsA, scaleB * locator z y rootsB, scaleC * locator z y rootsC] i

/-- Labels of the classes at each fiber, in head order 0, 1, 2, 3. -/
def classID (j : Fin 16) : Fin 4 → Nat :=
  ![![0,0,0,3], ![0,0,2,0], ![0,0,2,2], ![0,0,0,3],
    ![0,0,2,0], ![0,1,0,0], ![0,1,1,3], ![0,1,1,1],
    ![0,1,1,1], ![0,0,2,0], ![0,1,0,1], ![0,0,0,3],
    ![0,1,0,0], ![0,1,0,0], ![0,1,2,0], ![0,1,1,1]] j

/-- The complete equality-class table at the literal first prime. -/
theorem equality_class_table :
    ∀ (j : Fin 16) (i k : Fin 4),
      head omega i (omega ^ j.val) = head omega k (omega ^ j.val) ↔
      classID j i = classID j k := by
  rw [omega_eq]
  decide

#print axioms omega_eq
#print axioms normalization_constants
#print axioms equality_class_table

end ProximityGap.RateHalfSixteenFiberClasses
