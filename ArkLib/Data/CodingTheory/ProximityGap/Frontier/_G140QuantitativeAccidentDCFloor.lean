/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G139NoAccidentEntropyObstruction
import Mathlib.Algebra.Order.Chebyshev

/-!
# G140: the quantitative DC floor for unavoidable reduction accidents

G139 proves that eliminating every weight-220 reduction accident is impossible at production
scale.  This file identifies the correct replacement quantity for any finite sum map.

For `f : X → Y`, put

* `N = #X`,
* `q = #Y`, and
* `E = ∑_y #f⁻¹(y)²`.

Cauchy--Schwarz and fiber conservation give `N² ≤ qE`.  Since the diagonal contributes `N`,
the division-free DC-subtracted form is

`N(N-q) ≤ q(E-N)`.

Thus `E-N` is the quantitatively unavoidable collision excess.  Whenever `q < N`, it is strictly
positive.  A viable production theorem must upper-bound this excess near its DC floor; it cannot
set it to zero.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G140QuantitativeAccidentDCFloor

open scoped BigOperators

/-- Cardinality of a fiber of a finite map. -/
abbrev fiberCount {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (y : Y) : ℕ :=
  Fintype.card {x : X // f x = y}

/-- Fiber conservation. -/
theorem sum_fiberCount {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) :
    ∑ y, fiberCount f y = Fintype.card X := by
  calc
    ∑ y, fiberCount f y = Fintype.card (Σ y : Y, {x : X // f x = y}) := by
      simpa using (Fintype.card_sigma (fun y : Y => {x : X // f x = y})).symm
    _ = Fintype.card X := Fintype.card_congr (Equiv.sigmaFiberEquiv f)

/-- Collision energy of a finite map: the sum of squared fiber sizes. -/
def fiberEnergy {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) : ℕ :=
  ∑ y, (fiberCount f y) ^ 2

/-- Cauchy--Schwarz gives the raw DC floor `#X² ≤ #Y · E`. -/
theorem card_sq_le_card_mul_fiberEnergy
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] (f : X → Y) :
    (Fintype.card X) ^ 2 ≤ Fintype.card Y * fiberEnergy f := by
  rw [fiberEnergy, ← sum_fiberCount f]
  simpa using
    (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset Y)) (f := fun y => fiberCount f y))

/-- Every fiber contributes at least its diagonal, hence `#X ≤ E`. -/
theorem card_le_fiberEnergy
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] (f : X → Y) :
    Fintype.card X ≤ fiberEnergy f := by
  rw [fiberEnergy, ← sum_fiberCount f]
  apply Finset.sum_le_sum
  intro y _
  by_cases h : fiberCount f y = 0
  · simp [h]
  · simpa [pow_two] using
      (Nat.le_mul_of_pos_right (fiberCount f y) (Nat.pos_of_ne_zero h))

/-- **Quantitative accident floor.** After subtracting the diagonal, Cauchy--Schwarz becomes
`N(N-q) ≤ q(E-N)`.  This is the natural-number, division-free DC subtraction. -/
theorem dcExcess_floor
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] (f : X → Y) :
    Fintype.card X * (Fintype.card X - Fintype.card Y) ≤
      Fintype.card Y * (fiberEnergy f - Fintype.card X) := by
  have h := card_sq_le_card_mul_fiberEnergy f
  calc
    Fintype.card X * (Fintype.card X - Fintype.card Y) =
        Fintype.card X ^ 2 - Fintype.card Y * Fintype.card X := by
          rw [Nat.mul_sub_left_distrib]
          ring
    _ ≤ Fintype.card Y * fiberEnergy f - Fintype.card Y * Fintype.card X :=
      Nat.sub_le_sub_right h _
    _ = Fintype.card Y * (fiberEnergy f - Fintype.card X) := by
      rw [Nat.mul_sub_left_distrib]

/-- If the source is larger than the target, collision energy strictly exceeds the diagonal. -/
theorem card_lt_fiberEnergy_of_card_lt
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] (f : X → Y)
    (hcard : Fintype.card Y < Fintype.card X) :
    Fintype.card X < fiberEnergy f := by
  by_contra h
  have hE : fiberEnergy f ≤ Fintype.card X := Nat.le_of_not_gt h
  have hdc := card_sq_le_card_mul_fiberEnergy f
  have hmul : Fintype.card Y * fiberEnergy f ≤
      Fintype.card Y * Fintype.card X := Nat.mul_le_mul_left _ hE
  have hpos : 0 < Fintype.card X := lt_of_le_of_lt (Nat.zero_le _) hcard
  have hstrict : Fintype.card Y * Fintype.card X < Fintype.card X ^ 2 := by
    simpa [pow_two, mul_comm] using Nat.mul_lt_mul_of_pos_right hcard hpos
  exact (not_lt_of_ge (hdc.trans hmul)) hstrict

/-- Production subset families already exceed every field of size at most `2^160`. -/
theorem production_subsetFamily_card_gt_fieldCap
    {F : Type*} [Fintype F] (hq : Fintype.card F ≤ 2 ^ 160) :
    Fintype.card F < (2 ^ 29).choose 110 :=
  hq.trans_lt
    ArkLib.ProximityGap.Frontier.G139NoAccidentEntropyObstruction.production_choose_gt_fieldCap

#print axioms card_sq_le_card_mul_fiberEnergy
#print axioms sum_fiberCount
#print axioms card_le_fiberEnergy
#print axioms dcExcess_floor
#print axioms card_lt_fiberEnergy_of_card_lt
#print axioms production_subsetFamily_card_gt_fieldCap

end ArkLib.ProximityGap.Frontier.G140QuantitativeAccidentDCFloor
