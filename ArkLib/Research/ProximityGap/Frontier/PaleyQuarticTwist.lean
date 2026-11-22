/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Split quartic twists in the projective Paley moment

Dividing four linear factors by the last one sends a branch point to infinity.
The first ratio is the new coordinate. The other two ratios are affine functions
of it. Rescaling gives an elliptic cubic with three distinct rational roots.
-/
namespace ProximityGap.PaleyQuarticTwist

variable {K : Type*} [Field K]

/-- Determinant of two homogeneous representatives of projective points. -/
def bracket (u v : K × K) : K := u.1 * v.2 - u.2 * v.1

/-- The two anchor brackets give projective coordinates for every linear factor. -/
theorem bracket_coordinates (u v w t : K × K) :
    bracket u v * bracket w t =
      bracket w v * bracket u t + bracket u w * bracket v t := by
  unfold bracket
  ring

/-- Equality of the two-bracket ratios implies equality of the projective points. -/
theorem ratio_injective (u v s t : K × K) (huv : bracket u v ≠ 0)
    (hs : bracket v s ≠ 0) (ht : bracket v t ≠ 0)
    (h : bracket u s / bracket v s = bracket u t / bracket v t) :
    bracket s t = 0 := by
  apply (mul_eq_zero.mp (show bracket u v * bracket s t = 0 from ?_)).resolve_left huv
  have hc := (div_eq_div_iff hs ht).mp h
  unfold bracket at *
  linear_combination hc

/-- A split four-branch squareclass condition gives a point on the cubic.
Here the fourth linear factor supplied the denominator of the coordinate. -/
theorem twist_point (d a b e f r y : K) (h : d * y ^ 2 = r * (a * r + b) * (e * r + f)) :
    let c := d * a * e
    (c * d * y) ^ 2 = (c * r) * (c * r + d * e * b) * (c * r + d * a * f) := by
  dsimp only
  linear_combination d ^ 3 * a ^ 2 * e ^ 2 * h

/-- The three branch values are distinct when the linear factors are distinct. -/
theorem cubic_roots_distinct {d a b e f : K} (hd : d ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (he : e ≠ 0) (hf : f ≠ 0) (hdet : a * f ≠ b * e) :
    -(d * e * b) ≠ 0 ∧ -(d * a * f) ≠ 0 ∧ -(d * e * b) ≠ -(d * a * f) := by
  refine ⟨neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hd he) hb),
    neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hd ha) hf), ?_⟩
  intro h
  apply hdet
  have h' : d * (a * f) = d * (b * e) := by
    linear_combination h
  exact mul_left_cancel₀ hd h'

#print axioms ratio_injective
#print axioms twist_point
#print axioms cubic_roots_distinct

end ProximityGap.PaleyQuarticTwist
