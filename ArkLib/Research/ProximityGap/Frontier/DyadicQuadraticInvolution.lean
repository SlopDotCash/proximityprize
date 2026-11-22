/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-! # The trace-zero involution of a symmetric triple -/

namespace ProximityGap.DyadicQuadraticInvolution

variable {K : Type*} [Field K]

/-- Signed determinant of the trace-zero matrix through the three symmetric pairs. -/
theorem determinant (u v w : K) :
    (u*v*w)^2+(-(u+v+w)*(u*v*w))*(u*v+v*w+w*u) =
    -(u*v*w)*(u+v)*(u+w)*(v+w) := by ring

/-- The trace-zero matrix with diagonal coefficient `u*v*w`, upper right coefficient
`-(u+v+w)*u*v*w` and lower left coefficient `u*v+v*w+w*u` exchanges all three
pairs whenever the heads are nonzero and no two heads are antipodal. -/
theorem exchanges {u v w : K} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : u+v ≠ 0) (huw : u+w ≠ 0) (hvw : v+w ≠ 0) :
    let a := u*v*w
    let b := -(u+v+w)*a
    let c := u*v+v*w+w*u
    a^2+b*c ≠ 0 ∧
    c*u*(-(v*w)/u)-a*(u+(-(v*w)/u)) = b ∧
    c*v*(-(u*w)/v)-a*(v+(-(u*w)/v)) = b ∧
    c*w*(-(u*v)/w)-a*(w+(-(u*v)/w)) = b := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [determinant]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero hu hv) hw)) huv) huw) hvw
  all_goals field_simp <;> ring

end ProximityGap.DyadicQuadraticInvolution

#print axioms ProximityGap.DyadicQuadraticInvolution.exchanges
