/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-! # Quartic invariants at an order-three radial contact

These polynomial identities use ordinary quartic coefficients in ascending
order, including a zero leading coefficient when one root is at infinity.
-/

namespace ProximityGap.QuarticHarmonicInvariants

variable {R : Type*} [CommRing R]

/-- The quadratic binary-quartic invariant in ordinary coordinates. -/
def invariantI (a b c d e : R) : R := 12*e*a - 3*d*b + c^2

/-- The cubic binary-quartic invariant in ordinary coordinates. -/
def invariantJ (a b c d e : R) : R :=
  72*e*c*a + 9*d*c*b - 27*e*b^2 - 27*d^2*a - 2*c^3

/-- Translating the ordinate preserves both invariants. -/
theorem translate (a b c d e t : R) :
    let a' := a+b*t+c*t^2+d*t^3+e*t^4
    let b' := b+2*c*t+3*d*t^2+4*e*t^3
    let c' := c+3*d*t+6*e*t^2
    let d' := d+4*e*t
    invariantI a' b' c' d' e = invariantI a b c d e ∧
    invariantJ a' b' c' d' e = invariantJ a b c d e := by
  dsimp [invariantI, invariantJ]
  constructor <;> ring

/-- At an order-three site, the cubic invariant has a double zero, and the
quadratic invariant has a simple zero; a missing cubic term doubles the latter. -/
theorem local_orders (a b c d e t : R)
    (ha : t^2 ∣ a) (hb : t ∣ b) (hc : t ∣ c) :
    t^2 ∣ invariantJ a b c d e ∧ t ∣ invariantI a b c d e ∧
    (t ∣ d → t^2 ∣ invariantI a b c d e) := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨c, rfl⟩ := hc
  refine ⟨⟨72*e*c*t*a + 9*d*c*b - 27*e*b^2 - 27*d^2*a - 2*t*c^3, ?_⟩,
    ⟨12*e*t*a - 3*d*b + t*c^2, ?_⟩, ?_⟩
  · unfold invariantJ
    ring
  · unfold invariantI
    ring
  · rintro ⟨d, rfl⟩
    exact ⟨12*e*a - 3*d*b + c^2, by unfold invariantI; ring⟩

/-- The chart with simple roots at zero, one, infinity and a cross-ratio. -/
theorem cross_ratio (x : R) :
    invariantI (0:R) x (-(1+x)) 1 0 = 1-x+x^2 ∧
    invariantJ (0:R) x (-(1+x)) 1 0 = (1+x)*(2*x-1)*(x-2) := by
  constructor <;> simp only [invariantI, invariantJ] <;> ring

/-- The Hessian of the harmonic form with fourth roots of unity as zeros. -/
theorem fourth_roots_hessian (x : R) :
    4*(x^4-1)*(12*x^2)-3*(4*x^3)^2 = -48*x^2 := by ring

end ProximityGap.QuarticHarmonicInvariants

#print axioms ProximityGap.QuarticHarmonicInvariants.translate
#print axioms ProximityGap.QuarticHarmonicInvariants.local_orders
#print axioms ProximityGap.QuarticHarmonicInvariants.cross_ratio
#print axioms ProximityGap.QuarticHarmonicInvariants.fourth_roots_hessian
