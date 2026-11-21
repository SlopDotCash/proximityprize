/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-! # Quartic and elliptic equations for four signed triangle minors -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.QuarterQuarticPrym

/-- A normalization of the Vinberg quartic adapted to its two elliptic projections.
The five identities are polynomial and so apply before choosing an affine chart. -/
theorem elliptic_forms {R : Type*} [CommRing R] (a b c w : R)
    (hw : w ^ 4 = a * b * c * (a + b + c)) :
    (b + c) ^ 2 - (b - c) ^ 2 = 4 * b * c ∧
    (b + c + 2 * a) ^ 2 - (b + c) ^ 2 = 4 * a * (a + b + c) ∧
    (2 * w) ^ 4 = (4 * b * c) * (4 * a * (a + b + c)) ∧
    (b + c) + (b - c) = 2 * b ∧ (b + c) - (b - c) = 2 * c := by
  refine ⟨by ring, by ring, ?_, by ring, by ring⟩
  linear_combination 16 * hw

/-- Riemann–Hurwitz with inertia two at the cross sites and the two points
above each additional odd pole. -/
theorem cover_genus (d m r g : ℤ)
    (h : 2 * g - 2 = 4 * (4 * d - 4) + 2 * (2 * (d + m) + 2 * r)) :
    g = 10 * d + 2 * m + 2 * r - 7 := by omega

#print axioms elliptic_forms
#print axioms cover_genus

end ArkLib.ProximityGap.Frontier.QuarterQuarticPrym
