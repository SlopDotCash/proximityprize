/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvX_PrimitiveTwoPowRootHalfPowerEq

/-!
# Primitive 2-power roots: half-shifted powers are negatives (#444, AvX)

`_AvX_PrimitiveTwoPowRootHalfPowerEq` proves the half-period hinge
`ζ^(2^k) = -1` for a primitive `2^(k+1)`-th root.  `_AvX_AntipodalPairSumZero`
packages the additive cancellation `ζ^a + ζ^(a+2^k) = 0`.

This file records the equally useful caller-facing multiplicative form:

`ζ^(a + 2^k) = - ζ^a`.

It is a small Lam-Leung / antipodal-balance substrate over a domain.  It is not a finite-field
transfer, BGK proof, CORE closure, or capacity/growth-law claim.
-/

namespace ArkLib.ProximityGap.Frontier

/-- **Half-shift negation.** For a primitive `2^(k+1)`-th root `ζ`, shifting an exponent by
the half-period `2^k` negates the corresponding power: `ζ^(a+2^k) = -ζ^a`. -/
theorem PrimitiveTwoPowRootHalfShiftEqNeg
    {R : Type*} [CommRing R] [NoZeroDivisors R] {ζ : R} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) (a : ℕ) :
    ζ ^ (a + 2 ^ k) = -ζ ^ a := by
  rw [pow_add, PrimitiveTwoPowRootHalfPowerEqNegOne hζ]
  ring

#print axioms PrimitiveTwoPowRootHalfShiftEqNeg

end ArkLib.ProximityGap.Frontier
