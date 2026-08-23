/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvX_PrimitiveTwoPowRootHalfPowerEq

/-!
# Primitive 2-power roots: explicit antipodal pair zero-sum (#444, AvX)

The Lam–Leung 2-power lane repeatedly uses the elementary fact that the half-period shift
pairs roots antipodally. `_AvX_PrimitiveTwoPowRootHalfPowerEq` proves the hinge
`ζ^(2^k) = -1` from primitivity. This file packages the caller-facing zero-sum form:

`ζ^a + ζ^(a + 2^k) = 0`.

This is a small algebraic substrate for Lam–Leung / antipodal-balance formalizations only.
It is char-0 / domain algebra, not a char-`p` transfer, BGK proof, CORE closure, or capacity claim.
-/

namespace ArkLib.ProximityGap.Frontier

/-- **Antipodal pair zero-sum.** For a primitive `2^(k+1)`-th root `ζ`, the roots whose exponents
differ by the half-period `2^k` cancel exactly: `ζ^a + ζ^(a+2^k) = 0`. -/
theorem PrimitiveTwoPowRootAntipodalPairSumZero
    {R : Type*} [CommRing R] [NoZeroDivisors R] {ζ : R} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) (a : ℕ) :
    ζ ^ a + ζ ^ (a + 2 ^ k) = 0 := by
  rw [pow_add, PrimitiveTwoPowRootHalfPowerEqNegOne hζ]
  ring

#print axioms PrimitiveTwoPowRootAntipodalPairSumZero

end ArkLib.ProximityGap.Frontier
