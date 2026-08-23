/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RigidityIterated2kLift

/-!
# Bounded-coefficient cyclotomic independence — the precise char-p prize core (#407)

Tracing the moment ladder to its root: in **char-0**, `HalfBasisIndepZ ζ (2^{m-1})` (no nonzero integer
relation among the half-basis powers) is proven from `minpoly ℚ ζ = Φ_{2^m}`
(`halfBasisIndepZ_of_primitiveRoot`), and the GENERAL antipodal-structure results
(`antipodallyClosed_of_disjoint_equal_sum`) then give every `RepK` ⟹ every Wick energy bound. So the
entire ladder is char-0-proven; the prize is purely a **char-p** phenomenon.

But `HalfBasisIndepZ` is **always false in char-p** (take `g = (p,0,…)`: `p·ζ⁰ = 0`). The rigidity chain
only ever uses **bounded** coefficients (a `k`-tuple of roots gives a relation of support `≤ k` and
`|g_j| ≤ k`). Hence the precise char-p object:

> **`BoundedHalfBasisIndep ζ N C`** := no nonzero `g ∈ [−C,C]^N` with `∑_j g_j ζ^j = 0`.

This CAN hold in char-`p` above a threshold (the r=2 instance `C=2` is the landed
`sidonModNeg_rootsOfUnity_improved` at `p > 12^{φ(n)}`). **The prize is exactly
`BoundedHalfBasisIndep ω (2^{m-1}) C` mod the prize prime `p ~ n⁴` for support `C ~ 2 ln q`** — above the
reachable threshold, where it can fail = BGK. This file names it and discharges the char-0 side.

Issue #407.
-/

open Round29IteratedLift

namespace ArkLib.ProximityGap.BoundedCyclotomicIndep

variable {F : Type*} [Field F]

/-- **Bounded-coefficient half-basis independence (`HBIᵦ`).** No nonzero integer relation with
coefficients in `[−C, C]` among the half-basis powers `1, ζ, …, ζ^{N-1}`. The precise char-`p` object
the prize turns on: unlike the unbounded `HalfBasisIndepZ` (always false in char-`p`), this can hold
above a support-dependent prime threshold. -/
def BoundedHalfBasisIndep (ζ : F) (N C : ℕ) : Prop :=
  ∀ g : Fin N → ℤ, (∀ j, (g j).natAbs ≤ C) →
    (∑ j : Fin N, (g j : F) * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0

/-- The bounded version is **weaker** than unbounded integer independence: drop the coefficient bound. -/
theorem boundedHalfBasisIndep_of_halfBasisIndepZ {ζ : F} {N : ℕ} (C : ℕ)
    (h : HalfBasisIndepZ ζ N) : BoundedHalfBasisIndep ζ N C :=
  fun g _ hsum j => h g hsum j

/-- **Char-0 discharge.** For a primitive `2^m`-th root in a characteristic-0 field, bounded-coefficient
half-basis independence holds at **every** bound `C` (it is implied by the unbounded cyclotomic
independence). The prize is whether this survives the transfer to char-`p` at the prize prime for
`C ~ 2 ln q` — the open BGK core. -/
theorem boundedHalfBasisIndep_of_primitiveRoot [CharZero F] {m : ℕ} (hm : 1 ≤ m) (C : ℕ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) : BoundedHalfBasisIndep ζ (2 ^ (m - 1)) C :=
  boundedHalfBasisIndep_of_halfBasisIndepZ C (halfBasisIndepZ_of_primitiveRoot hm hζ)

end ArkLib.ProximityGap.BoundedCyclotomicIndep
#print axioms ArkLib.ProximityGap.BoundedCyclotomicIndep.boundedHalfBasisIndep_of_primitiveRoot
