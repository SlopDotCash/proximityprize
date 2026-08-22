/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2W4CyclotomicNonCollision
import Mathlib.Tactic.NormNum

/-!
# Finite-field discharge of `Cd₀NonCollisionModSign μ_n` (concrete `(n, p)` instances)

The complex version `invariantPairNonCollision_complex_primitive_zeta_sq` is already proven in the
core file. Over a finite field `F_p` the sign-quotiented non-collision residual
`Cd₀NonCollisionModSign (nthRootsFinset n 1)` is *not* a uniform theorem: it fails at the bad
primes catalogued in the core (`not_cd0NonCollisionModSign_of_e2BadScalarSet_…`). Here we bank
the *positive* side at concrete good `(n, p)` pairs where no sign-distinct invariant collision
exists, by a finite `decide`-style exclusion over the explicit root set.

`Cd₀NonCollisionModSign G` says: for `t, t' ∈ G` with `c = t + t⁻¹ ≠ 0`, `c' = t' + t'⁻¹ ≠ 0`,
`c ≠ c'`, and `c ≠ -c'` (so distinct even after the antipodal `t ↦ -t` collapse), there is no
`u ∈ G` with `c' = u·c`. The scanner-failure surface `not_cd0NonCollisionModSign_of_collision`
refutes it from one concrete collision; the certificate `cd0NonCollisionModSign_of_no_collision`
proves it from the absence of any collision. We feed the latter the finite-field
`nthRootsFinset n 1 = univ.filter (·^n = 1)`, which makes the existential decidable over the
fintype `ZMod p`.

## Honesty / scope

These are **off-wall** substrate witnesses. The δ* core is the recognized-open BGK/Paley wall
`M(μ_n) ≤ C·√(n log(p/n))` at `β ≈ 4`; nothing here pins `δ*`. Each concrete instance is
*necessary-not-sufficient*: it confirms the repaired residual's positive side at a small good
prime, but says nothing about the asymptotic regime or the worst-case incomplete-sum bound. The
good primes here (`p = 17` for `n = 8`, `p = 97` for `n = 16`) lie in the benign Linnik
least-prime family, not the high-`v₂(p-1)` ceiling-bad family.
-/

set_option autoImplicit false
set_option maxRecDepth 262144

namespace ArkLib.ProximityGap.E2W4CyclotomicNonCollision

open Polynomial

local instance fact_prime_17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The `8`-th roots of unity over `ZMod 17` as an explicit decidable filter. -/
theorem nthRootsFinset_eq_filter_zmod17_8 :
    nthRootsFinset 8 (1 : ZMod 17) = Finset.univ.filter (fun x => x ^ 8 = 1) := by
  ext x
  rw [mem_nthRootsFinset (by norm_num : 0 < 8), Finset.mem_filter]
  simp

/-- A concrete finite-field mod-sign non-collision certificate for the `n = 8`, `p = 17` root
set.  This is a tiny sanity witness for the E2/W4 finite-field obstruction lane. -/
theorem cd0_modsign_mu8_zmod17 :
    Cd₀NonCollisionModSign (nthRootsFinset 8 (1 : ZMod 17)) := by
  apply cd0NonCollisionModSign_of_no_collision
  rw [nthRootsFinset_eq_filter_zmod17_8]
  decide

local instance fact_prime_97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- nthRootsFinset for n=16 over ZMod 97 as an explicit decidable filter. -/
theorem nthRootsFinset_eq_filter_zmod97_16 :
    nthRootsFinset 16 (1 : ZMod 97) = Finset.univ.filter (fun x => x ^ 16 = 1) := by
  ext x
  rw [mem_nthRootsFinset (by norm_num : 0 < 16), Finset.mem_filter]
  simp

/-- Sign-quotiented width-4 cyclotomic non-collision holds concretely at `(n, p) = (16, 97)`. -/
theorem cd0_modsign_mu16_zmod97 :
    Cd₀NonCollisionModSign (nthRootsFinset 16 (1 : ZMod 97)) := by
  apply cd0NonCollisionModSign_of_no_collision
  rw [nthRootsFinset_eq_filter_zmod97_16]
  decide

end ArkLib.ProximityGap.E2W4CyclotomicNonCollision

#print axioms ArkLib.ProximityGap.E2W4CyclotomicNonCollision.cd0_modsign_mu8_zmod17
#print axioms ArkLib.ProximityGap.E2W4CyclotomicNonCollision.cd0_modsign_mu16_zmod97
