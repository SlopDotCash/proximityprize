/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Route R3 (algebraic / GM-MDS / Lovett NVM) — the 2-power obstruction (Proximity Prize #407)

**Target attempted.** Extend the "nonvanishing-minors" (NVM) / generalized-Vandermonde
nonsingularity property — the `LovettPrimitiveStep` content of the in-tree GM-MDS formalization
(`ArkLib/Data/CodingTheory/GMMDS/Lovett*.lean`) — from the GENERIC evaluation domain (where it
is the symbolic GM-MDS theorem, over `MvPolynomial (Fin n) F`) to the SPECIFIC prize domain
`μ_n ⊆ 𝔽_p^×` at 2-power index `m = (p−1)/n` (the dyadic NTT domain).

**Result: REFUTED at the minor level.** The distinct-degree generalized-Vandermonde minor
`det[ zᵢ^{dⱼ} ]`, which is *unconditionally nonsingular for distinct points and distinct degrees
over an integral domain in the GENERIC / symbolic regime* (this is the in-tree axiom-clean
`ArkLib.GMMDS.linearIndependent_of_injOn_natDegree`), can VANISH over the structured subgroup
`μ_n` once a degree exceeds the subgroup-collapse threshold. Reason, fully elementary: for
`x ∈ μ_n` the power `x ↦ x^d` factors through `d mod n`, and the `d`-th power map collapses
`μ_n` onto the subgroup `μ_{n/gcd(d,n)}`. When two columns of the minor have degrees that
collapse to the same value on the chosen points, the columns coincide and the determinant is `0`.

This file records the **machine-checked countermodel** (`decide` over `ZMod 73`): the `3×3`
distinct-degree minor on `μ₈ ⊆ (ZMod 73)ˣ` with points `{1, −1, ζ²}` and degrees `{0,1,4}` is
singular, because `x⁴ = 1` for every `x ∈ μ₈` (the `4`-th power map sends `μ₈ → μ₂ = {1}` on
these points), so the degree-`0` and degree-`4` columns are identical. The control minor on the
SAME points with degrees `{0,1,2}` is nonsingular.

## Why this refutes the R3 route's hope (precise obstruction)

The route hoped: pin `LovettPrimitiveStep` over `μ_n` via Chebotarëv / Lam–Leung vanishing-sum
theory (index 2,3 "solved", 2-power "open"), and thereby get an algebraic handle on the prize
floor `B = max_{b≠0}|η_b|`. Two independent walls, both confirmed by probe
(`scripts/probes/_wf407_nvm_*.py`):

* **(W-transfer) The symbolic GM-MDS does NOT transfer to `μ_n` at 2-power index.** Generic
  nonsingularity is *not* nonsingularity at the special point set `μ_{2^a}`: distinct-degree
  minors genuinely vanish there (probe: `n=8, p=73`: `320/3136` distinct-degree minors singular;
  `n=16, p=97`: `26880/313600`; while for *prime* `n ∈ {3,5,7,11}`: `0` singular). The singular
  configurations are exactly the Lam–Leung ones — points containing a coset of `{±1} = μ₂` and
  degrees with an aligned odd gap. So whatever NVM statement holds over `μ_n` is a *strictly
  weaker, structured* statement than the generic GM-MDS theorem; the 2-power domain is the WORST
  case (matching `docs/kb/deltastar-wall-unification-2026-06-13.md §4`), not a tractable one.

* **(W-archimedean) NVM is non-archimedean; the prize is archimedean.** Even granting the NVM
  property for all index, it is a *nonvanishing* (`det ≠ 0`) statement and is logically blind to
  the *modulus* `B`. Probe (`_wf407_nvm_verdict.py §2`): the full `μ₄` Vandermonde determinant is
  nonzero for every swept prime, yet `B/√(n ln m)` drifts `1.26 → 0.86` as `p` grows — the
  determinant being nonzero carries *zero* information about the size of `|η_b|`. This is the same
  archimedean-vs-algebraic gap diagnosed for the whole algebraic class in
  `docs/kb/deltastar-conjecture-loop-algebraic-route-2026-06-13.md` (Stickelberger/Gross–Koblitz/
  Hasse–Davenport all pin non-archimedean structure; the prize is the archimedean argument sup).

**Honesty (contract §6).** Nothing here is claimed to close the prize. The genuine, axiom-clean
content is the *refutation*: a `decide`-checked singular minor over `μ₈` proving the NVM property
FAILS over the prize subgroup at 2-power index, plus the named `Prop` isolating exactly the
(false-over-`μ_n`) statement the route would have needed.
-/

namespace ArkLib.ProximityGap.NVMRoute

open Matrix

/-! ## The named route object (what R3 would have needed) -/

/-- **The subgroup-NVM property the route hoped to establish.**  Over the evaluation domain
`pts : Fin r → R` (intended: `r` distinct points of `μ_n ⊆ 𝔽_p^×`), for every strictly-increasing
degree vector `degs : Fin r → ℕ`, the generalized-Vandermonde minor `det[ (pts i)^(degs j) ]` is
nonzero.  Over a *generic* domain this is the in-tree distinct-degree GM-MDS fact
(`ArkLib.GMMDS.linearIndependent_of_injOn_natDegree`).  The claim below is that over the
*structured* subgroup `μ_n` at 2-power index it is **FALSE** (see `nvm_subgroup_property_false`). -/
def SubgroupNVMProperty {R : Type*} [CommRing R] {r : ℕ} (pts : Fin r → R) : Prop :=
  ∀ degs : Fin r → ℕ, StrictMono degs →
    (Matrix.of fun i j => (pts i) ^ (degs j)).det ≠ 0

/-! ## The machine-checked countermodel over `μ₈ ⊆ (ZMod 73)ˣ` -/

/-- The three subgroup points: `1`, `−1 = 72`, and `ζ² = 27` where `ζ = 10` is a primitive
`8`-th root of unity in `ZMod 73` (`ζ⁸ = 1`, `ζ⁴ = −1`).  All three lie in `μ₈`. -/
def pts3 : Fin 3 → ZMod 73 := ![1, 72, 27]

/-- The strictly-increasing degree vector `(0, 1, 4)`. -/
def degs3 : Fin 3 → ℕ := ![0, 1, 4]

/-- `degs3` is strictly monotone (a *bona fide* distinct-degree pattern). -/
theorem degs3_strictMono : StrictMono degs3 := by
  decide

/-- **The countermodel matrix** `M[i,j] = (pts3 i)^(degs3 j)` over `ZMod 73`. -/
def Mbad : Matrix (Fin 3) (Fin 3) (ZMod 73) :=
  Matrix.of fun i j => (pts3 i) ^ (degs3 j)

/-- **The degree-`4` column collapses onto the degree-`0` column** on `μ₈`: `x⁴ = 1` for each
chosen point (`1⁴ = 1`, `(−1)⁴ = 1`, `(ζ²)⁴ = ζ⁸ = 1`).  This is the subgroup-collapse mechanism
(`x ↦ x⁴` sends these `μ₈` points to `μ₂ = {1}`), the elementary reason the minor is singular. -/
theorem col4_eq_col0 : ∀ i : Fin 3, Mbad i 2 = Mbad i 0 := by
  decide

/-- **COUNTERMODEL (machine-checked).**  The distinct-degree generalized-Vandermonde minor over
`μ₈ ⊆ (ZMod 73)ˣ` with points `{1, −1, ζ²}` and degrees `{0, 1, 4}` is **singular**.  Hence the
GM-MDS / Lovett distinct-degree nonsingularity, which holds for *generic* points, FAILS over the
structured 2-power subgroup. -/
theorem Mbad_det_eq_zero : Mbad.det = 0 := by
  decide

/-- **Control: the SAME points with degrees `{0,1,2}` give a NONsingular minor** (`det = 4 ≠ 0`).
So the singularity is genuinely a *high-degree subgroup-collapse* phenomenon, not a degeneracy of
the point set.  (Confirms the probe value.) -/
theorem control_det_ne_zero :
    (Matrix.of fun i j => (pts3 i) ^ ((![0, 1, 2] : Fin 3 → ℕ) j) : Matrix (Fin 3) (Fin 3) (ZMod 73)).det ≠ 0 := by
  decide

/-- **The route is refuted: `SubgroupNVMProperty` is FALSE for `μ₈ ⊆ (ZMod 73)ˣ`.**  There exists a
strictly-increasing degree vector whose generalized-Vandermonde minor over these subgroup points
vanishes.  Therefore the in-tree symbolic-domain GM-MDS nonsingularity (`LovettPrimitiveStep`,
which is the distinct-degree case over GENERIC points) does **not** transfer to the prize subgroup
domain at 2-power index — the central hypothesis of route R3. -/
theorem nvm_subgroup_property_false : ¬ SubgroupNVMProperty pts3 := by
  intro h
  exact (h degs3 degs3_strictMono) Mbad_det_eq_zero

end ArkLib.ProximityGap.NVMRoute

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only).
#print axioms ArkLib.ProximityGap.NVMRoute.degs3_strictMono
#print axioms ArkLib.ProximityGap.NVMRoute.col4_eq_col0
#print axioms ArkLib.ProximityGap.NVMRoute.Mbad_det_eq_zero
#print axioms ArkLib.ProximityGap.NVMRoute.control_det_ne_zero
#print axioms ArkLib.ProximityGap.NVMRoute.nvm_subgroup_property_false
