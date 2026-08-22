/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G125DisjointSectorIsolation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G96DepthMomentWeld

/-!
# G126: the disjoint-census gate — `DCEnergyBound` from one census hypothesis

Routing G125's isolation through G96's weld: `DCEnergyBound G r` holds at any prime as soon
as the fully-disjoint equal-sum census, PLUS the explicit descent overhead, fits the DC mass
plus the Wick budget:

```text
q · (depthFiber G r r + Σ_{s<r} (r)_{r−s}²·#G^{r−s}·E_s(G))
    ≤ q · (2r−1)!!·#G^r + #G^(2r)
    ⟹  DCEnergyBound G r.
```

After nine landings of connective tissue, the production prize hypothesis is consumable from
a SINGLE census statement about fully-disjoint equal-sum pairs — the descent overhead is a
concrete number computable from lower-rung energies.  Combined with the post-counterexample
regime (uniform laws dead), this is the correct per-prime gate shape: each certified prime
gets its own census obligation, nothing else.

**Honest scope.**  The gate hypothesis at production scale IS the wall (disjoint-support
cancellation); no claim it holds.  CORE remains OPEN.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G126DisjointCensusGate

open Finset Fintype
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G96DepthMomentWeld
open ArkLib.ProximityGap.Frontier.G125DisjointSectorIsolation
open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The explicit descent overhead of the rung-`r` census: everything below full depth,
bounded by lower-rung energies with kernel constants. -/
noncomputable def descentOverhead (G : Finset F) (r : ℕ) : ℕ :=
  ∑ s ∈ Finset.range r,
    (r.descFactorial (r - s)) ^ 2 * (G.card ^ (r - s) * Finset.addREnergy s G)

/-- **The disjoint-census gate.**  If the fully-disjoint equal-sum census plus the descent
overhead fits the Wick budget plus the DC mass, `DCEnergyBound G r` holds. -/
theorem dcEnergyBound_of_disjoint_census (G : Finset F) (r : ℕ)
    (hcensus : Fintype.card F * (depthFiber G r r + descentOverhead G r)
      ≤ Fintype.card F * (Nat.doubleFactorial (2 * r - 1) * G.card ^ r)
          + G.card ^ (2 * r)) :
    DCEnergyBound G r := by
  rw [dcEnergyBound_iff_nat]
  calc
    Fintype.card F * rEnergy G r
        = Fintype.card F * Finset.addREnergy r G := by
      rw [rEnergy_eq_addREnergy]
    _ ≤ Fintype.card F * (depthFiber G r r + descentOverhead G r) :=
      Nat.mul_le_mul_left _ (addREnergy_le_disjoint_add_descent G r)
    _ ≤ Fintype.card F * (Nat.doubleFactorial (2 * r - 1) * G.card ^ r)
          + G.card ^ (2 * r) := hcensus

end ArkLib.ProximityGap.Frontier.G126DisjointCensusGate

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G126DisjointCensusGate.dcEnergyBound_of_disjoint_census
