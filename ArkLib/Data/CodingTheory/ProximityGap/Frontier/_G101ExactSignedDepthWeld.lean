/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G96DepthMomentWeld
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G100PerDepthCenteringCancellation

/-!
# G101: exact signed-depth formulation of the DC energy wall

G96 welds maximal-cancellation depth fibers to `DCEnergyBound`, using nonnegative per-depth caps
as a sufficient localized consumer.  G100 shows those caps lose cancellation between depths.
This file supplies the lossless replacement on the actual prize objects.

At depth `s`, define the signed anomaly

```text
q * (equal-sum pairs at depth s) - (all pairs at depth s).
```

The sum of these integer anomalies is exactly `q * rEnergy - #G^(2r)`.  Consequently
`DCEnergyBound` is equivalent to bounding their signed sum by `q * Wick`.  Negative depth
anomalies remain available to cancel positive ones; no positive-part or per-depth loss occurs.

This is an exact reformulation, not an estimate.  Proving the signed-sum bound at production depth
remains the BGK/Paley wall.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G101ExactSignedDepthWeld

open Finset Fintype
open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G96DepthMomentWeld
open ArkLib.ProximityGap.Frontier.G100PerDepthCenteringCancellation

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The genuine signed DC anomaly carried by one maximal-cancellation depth. -/
def actualDepthAnomaly (G : Finset F) (r s : ℕ) : ℤ :=
  depthAnomaly (Fintype.card F) (depthFiber G r s) (allPairsDepthFiber G r s)

/-- **Exact signed depth decomposition.** The sum of actual depth anomalies is the global
DC-subtracted additive-energy numerator. -/
theorem sum_actualDepthAnomaly (G : Finset F) (r : ℕ) :
    ∑ s ∈ Finset.range (r + 1), actualDepthAnomaly G r s =
      (Fintype.card F : ℤ) * rEnergy G r - (G.card : ℤ) ^ (2 * r) := by
  unfold actualDepthAnomaly
  rw [sum_depthAnomaly,
    ← rEnergy_eq_sum_depthFiber, sum_allPairsDepthFiber]
  push_cast
  rfl

/-- **Lossless signed-depth wall.** `DCEnergyBound` is equivalent to a single bound on the signed
sum of maximal-cancellation depth anomalies.  Unlike G96's nonnegative per-depth caps, this iff
retains cancellation between depths exactly. -/
theorem dcEnergyBound_iff_sum_actualDepthAnomaly_le
    (G : Finset F) (r : ℕ) :
    DCEnergyBound G r ↔
      ∑ s ∈ Finset.range (r + 1), actualDepthAnomaly G r s ≤
        (Fintype.card F : ℤ) *
          (Nat.doubleFactorial (2 * r - 1) * G.card ^ r) := by
  rw [sum_actualDepthAnomaly, sub_le_iff_le_add, dcEnergyBound_iff_nat]
  norm_cast

/-- A signed-depth estimate with the exact Wick right-hand side closes the DC energy hypothesis
without allocating any nonnegative per-depth caps. -/
theorem dcEnergyBound_of_signedDepthSum
    (G : Finset F) (r : ℕ)
    (h : ∑ s ∈ Finset.range (r + 1), actualDepthAnomaly G r s ≤
      (Fintype.card F : ℤ) *
        (Nat.doubleFactorial (2 * r - 1) * G.card ^ r)) :
    DCEnergyBound G r :=
  (dcEnergyBound_iff_sum_actualDepthAnomaly_le G r).2 h

end ArkLib.ProximityGap.Frontier.G101ExactSignedDepthWeld

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G101ExactSignedDepthWeld.sum_actualDepthAnomaly
#print axioms
  ArkLib.ProximityGap.Frontier.G101ExactSignedDepthWeld.dcEnergyBound_iff_sum_actualDepthAnomaly_le
#print axioms
  ArkLib.ProximityGap.Frontier.G101ExactSignedDepthWeld.dcEnergyBound_of_signedDepthSum
