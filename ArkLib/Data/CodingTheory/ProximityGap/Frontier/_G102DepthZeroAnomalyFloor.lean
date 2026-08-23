/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G101ExactSignedDepthWeld

/-!
# G102: depth zero is the deterministic positive anomaly floor

G101 expresses the DC wall as a signed sum over maximal-cancellation depths.  This file pins the
sign of the fully cancelled depth.  Cancellation depth zero means the two endpoint value
multisets are identical, hence their additive sums agree automatically.  Therefore every
population pair at depth zero lies in the equal-sum fiber.

It follows that the depth-zero anomaly is exactly

```text
(#F - 1) * allPairsDepthFiber G r 0,
```

and is nonnegative.  Cross-depth cancellation can only come from depths `s >= 1`; depth zero is
the unavoidable diagonal/Wick floor.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G102DepthZeroAnomalyFloor

open Finset Fintype
open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G96DepthMomentWeld
open ArkLib.ProximityGap.Frontier.G101ExactSignedDepthWeld

/-- Zero maximal-cancellation depth forces equality of the two endpoint value multisets. -/
theorem valueBag_eq_of_cancelDepth_eq_zero
    {α : Type*} [DecidableEq α] {r : ℕ}
    (x : (Fin r → α) × (Fin r → α)) (hzero : cancelDepth x = 0) :
    valueBag x.1 = valueBag x.2 := by
  unfold cancelDepth at hzero
  have hcore : leftCore (valueBag x.1) (valueBag x.2) = 0 :=
    Multiset.card_eq_zero.mp hzero
  have hcard : (valueBag x.1).card = (valueBag x.2).card := by simp [valueBag]
  have hrightCard := core_card_eq hcard
  rw [hzero] at hrightCard
  have hright : rightCore (valueBag x.1) (valueBag x.2) = 0 :=
    Multiset.card_eq_zero.mp hrightCard.symm
  have hl := left_reconstruct (valueBag x.1) (valueBag x.2)
  have hr := right_reconstruct (valueBag x.1) (valueBag x.2)
  rw [hcore, zero_add] at hl
  rw [hright, zero_add] at hr
  exact hl.symm.trans hr

/-- Consequently a depth-zero endpoint pair has equal additive sums. -/
theorem sum_eq_of_cancelDepth_eq_zero
    {α : Type*} [AddCommMonoid α] [DecidableEq α] {r : ℕ}
    (x : (Fin r → α) × (Fin r → α)) (hzero : cancelDepth x = 0) :
    ∑ i, x.1 i = ∑ i, x.2 i := by
  have hbag := congrArg Multiset.sum (valueBag_eq_of_cancelDepth_eq_zero x hzero)
  simpa [valueBag, List.sum_ofFn] using hbag

/-- **Depth-zero fiber identity.** Every population pair at cancellation depth zero is already an
equal-sum pair, so the energy and population fibers coincide exactly. -/
theorem depthFiber_zero_eq_allPairsDepthFiber
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (r : ℕ) :
    depthFiber G r 0 = allPairsDepthFiber G r 0 := by
  classical
  unfold depthFiber allPairsDepthFiber energySet
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨hleft, hright⟩, _hsum⟩, hdepth⟩
    exact ⟨⟨hleft, hright⟩, hdepth⟩
  · rintro ⟨⟨hleft, hright⟩, hdepth⟩
    exact ⟨⟨⟨hleft, hright⟩, sum_eq_of_cancelDepth_eq_zero x hdepth⟩, hdepth⟩

/-- The genuine depth-zero anomaly is exactly the positive diagonal floor. -/
theorem actualDepthAnomaly_zero_eq
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (r : ℕ) :
    actualDepthAnomaly G r 0 =
      ((Fintype.card F : ℤ) - 1) * allPairsDepthFiber G r 0 := by
  unfold actualDepthAnomaly
  rw [depthFiber_zero_eq_allPairsDepthFiber]
  unfold G100PerDepthCenteringCancellation.depthAnomaly
  ring

/-- In particular the depth-zero anomaly is nonnegative. -/
theorem actualDepthAnomaly_zero_nonneg
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (r : ℕ) :
    0 ≤ actualDepthAnomaly G r 0 := by
  rw [actualDepthAnomaly_zero_eq]
  have hcard : (1 : ℤ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos
  exact mul_nonneg (sub_nonneg.mpr hcard) (by positivity)

end ArkLib.ProximityGap.Frontier.G102DepthZeroAnomalyFloor

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G102DepthZeroAnomalyFloor.valueBag_eq_of_cancelDepth_eq_zero
#print axioms
  ArkLib.ProximityGap.Frontier.G102DepthZeroAnomalyFloor.sum_eq_of_cancelDepth_eq_zero
#print axioms
  ArkLib.ProximityGap.Frontier.G102DepthZeroAnomalyFloor.depthFiber_zero_eq_allPairsDepthFiber
#print axioms
  ArkLib.ProximityGap.Frontier.G102DepthZeroAnomalyFloor.actualDepthAnomaly_zero_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G102DepthZeroAnomalyFloor.actualDepthAnomaly_zero_nonneg
