/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoPowerSubsetSumSpectrum

/-!
# G328: the dimension-two spectrum is not field-uniform without a field-size guard

The dimension-two KKH26 ceiling stack on an order-eight subgroup has `40` distinct bad scalars
at the large primes used by the campaign.  That number comes from injectivity of the signed-sum
spectrum with support weights one and three.  This file records the smallest admissible field as
an exact counterexample to an unguarded field-uniform statement.

In `ZMod 17`, the element `2` has exact order eight, but the weight-one datum `+1` collides with
the weight-three datum `-1 - g + g^2`, because `g = 2`.  Consequently the injectivity hypothesis
needed by `subsetSumSpectrum_card` fails.  The companion executable probe
`scripts/probes/g328_k2_field_stability_boundary.py` computes the exact ceiling count `16` at
`p = 17` and `40` for every tested prime `p = 1 mod 8` in `[41, 10000]`.

This does not affect the landed large-field dimension-two pin or the production Delta Star
problem.  It only makes the field-size guard explicit and refutes universal `q`-independence.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G328DimTwoFieldStabilityBoundary

open ArkLib.ProximityGap.KKH26

/-- The order-eight generator used for the exceptional field. -/
def g17 : ZMod 17 := 2

/-- The signed datum `+1`, of support weight one. -/
def weightOneDatum : (_ : Finset ℕ) × Finset ℕ := ⟨{0}, {0}⟩

/-- The signed datum `-1 - g + g^2`, of support weight three. -/
def weightThreeDatum : (_ : Finset ℕ) × Finset ℕ := ⟨{0, 1, 2}, {2}⟩

local instance localInstance_G328DimTwoFieldStabilityBoundary_1 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The multiplicative order of `2` modulo `17` is eight. -/
theorem orderOf_g17 : orderOf g17 = 8 := by
  have hFour : ¬g17 ^ (2 : ℕ) ^ 2 = 1 := by decide
  have hEight : g17 ^ (2 : ℕ) ^ 3 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := g17) hFour hEight
  norm_num at h
  exact h

/-- `2` has exact order eight in `ZMod 17`. -/
theorem g17_isPrimitiveRoot : IsPrimitiveRoot g17 8 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_g17

/-- The first datum belongs to the weight-one signed stratum. -/
theorem weightOneDatum_mem : weightOneDatum ∈ sigData 4 1 := by
  decide

/-- The second datum belongs to the weight-three signed stratum. -/
theorem weightThreeDatum_mem : weightThreeDatum ∈ sigData 4 3 := by
  decide

/-- The two signed data are distinct. -/
theorem weightOneDatum_ne_weightThreeDatum : weightOneDatum ≠ weightThreeDatum := by
  decide

/-- The concrete cross-stratum collision in `ZMod 17`: `1 = -1 - 2 + 2^2`. -/
theorem signedSpectrum_collision : sVal g17 weightOneDatum = sVal g17 weightThreeDatum := by
  norm_num [g17, weightOneDatum, weightThreeDatum, sVal]

/-- The full weight-one/weight-three spectrum map is not injective over `ZMod 17`.

This is the exact hypothesis failure that prevents the characteristic-independent `40`-value
spectrum formula from applying at the smallest proper order-eight subgroup field. -/
theorem not_injOn_spectrumVal_g17 :
    ¬Set.InjOn (spectrumVal g17) (spectrumData 4 {1, 3}) := by
  intro hinj
  have hOne : (⟨1, weightOneDatum⟩ : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ)) ∈
      spectrumData 4 {1, 3} := by
    simpa [spectrumData] using weightOneDatum_mem
  have hThree : (⟨3, weightThreeDatum⟩ : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ)) ∈
      spectrumData 4 {1, 3} := by
    simpa [spectrumData] using weightThreeDatum_mem
  have hEq := hinj hOne hThree (by simpa [spectrumVal] using signedSpectrum_collision)
  have : (1 : ℕ) = 3 := congrArg Sigma.fst hEq
  omega

end ArkLib.ProximityGap.Frontier.G328DimTwoFieldStabilityBoundary

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.G328DimTwoFieldStabilityBoundary.g17_isPrimitiveRoot
#print axioms
  ArkLib.ProximityGap.Frontier.G328DimTwoFieldStabilityBoundary.signedSpectrum_collision
#print axioms
  ArkLib.ProximityGap.Frontier.G328DimTwoFieldStabilityBoundary.not_injOn_spectrumVal_g17
