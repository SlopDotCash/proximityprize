/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridConstants

/-!
# A lower bound on the optimized first-order exceptional-count certificate

The actual first-derivative degree one contributes a fixed-fiber charge at
every permissible split. For total jet degree at least two this charge is at
least (n-A)(1+2D-3), with the inner subtraction in the naturals. This bounds
the numerical certificate used by the hybrid proof.
-/

namespace ProximityGap.FirstOrderChargeFloor

open ReedSolomon.HiddenDerivative MvPolynomial Finset

private theorem stage_floor {D μ : ℕ} (hμ : 2 ≤ μ) :
    1 + regularTaylorExponent D ≤ regularFiberStageSum D μ 1 := by
  simp only [regularFiberStageSum, sum_range_one, Nat.sub_zero, firstOrderCurveFiberStageOne]
  rw [cappedDegreeMixedVolume_eq (by omega) (by apply firstOrderTaylorDerivativeCap_le_totalCap)]
  rw [one_mul]
  apply le_trans _ (Nat.le_add_left _ _)
  unfold firstOrderTaylorTotalCap
  have h := Nat.mul_le_mul_left (regularTaylorExponent D) (show 1 ≤ μ-1 by omega)
  omega

/-- Taking the best split in the hybrid bound still incurs a fixed-fiber charge
whenever derivative degree one is among the possible actual degrees. -/
theorem optimized_floor {n D A h μ M : ℕ} (hDA : D < A) (hAn : A ≤ n)
    (hμ : 2 ≤ μ) (hM : 1 ≤ M) :
    ((n-A : ℕ) : ℝ)*(1+regularTaylorExponent D : ℕ) ≤
      maxMinFirstOrderExceptionCharge (agreementIncidenceRatio n D A) n D A h μ M := by
  classical
  let θ := agreementIncidenceRatio n D A
  have hθ : 0 ≤ θ := by dsimp [θ,agreementIncidenceRatio]; positivity
  apply le_trans _ (minFirstOrderExceptionCharge_le_maxMin (θ := θ) hM)
  obtain ⟨L,hL,hmin⟩ : ∃ L ∈ Icc (D+1) A,
      firstOrderExceptionCharge θ n D A h μ 1 L = minFirstOrderExceptionCharge θ n D A h μ 1 := by
    unfold minFirstOrderExceptionCharge
    simp only [dite_eq_left hDA]
    exact mem_image.mp (Finset.min'_mem _ _)
  rw [← hmin]
  have ⟨hDL,hLA⟩ := mem_Icc.mp hL
  have hfix : 1 ≤ fixedCoordinateRatio n D L := by
    unfold fixedCoordinateRatio
    apply (le_div_iff₀ (by exact_mod_cast (show 0 < L-D by omega))).mpr
    rw [one_mul]
    exact_mod_cast (show L-D ≤ n-D by omega)
  have hret : 0 ≤ retainedCoordinateRatio n A L := by unfold retainedCoordinateRatio; positivity
  have htail : 0 ≤ ordinaryTailCharge θ n D h (μ-1) := by
    unfold ordinaryTailCharge
    split_ifs <;> positivity
  have ha : ((n-A:ℕ):ℝ) ≤ (n-L:ℕ) := by exact_mod_cast (show n-A ≤ n-L by omega)
  have hs : ((1+regularTaylorExponent D : ℕ):ℝ) ≤ regularFiberStageSum D μ 1 := by
    exact_mod_cast stage_floor hμ
  unfold firstOrderExceptionCharge
  calc _ = ((n-A : ℕ):ℝ)*1*(1+regularTaylorExponent D : ℕ) := by rw [mul_one]
       _ ≤ ((n-L : ℕ):ℝ) * fixedCoordinateRatio n D L * regularFiberStageSum D μ 1 := by gcongr
       _ ≤ _ := by apply le_add_of_nonneg_left; positivity

/-- At the length-2^30 half-rate certificate radius 39/128, every nontrivial
first-derivative cap with total jet degree at least two costs more than 2^58,
independently of the chosen height and split. -/
theorem half_rate_floor (h μ M : ℕ) (hμ : 2 ≤ μ) (hM : 1 ≤ M) :
    (2:ℝ)^58 < maxMinFirstOrderExceptionCharge
      (agreementIncidenceRatio (2^30) (2^29-1) (89*2^23))
      (2^30) (2^29-1) (89*2^23) h μ M := by
  apply lt_of_lt_of_le _ (optimized_floor (by decide) (by decide) hμ hM)
  norm_num [regularTaylorExponent]

end ProximityGap.FirstOrderChargeFloor

#print axioms ProximityGap.FirstOrderChargeFloor.optimized_floor

#print axioms ProximityGap.FirstOrderChargeFloor.half_rate_floor
