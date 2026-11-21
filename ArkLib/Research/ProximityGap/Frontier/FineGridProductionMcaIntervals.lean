/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FineGridFirstOrderSecurity
import ArkLib.Research.ProximityGap.Frontier.ProductionMcaIntervals

/-!
# Sharper two-sided line-MCA intervals at length 2³⁰

`ProductionMcaIntervals` brackets the operational 128-bit line-MCA supremum at length
`2³⁰` between a first-order interpolation radius and a power-map failure radius. Every
prime in `FourRateSmoothMca128.BudgetWindow` exceeds `2^241`, which is more than the
`2^231` required by `FineGridFirstOrderSecurity.four_rates_wide`. The lower endpoints
therefore rise to `1265/4096`, `2170/4096`, `2783/4096` and `3197/4096`. The failing
endpoints are unchanged.
-/

namespace ProximityGap.FineGridProductionMcaIntervals

open CoreDefinitions FourRateSmoothMca128 FourRateSmoothMcaLift
open scoped NNReal ENNReal

/-- Certified closed-ball good radii in prize-rate order. -/
noncomputable def safeRadius : Fin 4 → ℝ≥0 := ![1265/4096,2170/4096,2783/4096,3197/4096]

/-- Each radius strictly exceeds the corresponding radius of `ProductionMcaIntervals`. -/
theorem safeRadius_gt (j : Fin 4) : ProductionMcaIntervals.safeRadius j < safeRadius j := by
  rw [← NNReal.coe_lt_coe]
  fin_cases j <;> norm_num [safeRadius, ProductionMcaIntervals.safeRadius]

/-- For every prime in the field-budget interval, the error is within tolerance
at the raised lower endpoints and exceeds tolerance at the upper endpoints. -/
theorem endpoints {p : ℕ} [Fact p.Prime] (dom : Fin (2^30) ↪ ZMod p) [ReedSolomon.Smooth dom]
    (hw : BudgetWindow (Fintype.card (ZMod p))) (j : Fin 4) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code dom (prizeDimension (ι := Fin (2^30)) j) :
      Set (Fin (2^30) → ZMod p)) ^⋈ (Fin width)
    epsMCA (F := ZMod p) C (safeRadius j) ≤ ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ∧
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) < epsMCA (F := ZMod p) C (failureRadius j) := by
  let : SampleableType (ZMod p) := SampleableType.ofFintype _
  dsimp only
  refine ⟨?_, (ProductionMcaIntervals.endpoints dom hw j width).2⟩
  rw [epsMCA_interleaved_eq, epsMCA_eq_mcaError]
  have hlo := hw.1
  rw [ZMod.card] at hlo
  have hp : 2^171*((2^18)*4096)^2 ≤ p := calc
    _ ≤ lowerBudget*2^128 := by decide
    _ ≤ p := (Nat.le_div_iff_mul_le (by decide)).mp hlo
  have h := FineGridFirstOrderSecurity.four_rates_wide (b := 2^18) (by decide) hp dom
  have ht : ENNReal.ofReal (1/(2:ℝ)^128) = ((prizeThreshold : ℝ≥0) : ℝ≥0∞) := by
    norm_num [prizeThreshold, ENNReal.ofReal_div_of_pos]
  rw [← ht]
  have hrad : ((safeRadius j : ℝ≥0) : ℝ) =
      (![1265/4096,2170/4096,2783/4096,3197/4096] : Fin 4 → ℝ) j := by
    fin_cases j <;> norm_num [safeRadius]
  rw [hrad]
  simp only [prizeDimension,Fintype.card_fin]
  fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

/-- Two-sided operational suprema with the raised lower endpoints, on the inhabited
prime-field family covering all four rates at the production block length. -/
theorem prime246_intervals (dom : Fin (2^30) ↪ FourRateListPrime246.K) [ReedSolomon.Smooth dom]
    (j : Fin 4) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code dom (prizeDimension (ι := Fin (2^30)) j) :
      Set (Fin (2^30) → FourRateListPrime246.K)) ^⋈ (Fin width)
    safeRadius j ≤ MCAThresholdLedger.mcaDeltaStar (F := FourRateListPrime246.K)
        C ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ∧
      MCAThresholdLedger.mcaDeltaStar (F := FourRateListPrime246.K)
        C ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ≤ failureRadius j := by
  have hp := endpoints dom prime246_window j width
  exact ⟨MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ (by
    rw [← NNReal.coe_le_coe]
    fin_cases j <;> norm_num [safeRadius]) hp.1,
    MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ hp.2⟩

end ProximityGap.FineGridProductionMcaIntervals

#print axioms ProximityGap.FineGridProductionMcaIntervals.endpoints
#print axioms ProximityGap.FineGridProductionMcaIntervals.prime246_intervals
