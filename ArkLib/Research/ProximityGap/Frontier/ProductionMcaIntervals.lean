/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ScaledFirstOrderSecurity
import ArkLib.Research.ProximityGap.Frontier.FourRateSmoothMcaLift

/-!
# Two-sided line-MCA intervals at length 2³⁰

The good bounds come from first-order interpolation on the entire domain.
Power-map lifts from small smooth codes witness the bad bounds. Both apply to
the same code, field, security tolerance and positive interleaving width.
-/

namespace ProximityGap.ProductionMcaIntervals

open CoreDefinitions FourRateSmoothMca128 FourRateSmoothMcaLift
open scoped NNReal ENNReal

/-- Certified closed-ball good radii in prize-rate order. -/
noncomputable def safeRadius : Fin 4 → ℝ≥0 := ![39/128,67/128,86/128,99/128]

/-- For every prime in the field-budget interval, the error is within tolerance
at the lower endpoints and exceeds tolerance at the upper endpoints. -/
theorem endpoints {p : ℕ} [Fact p.Prime] (dom : Fin (2^30) ↪ ZMod p) [ReedSolomon.Smooth dom]
    (hw : BudgetWindow (Fintype.card (ZMod p))) (j : Fin 4) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code dom (prizeDimension (ι := Fin (2^30)) j) :
      Set (Fin (2^30) → ZMod p)) ^⋈ (Fin width)
    epsMCA (F := ZMod p) C (safeRadius j) ≤ ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ∧
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) < epsMCA (F := ZMod p) C (failureRadius j) := by
  let : SampleableType (ZMod p) := SampleableType.ofFintype _
  dsimp only
  constructor
  · rw [epsMCA_interleaved_eq, epsMCA_eq_mcaError]
    have hlo := hw.1
    rw [ZMod.card] at hlo
    have hp : 2^165*((2^23)*128)^2 ≤ p := calc
      _ ≤ lowerBudget*2^128 := by decide
      _ ≤ p := (Nat.le_div_iff_mul_le (by decide)).mp hlo
    have h := ScaledFirstOrderSecurity.four_rates (b := 2^23) (by decide) hp dom
    have ht : ENNReal.ofReal (1/(2:ℝ)^128) = ((prizeThreshold : ℝ≥0) : ℝ≥0∞) := by
      norm_num [prizeThreshold, ENNReal.ofReal_div_of_pos]
    rw [← ht]
    have hrad : ((safeRadius j : ℝ≥0) : ℝ) = (![39/128,67/128,86/128,99/128] : Fin 4 → ℝ) j := by
      fin_cases j <;> norm_num [safeRadius]
    rw [hrad]
    simp only [prizeDimension,Fintype.card_fin]
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · rw [epsMCA_interleaved_eq]
    exact all_rates_bad dom (r:=2097152) (by decide) (by simp) hw j _ le_rfl


/-- Two-sided operational suprema, with a single inhabited prime-field family
covering all four rates at the production block length. -/
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

end ProximityGap.ProductionMcaIntervals

#print axioms ProximityGap.ProductionMcaIntervals.endpoints
#print axioms ProximityGap.ProductionMcaIntervals.prime246_intervals
