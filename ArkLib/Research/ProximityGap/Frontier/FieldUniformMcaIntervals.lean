/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.JohnsonBudgetLadder
import ArkLib.Research.ProximityGap.Frontier.FieldUniformMcaCeilings
import ArkLib.Research.ProximityGap.Frontier.FineGridProductionMcaIntervals

/-!
# Two-sided line-MCA intervals at length 2³⁰ across field sizes

The intervals of `ProductionMcaIntervals` and `FineGridProductionMcaIntervals` hold for
primes in one field-budget window. Here the lower endpoints come from the weighted Johnson
ladder and from first-order interpolation, and the upper endpoints from power-map failures
that need no window. Together they bracket the operational 128-bit line-MCA supremum of
every smooth Reed–Solomon code of length `2³⁰` at the four prize rates, for field sizes
from `2^164` up to `2^256`.

## Main statements

* `rung_le_mcaDeltaStar`: a production rung with exponent `β` is a lower bound over every
  finite field with at least `2^(128+β)` elements, on every injective domain.
* `field_interval`: on a smooth domain and below `2^256` elements, the supremum lies between
  that rung and `FieldUniformMcaCeilings.universalFailureRadius`.
* `prime_interval`, `prime_interval_wide`: over prime fields with `2^225 ≤ p < 2^256` and
  `2^240 ≤ p < 2^256`, the lower endpoints are the first-order radii.

The suprema inside these intervals remain open.
-/

namespace ProximityGap.FieldUniformMcaIntervals

open CoreDefinitions FourRateSmoothMca128 FourRateSmoothMcaLift JohnsonBudgetLadder
  FieldUniformMcaCeilings
open scoped NNReal ENNReal

private theorem threshold_eq :
    ENNReal.ofReal (1/(2:ℝ)^128) = ((prizeThreshold : ℝ≥0) : ℝ≥0∞) := by
  norm_num [prizeThreshold, ENNReal.ofReal_div_of_pos]

/-- The safe radius of a rung at length `2^30`. -/
noncomputable def rungRadius (r : Rung) : ℝ≥0 := ((2^30 - r.A : ℕ) : ℝ≥0) / 2^30

/-- A production rung bounds the operational supremum from below at every positive
interleaving width, over every finite field with at least `2^(128+β)` elements and on every
injective evaluation domain of length `2^30`. -/
theorem rung_le_mcaDeltaStar {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (dom : Fin (2^30) ↪ F) {r : Rung} (hr : r ∈ productionRungs)
    (hF : 2^(128+r.β) ≤ Fintype.card F) (width : ℕ) [NeZero width] :
    rungRadius r ≤ MCAThresholdLedger.mcaDeltaStar (F := F)
      ((ReedSolomon.code dom r.k : Set (Fin (2^30) → F)) ^⋈ (Fin width))
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) := by
  let : SampleableType F := SampleableType.ofFintype _
  have hA : r.A ≤ 2^30 := (productionRungs_valid r hr).2.2.1
  have hcoe : ((rungRadius r : ℝ≥0) : ℝ) = 1 - (r.A:ℝ)/2^30 := by
    rw [rungRadius, NNReal.coe_div, NNReal.coe_natCast, Nat.cast_sub hA]
    push_cast
    field_simp
    norm_num
  apply MCAThresholdLedger.le_mcaDeltaStar_of_good
  · rw [← NNReal.coe_le_coe, hcoe]
    have : (0:ℝ) ≤ (r.A:ℝ)/2^30 := by positivity
    norm_num
    linarith
  · rw [epsMCA_interleaved_eq, epsMCA_eq_mcaError, ← threshold_eq]
    exact production_secure dom hr hF hcoe.le

/-- On a smooth domain of length `2^30`, over every finite field with at least `2^(128+β)`
and fewer than `2^256` elements, the operational supremum at the rate of a production rung
lies between the rung and the universal failing radius. -/
theorem field_interval {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (dom : Fin (2^30) ↪ F) [ReedSolomon.Smooth dom] {r : Rung} (hr : r ∈ productionRungs)
    (j : Fin 4) (hj : prizeDimension (ι := Fin (2^30)) j = r.k)
    (hlo : 2^(128+r.β) ≤ Fintype.card F) (hhi : Fintype.card F < 2^256)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code dom (prizeDimension (ι := Fin (2^30)) j) :
      Set (Fin (2^30) → F)) ^⋈ (Fin width)
    rungRadius r ≤ MCAThresholdLedger.mcaDeltaStar (F := F) C
        ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ∧
      MCAThresholdLedger.mcaDeltaStar (F := F) C ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ≤
        universalFailureRadius j := by
  have hq : 2048 < Fintype.card F :=
    lt_of_lt_of_le (lt_of_lt_of_le (by decide : 2048 < 2^128)
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right 128 r.β))) hlo
  dsimp only
  rw [hj]
  refine ⟨rung_le_mcaDeltaStar dom hr hlo width, ?_⟩
  rw [← hj]
  exact threshold_le_universalFailureRadius dom (r := 2097152) (by decide)
    ((Fintype.card_fin _).trans (by decide)) hq hhi j width

/-- First-order lower endpoints under `2^225 ≤ p`, in prize-rate order. -/
noncomputable def firstOrderRadius : Fin 4 → ℝ≥0 := ![1262/4096,2166/4096,2780/4096,3195/4096]

/-- Over every prime field with `2^225 ≤ p < 2^256`, the operational supremum on a smooth
domain of length `2^30` lies between the first-order radius and the universal failing
radius, at all four rates and every positive interleaving width. -/
theorem prime_interval {p : ℕ} [Fact p.Prime] (dom : Fin (2^30) ↪ ZMod p)
    [ReedSolomon.Smooth dom] (hlo : 2^225 ≤ p) (hhi : p < 2^256) (j : Fin 4) (width : ℕ)
    [NeZero width] :
    let C := (ReedSolomon.code dom (prizeDimension (ι := Fin (2^30)) j) :
      Set (Fin (2^30) → ZMod p)) ^⋈ (Fin width)
    firstOrderRadius j ≤ MCAThresholdLedger.mcaDeltaStar (F := ZMod p) C
        ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ∧
      MCAThresholdLedger.mcaDeltaStar (F := ZMod p) C ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ≤
        universalFailureRadius j := by
  let : SampleableType (ZMod p) := SampleableType.ofFintype _
  dsimp only
  constructor
  · apply MCAThresholdLedger.le_mcaDeltaStar_of_good
    · rw [← NNReal.coe_le_coe]
      fin_cases j <;> norm_num [firstOrderRadius]
    · rw [epsMCA_interleaved_eq, epsMCA_eq_mcaError, ← threshold_eq]
      have hp : 2^165*((2^18)*4096)^2 ≤ p := le_trans (by decide) hlo
      have h := FineGridFirstOrderSecurity.four_rates (b := 2^18) (by decide) hp dom
      have hrad : ((firstOrderRadius j : ℝ≥0) : ℝ) =
          (![1262/4096,2166/4096,2780/4096,3195/4096] : Fin 4 → ℝ) j := by
        fin_cases j <;> norm_num [firstOrderRadius]
      rw [hrad]
      simp only [prizeDimension,Fintype.card_fin]
      fin_cases j
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2
  · refine threshold_le_universalFailureRadius dom (r := 2097152) (by decide)
      ((Fintype.card_fin _).trans (by decide)) ?_ ?_ j width
    · rw [ZMod.card]
      exact lt_of_lt_of_le (by decide) hlo
    · rw [ZMod.card]
      exact hhi

/-- Over every prime field with `2^240 ≤ p < 2^256`, the lower endpoints rise to the radii
of `FineGridProductionMcaIntervals.safeRadius`. -/
theorem prime_interval_wide {p : ℕ} [Fact p.Prime] (dom : Fin (2^30) ↪ ZMod p)
    [ReedSolomon.Smooth dom] (hlo : 2^240 ≤ p) (hhi : p < 2^256) (j : Fin 4) (width : ℕ)
    [NeZero width] :
    let C := (ReedSolomon.code dom (prizeDimension (ι := Fin (2^30)) j) :
      Set (Fin (2^30) → ZMod p)) ^⋈ (Fin width)
    FineGridProductionMcaIntervals.safeRadius j ≤
        MCAThresholdLedger.mcaDeltaStar (F := ZMod p) C ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ∧
      MCAThresholdLedger.mcaDeltaStar (F := ZMod p) C ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ≤
        universalFailureRadius j := by
  let : SampleableType (ZMod p) := SampleableType.ofFintype _
  dsimp only
  constructor
  · apply MCAThresholdLedger.le_mcaDeltaStar_of_good
    · rw [← NNReal.coe_le_coe]
      fin_cases j <;> norm_num [FineGridProductionMcaIntervals.safeRadius]
    · rw [epsMCA_interleaved_eq, epsMCA_eq_mcaError, ← threshold_eq]
      have hp : 2^180*((2^18)*4096)^2 ≤ p := le_trans (by decide) hlo
      have h := FineGridFirstOrderSecurity.four_rates_wide (b := 2^18) (by decide) hp dom
      have hrad : ((FineGridProductionMcaIntervals.safeRadius j : ℝ≥0) : ℝ) =
          (![1269/4096,2174/4096,2788/4096,3201/4096] : Fin 4 → ℝ) j := by
        fin_cases j <;> norm_num [FineGridProductionMcaIntervals.safeRadius]
      rw [hrad]
      simp only [prizeDimension,Fintype.card_fin]
      fin_cases j
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2
  · refine threshold_le_universalFailureRadius dom (r := 2097152) (by decide)
      ((Fintype.card_fin _).trans (by decide)) ?_ ?_ j width
    · rw [ZMod.card]
      exact lt_of_lt_of_le (by decide) hlo
    · rw [ZMod.card]
      exact hhi

end ProximityGap.FieldUniformMcaIntervals

#print axioms ProximityGap.FieldUniformMcaIntervals.rung_le_mcaDeltaStar
#print axioms ProximityGap.FieldUniformMcaIntervals.field_interval
#print axioms ProximityGap.FieldUniformMcaIntervals.prime_interval
#print axioms ProximityGap.FieldUniformMcaIntervals.prime_interval_wide
