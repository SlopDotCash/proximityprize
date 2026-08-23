/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R192 bulk/spike budget split)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R190BulkPlusSpikesQuarterMGF

/-!
# R192 (#466): split the R190 weighted budget into bulk and spike budgets

R191 decomposed the R189/R190 half-grid certificate into two independent
pieces:

* the bulk geometric weighted sum;
* the additive spike weighted sum.

This file exposes that bookkeeping in Lean.  If the bulk part is at most
`Bbulk |s|`, the spike part is at most `Bspike |s|`, and
`Bbulk + Bspike ≤ 2`, then the R190 consumer proves `DyadicQuarterMGFBound`.

Status: consumer only.  Residual = prove the two split numerical/analytic
budgets for actual dyadic spectra.
-/

set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit

open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer
open ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF

noncomputable section

/-- Bulk contribution of the R190 weighted envelope. -/
def BulkWeightedBudget {ι : Type*} (s : Finset ι) (Θ : Finset ℝ)
    (δ : ℝ → ℝ) (Cbulk : ℝ) : ℝ :=
  ∑ θ ∈ Θ, δ θ * (Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)))

/-- Bulk contribution normalized by the ambient population size.  This is the grid-only
quantity that probes report as a per-point bulk ratio. -/
def NormalizedBulkWeightedBudget (Θ : Finset ℝ) (δ : ℝ → ℝ) (Cbulk : ℝ) : ℝ :=
  ∑ θ ∈ Θ, δ θ * (Cbulk * Real.exp (-(θ / 2)))

/-- Spike contribution of the R190 weighted envelope. -/
def SpikeWeightedBudget (Θ : Finset ℝ) (δ : ℝ → ℝ) (Kspike : ℝ) : ℝ :=
  ∑ θ ∈ Θ, δ θ * Kspike

/-- The bulk budget factors as `|s|` times its normalized grid-only budget. -/
theorem bulkWeightedBudget_eq_card_mul_normalized {ι : Type*}
    (s : Finset ι) (Θ : Finset ℝ) (δ : ℝ → ℝ) (Cbulk : ℝ) :
    BulkWeightedBudget s Θ δ Cbulk =
      (s.card : ℝ) * NormalizedBulkWeightedBudget Θ δ Cbulk := by
  unfold BulkWeightedBudget NormalizedBulkWeightedBudget
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ _
  ring

/-- A normalized bulk-budget bound proves the scaled bulk-budget side of R192. -/
theorem bulkWeightedBudget_le_of_normalized
    {ι : Type*} (s : Finset ι) (Θ : Finset ℝ) (δ : ℝ → ℝ) (Cbulk Bbulk : ℝ)
    (hNorm : NormalizedBulkWeightedBudget Θ δ Cbulk ≤ Bbulk) :
    BulkWeightedBudget s Θ δ Cbulk ≤ Bbulk * (s.card : ℝ) := by
  rw [bulkWeightedBudget_eq_card_mul_normalized]
  calc
    (s.card : ℝ) * NormalizedBulkWeightedBudget Θ δ Cbulk
        ≤ (s.card : ℝ) * Bbulk :=
      mul_le_mul_of_nonneg_left hNorm (Nat.cast_nonneg _)
    _ = Bbulk * (s.card : ℝ) := by ring

/-- The R190 weighted envelope is the sum of its bulk and spike pieces. -/
theorem weightedEnvelope_eq_bulk_add_spike {ι : Type*}
    (s : Finset ι) (Θ : Finset ℝ) (δ : ℝ → ℝ) (Cbulk Kspike : ℝ) :
    (∑ θ ∈ Θ,
      δ θ * (Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike))
      = BulkWeightedBudget s Θ δ Cbulk + SpikeWeightedBudget Θ δ Kspike := by
  unfold BulkWeightedBudget SpikeWeightedBudget
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro θ _
  ring

/-- **Split-budget R190 consumer.**  Bounding the bulk and spike weighted sums
separately is enough to discharge the R190 budget and hence prove the named
quarter-MGF residual. -/
theorem quarterMGF_of_bulkPlusSpikes_splitBudget {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Cbulk Kspike Bbulk Bspike : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ Cbulk Kspike)
    (hBulk : BulkWeightedBudget s Θ δ Cbulk ≤ Bbulk * (s.card : ℝ))
    (hSpike : SpikeWeightedBudget Θ δ Kspike ≤ Bspike * (s.card : ℝ))
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  refine quarterMGF_of_bulkPlusSpikesGridTail s t Θ δ Cbulk Kspike
    hδ hstair hTail ?_
  calc
    (∑ θ ∈ Θ,
      δ θ * (Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike))
        = BulkWeightedBudget s Θ δ Cbulk + SpikeWeightedBudget Θ δ Kspike := by
          exact weightedEnvelope_eq_bulk_add_spike s Θ δ Cbulk Kspike
    _ ≤ Bbulk * (s.card : ℝ) + Bspike * (s.card : ℝ) := add_le_add hBulk hSpike
    _ = (Bbulk + Bspike) * (s.card : ℝ) := by ring
    _ ≤ 2 * (s.card : ℝ) := by
      exact mul_le_mul_of_nonneg_right hBudget (Nat.cast_nonneg _)

/-- Split-budget consumer specialized to the R189 constants `(3/5)` and `2`. -/
theorem quarterMGF_of_threeFifths_plus_two_splitBudget {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Bbulk Bspike : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ (3 / 5) 2)
    (hBulk : BulkWeightedBudget s Θ δ (3 / 5) ≤ Bbulk * (s.card : ℝ))
    (hSpike : SpikeWeightedBudget Θ δ 2 ≤ Bspike * (s.card : ℝ))
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  exact quarterMGF_of_bulkPlusSpikes_splitBudget s t Θ δ (3 / 5) 2 Bbulk Bspike
    hδ hstair hTail hBulk hSpike hBudget

/-- Split-budget consumer with the bulk side supplied in normalized grid-only form. -/
theorem quarterMGF_of_bulkPlusSpikes_normalizedBulk {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Cbulk Kspike Bbulk Bspike : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ Cbulk Kspike)
    (hBulk : NormalizedBulkWeightedBudget Θ δ Cbulk ≤ Bbulk)
    (hSpike : SpikeWeightedBudget Θ δ Kspike ≤ Bspike * (s.card : ℝ))
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t :=
  quarterMGF_of_bulkPlusSpikes_splitBudget s t Θ δ Cbulk Kspike Bbulk Bspike
    hδ hstair hTail
    (bulkWeightedBudget_le_of_normalized s Θ δ Cbulk Bbulk hBulk)
    hSpike hBudget

/-- R189 constants with the bulk side supplied in normalized form. -/
theorem quarterMGF_of_threeFifths_plus_two_normalizedBulk {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Bbulk Bspike : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ (3 / 5) 2)
    (hBulk : NormalizedBulkWeightedBudget Θ δ (3 / 5) ≤ Bbulk)
    (hSpike : SpikeWeightedBudget Θ δ 2 ≤ Bspike * (s.card : ℝ))
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t :=
  quarterMGF_of_bulkPlusSpikes_normalizedBulk s t Θ δ (3 / 5) 2 Bbulk Bspike
    hδ hstair hTail hBulk hSpike hBudget

end

end ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit.bulkWeightedBudget_eq_card_mul_normalized
#print axioms ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit.bulkWeightedBudget_le_of_normalized
#print axioms ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit.weightedEnvelope_eq_bulk_add_spike
#print axioms ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit.quarterMGF_of_bulkPlusSpikes_splitBudget
#print axioms ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit.quarterMGF_of_threeFifths_plus_two_splitBudget
#print axioms ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit.quarterMGF_of_bulkPlusSpikes_normalizedBulk
#print axioms ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit.quarterMGF_of_threeFifths_plus_two_normalizedBulk
