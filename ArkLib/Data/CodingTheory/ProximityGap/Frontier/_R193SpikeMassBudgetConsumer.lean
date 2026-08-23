/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R193 spike-mass budget consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R192BulkSpikeBudgetSplit

/-!
# R193 (#466): spike budget from staircase mass

R191 observed that, after the R189/R190 split, the additive-spike part is
controlled by the total mass of the staircase increments.  This file exposes
that reduction in Lean:

```text
  SpikeWeightedBudget Θ δ Kspike = Kspike * Σ_{θ∈Θ} δ θ.
```

Thus the R189 spike side can be attacked through a scalar certificate
`2 * Σ δ ≤ Bspike |s|`, which is the formal version of controlling
`exp(max(X)/4) / M`.
-/

set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer

open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer
open ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF
open ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit

noncomputable section

/-- Total mass of the threshold staircase increments. -/
def StaircaseMass (Θ : Finset ℝ) (δ : ℝ → ℝ) : ℝ :=
  ∑ θ ∈ Θ, δ θ

/-- The spike weighted budget is the spike multiplicity times staircase mass. -/
theorem spikeWeightedBudget_eq_spike_mul_mass
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Kspike : ℝ) :
    SpikeWeightedBudget Θ δ Kspike = Kspike * StaircaseMass Θ δ := by
  unfold SpikeWeightedBudget StaircaseMass
  rw [← Finset.sum_mul]
  ring

/-- A scalar staircase-mass bound proves the spike-budget side of R192. -/
theorem spikeWeightedBudget_le_of_mass_bound
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Kspike Bspike P : ℝ)
    (hMass : Kspike * StaircaseMass Θ δ ≤ Bspike * P) :
    SpikeWeightedBudget Θ δ Kspike ≤ Bspike * P := by
  rw [spikeWeightedBudget_eq_spike_mul_mass]
  exact hMass

/-- A staircase-mass ceiling plus a scalar fit proves the spike-budget side.  This is the form
used by analytic/probe lanes: first bound the total staircase mass, then fit that ceiling into
the split budget. -/
theorem spikeWeightedBudget_le_of_mass_ceiling
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Kspike Bspike P M : ℝ)
    (hK : 0 ≤ Kspike)
    (hMass : StaircaseMass Θ δ ≤ M)
    (hFit : Kspike * M ≤ Bspike * P) :
    SpikeWeightedBudget Θ δ Kspike ≤ Bspike * P := by
  rw [spikeWeightedBudget_eq_spike_mul_mass]
  exact le_trans (mul_le_mul_of_nonneg_left hMass hK) hFit

/-- Normalized staircase-mass ceiling.  If the mass is at most `Mper * P` and the per-point
spike fit is `Kspike * Mper ≤ Bspike`, then the spike budget is at most `Bspike * P`. -/
theorem spikeWeightedBudget_le_of_normalized_mass_ceiling
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Kspike Bspike P Mper : ℝ)
    (hK : 0 ≤ Kspike)
    (hP : 0 ≤ P)
    (hMass : StaircaseMass Θ δ ≤ Mper * P)
    (hFit : Kspike * Mper ≤ Bspike) :
    SpikeWeightedBudget Θ δ Kspike ≤ Bspike * P := by
  rw [spikeWeightedBudget_eq_spike_mul_mass]
  calc
    Kspike * StaircaseMass Θ δ ≤ Kspike * (Mper * P) :=
      mul_le_mul_of_nonneg_left hMass hK
    _ = (Kspike * Mper) * P := by ring
    _ ≤ Bspike * P := mul_le_mul_of_nonneg_right hFit hP

/-- **R193 split-budget consumer.**  Feed R192 with a scalar spike-mass
certificate instead of a direct `SpikeWeightedBudget` certificate. -/
theorem quarterMGF_of_bulkPlusSpikes_massBudget {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Cbulk Kspike Bbulk Bspike : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ Cbulk Kspike)
    (hBulk : BulkWeightedBudget s Θ δ Cbulk ≤ Bbulk * (s.card : ℝ))
    (hMass : Kspike * StaircaseMass Θ δ ≤ Bspike * (s.card : ℝ))
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  refine quarterMGF_of_bulkPlusSpikes_splitBudget s t Θ δ
    Cbulk Kspike Bbulk Bspike hδ hstair hTail hBulk ?_ hBudget
  exact spikeWeightedBudget_le_of_mass_bound Θ δ Kspike Bspike (s.card : ℝ) hMass

/-- R189 constants: `(3/5)` bulk and two spike cosets.  The spike certificate is
now the scalar inequality `2 * StaircaseMass Θ δ ≤ Bspike |s|`. -/
theorem quarterMGF_of_threeFifths_plus_two_massBudget {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Bbulk Bspike : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ (3 / 5) 2)
    (hBulk : BulkWeightedBudget s Θ δ (3 / 5) ≤ Bbulk * (s.card : ℝ))
    (hMass : 2 * StaircaseMass Θ δ ≤ Bspike * (s.card : ℝ))
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  exact quarterMGF_of_bulkPlusSpikes_massBudget s t Θ δ (3 / 5) 2
    Bbulk Bspike hδ hstair hTail hBulk hMass hBudget

/-- **Ceiling-form R193 consumer.**  The spike side may be supplied as an unscaled staircase-mass
ceiling `StaircaseMass Θ δ ≤ M` plus the scalar fit `Kspike * M ≤ Bspike |s|`. -/
theorem quarterMGF_of_bulkPlusSpikes_massCeiling {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Cbulk Kspike Bbulk Bspike M : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ Cbulk Kspike)
    (hBulk : BulkWeightedBudget s Θ δ Cbulk ≤ Bbulk * (s.card : ℝ))
    (hK : 0 ≤ Kspike)
    (hMass : StaircaseMass Θ δ ≤ M)
    (hFit : Kspike * M ≤ Bspike * (s.card : ℝ))
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  refine quarterMGF_of_bulkPlusSpikes_splitBudget s t Θ δ
    Cbulk Kspike Bbulk Bspike hδ hstair hTail hBulk ?_ hBudget
  exact spikeWeightedBudget_le_of_mass_ceiling Θ δ Kspike Bspike (s.card : ℝ) M
    hK hMass hFit

/-- R189 constants with the ceiling-form spike certificate. -/
theorem quarterMGF_of_threeFifths_plus_two_massCeiling {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Bbulk Bspike M : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ (3 / 5) 2)
    (hBulk : BulkWeightedBudget s Θ δ (3 / 5) ≤ Bbulk * (s.card : ℝ))
    (hMass : StaircaseMass Θ δ ≤ M)
    (hFit : 2 * M ≤ Bspike * (s.card : ℝ))
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  exact quarterMGF_of_bulkPlusSpikes_massCeiling s t Θ δ (3 / 5) 2
    Bbulk Bspike M hδ hstair hTail hBulk (by norm_num) hMass hFit hBudget

/-- **Normalized-mass R193 consumer.**  This is the probe-facing form: a per-point staircase
mass ceiling `StaircaseMass Θ δ ≤ Mper |s|` plus the scalar fit
`Kspike * Mper ≤ Bspike` proves the spike side. -/
theorem quarterMGF_of_bulkPlusSpikes_normalizedMass {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Cbulk Kspike Bbulk Bspike Mper : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ Cbulk Kspike)
    (hBulk : BulkWeightedBudget s Θ δ Cbulk ≤ Bbulk * (s.card : ℝ))
    (hK : 0 ≤ Kspike)
    (hMass : StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : Kspike * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  refine quarterMGF_of_bulkPlusSpikes_splitBudget s t Θ δ
    Cbulk Kspike Bbulk Bspike hδ hstair hTail hBulk ?_ hBudget
  exact spikeWeightedBudget_le_of_normalized_mass_ceiling Θ δ Kspike Bspike
    (s.card : ℝ) Mper hK (Nat.cast_nonneg _) hMass hFit

/-- R189 constants with the normalized-mass spike certificate. -/
theorem quarterMGF_of_threeFifths_plus_two_normalizedMass {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Bbulk Bspike Mper : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ (3 / 5) 2)
    (hBulk : BulkWeightedBudget s Θ δ (3 / 5) ≤ Bbulk * (s.card : ℝ))
    (hMass : StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : 2 * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  exact quarterMGF_of_bulkPlusSpikes_normalizedMass s t Θ δ (3 / 5) 2
    Bbulk Bspike Mper hδ hstair hTail hBulk (by norm_num) hMass hFit hBudget

/-- **Fully normalized R193/R192 consumer.**  The bulk side is supplied as an average
threshold budget, and the spike side as a per-point staircase-mass ceiling. -/
theorem quarterMGF_of_bulkPlusSpikes_normalizedBudgets {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Cbulk Kspike Bbulk Bspike Mper : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ Cbulk Kspike)
    (hBulk : NormalizedBulkWeightedBudget Θ δ Cbulk ≤ Bbulk)
    (hK : 0 ≤ Kspike)
    (hMass : StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : Kspike * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  exact quarterMGF_of_bulkPlusSpikes_normalizedBulk s t Θ δ
    Cbulk Kspike Bbulk Bspike hδ hstair hTail hBulk
    (spikeWeightedBudget_le_of_normalized_mass_ceiling Θ δ Kspike Bspike
      (s.card : ℝ) Mper hK (Nat.cast_nonneg _) hMass hFit)
    hBudget

/-- R189 constants with both split budgets in normalized form. -/
theorem quarterMGF_of_threeFifths_plus_two_normalizedBudgets {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Bbulk Bspike Mper : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ (3 / 5) 2)
    (hBulk : NormalizedBulkWeightedBudget Θ δ (3 / 5) ≤ Bbulk)
    (hMass : StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : 2 * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  exact quarterMGF_of_bulkPlusSpikes_normalizedBudgets s t Θ δ (3 / 5) 2
    Bbulk Bspike Mper hδ hstair hTail hBulk (by norm_num) hMass hFit hBudget

end

end ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer.spikeWeightedBudget_eq_spike_mul_mass
#print axioms ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer.spikeWeightedBudget_le_of_mass_bound
#print axioms ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer.spikeWeightedBudget_le_of_mass_ceiling
#print axioms ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer.spikeWeightedBudget_le_of_normalized_mass_ceiling
#print axioms ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer.quarterMGF_of_bulkPlusSpikes_massBudget
#print axioms ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer.quarterMGF_of_threeFifths_plus_two_massBudget
#print axioms ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer.quarterMGF_of_bulkPlusSpikes_massCeiling
#print axioms ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer.quarterMGF_of_threeFifths_plus_two_massCeiling
#print axioms ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer.quarterMGF_of_bulkPlusSpikes_normalizedMass
#print axioms ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer.quarterMGF_of_threeFifths_plus_two_normalizedMass
#print axioms ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer.quarterMGF_of_bulkPlusSpikes_normalizedBudgets
#print axioms ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer.quarterMGF_of_threeFifths_plus_two_normalizedBudgets
