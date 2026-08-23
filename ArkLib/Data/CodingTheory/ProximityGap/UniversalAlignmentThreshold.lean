/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.UniversalAlignmentLaw

/-!
# Threshold consumers for the universal alignment law (#371)

`UniversalAlignmentLaw.lean` turns bad scalars at agreement threshold `a` into an
alignment census.  This file connects that census to the `mcaDeltaStar` ledger:
any uniform bound on `alignableSets` gives a good radius, and therefore a lower
bound on `δ*`.
-/

open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Any uniform alignment-census bound whose mass fits the target budget gives a
direct lower bound on `mcaDeltaStar`. -/
theorem le_mcaDeltaStar_of_alignableSets_card_le [DecidableEq F] (dom : Fin n ↪ F) {k a : ℕ}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (a : ℕ)) (L : ℕ)
    (hL : ∀ u₀ u₁ : Fin n → F, (alignableSets dom k a u₀ u₁).card ≤ L)
    {εstar : ℝ≥0∞}
    (hbudget : (L : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (epsMCA_le_of_alignableSets_card_le dom hk hka hlo hhi L hL) hbudget)

open Classical in
/-- Coarse threshold form of the universal alignment law:
if `C(n,a)/|F|` fits the target budget, then the radius is below `δ*`. -/
theorem le_mcaDeltaStar_alignment_choose (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (hka : k + 1 ≤ a) {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (a : ℕ))
    {εstar : ℝ≥0∞}
    (hbudget : ((n.choose a : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  letI := Classical.decEq F
  le_mcaDeltaStar_of_alignableSets_card_le dom hk hka hδ1 hlo hhi (n.choose a)
    (fun u₀ u₁ => alignableSets_card_le_choose dom k a u₀ u₁) hbudget

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.le_mcaDeltaStar_of_alignableSets_card_le
#print axioms ProximityGap.Ownership.le_mcaDeltaStar_alignment_choose
