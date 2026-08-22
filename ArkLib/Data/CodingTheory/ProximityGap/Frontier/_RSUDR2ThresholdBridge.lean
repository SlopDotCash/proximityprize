/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAUDR2Bound
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# A threshold bridge for explicit RS UDR2 certificates

This packages the good-side half of the corrected tight-budget analysis. Once a radius is shown
to lie below the RS relative unique-decoding radius and the two arithmetic UDR2 side conditions
hold, the existing `epsMCA_rs_udr2_le` estimate immediately becomes a lower bound on
`mcaDeltaStar` whenever the field mass `n / |F|` fits the target budget.
-/

set_option autoImplicit false

open ProximityGap ProximityGap.MCAThresholdLedger

namespace ArkLib.ProximityGap.Frontier.RSUDR2ThresholdBridge

open scoped NNReal ENNReal

theorem le_mcaDeltaStar_of_rs_udr2_budget
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (α : ι ↪ F) (k : ℕ) [NeZero k] (hk : k ≤ Fintype.card ι)
    {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδ_udr : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code α k : Set (ι → F)))
    (htn : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ < Fintype.card ι)
    (hreg : 2 * (Fintype.card ι -
      ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) < Fintype.card ι - k + 1)
    {εstar : ℝ≥0∞}
    (hbudget : (Fintype.card ι : ℕ) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := F)
      (ReedSolomon.code α k : Set (ι → F)) εstar := by
  apply le_mcaDeltaStar_of_good _ _ hδ1
  exact le_trans
    (ProximityGap.UDR2.epsMCA_rs_udr2_le α k hk δ hδ_udr htn hreg)
    hbudget

end ArkLib.ProximityGap.Frontier.RSUDR2ThresholdBridge

#print axioms ArkLib.ProximityGap.Frontier.RSUDR2ThresholdBridge.le_mcaDeltaStar_of_rs_udr2_budget
