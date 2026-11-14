/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.MCAUDRBound
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# A threshold bridge for explicit RS UDR2 certificates

This packages the good-side half of the corrected tight-budget analysis. Once a radius is shown
to lie below the RS relative unique-decoding radius and the arithmetic UDR side condition
holds, the existing full-UDR estimate `UDRwire.epsMCA_rs_udr_le_full` immediately becomes a lower
bound on
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
    (hreg : 2 * (Fintype.card ι -
      ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) < Fintype.card ι - k + 1)
    {εstar : ℝ≥0∞}
    (hbudget : (Fintype.card ι : ℕ) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := F)
      (ReedSolomon.code α k : Set (ι → F)) εstar := by
  apply le_mcaDeltaStar_of_good _ _ hδ1
  exact le_trans
    (ProximityGap.UDRwire.epsMCA_rs_udr_le_full α k hk δ hδ_udr hreg)
    hbudget

end ArkLib.ProximityGap.Frontier.RSUDR2ThresholdBridge

#print axioms ArkLib.ProximityGap.Frontier.RSUDR2ThresholdBridge.le_mcaDeltaStar_of_rs_udr2_budget
