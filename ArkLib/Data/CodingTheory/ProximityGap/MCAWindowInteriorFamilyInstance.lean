/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAWindowInteriorFamily
import ArkLib.Data.CodingTheory.ProximityGap.MCAWindowInteriorExact

/-!
# The concrete interior pin as a corollary of the family theorem (#357)

`MCAWindowInteriorFamily.lean` proved the parametric interior pin
`mcaDeltaStar(C, C(n,t+1)/q) = 1 − t/n` conditional on `ExtremalWitnessLayer C t`. This file
**discharges that hypothesis** for the concrete `RS[F₁₁, (1,2,3,4,5), 2]` at layer `t = 3` —
the sibling's exact value `ε_mca(C, 2/5) = 10/11 = C(5,3)/q` (`epsMCA_window_eq`) is *exactly*
`ExtremalWitnessLayer C 3` — and recovers the concrete interior pin
`mcaDeltaStar(C, 5/11) = 2/5` as a one-line **corollary** of the family theorem.

This unifies the two results: the standalone `MCAWindowInteriorPin.mcaDeltaStar_window_interior_eq`
and this `mcaDeltaStar_window_via_family` are the *same pin*, the latter exhibiting it as an
instance of the parametric machinery. It validates the family theorem on the one case where the
extremal layer is independently known, and shows the conditional hypothesis is genuinely
dischargeable (not vacuous).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ProximityGap.MCAWindowInteriorExact ProximityGap.MCAWindowInteriorFamily

namespace ProximityGap.MCAWindowInteriorFamilyInstance

/-- **The extremal layer is discharged at `t = 3`** for the concrete code, directly from the
sibling's exact interior value `ε_mca(C, 2/5) = 10/11 = C(5,3)/q`. -/
theorem extremal_layer_F11 :
    ExtremalWitnessLayer (F := F11) (A := F11)
      (ReedSolomon.code domain5 2 : Set (Fin 5 → F11)) 3 := by
  unfold ExtremalWitnessLayer
  have hF : Fintype.card F11 = 11 := ZMod.card 11
  rw [Fintype.card_fin, hF]
  have hrad : (1 : ℝ≥0) - ((3:ℕ) : ℝ≥0) / ((5:ℕ) : ℝ≥0) = 2/5 := by
    apply NNReal.coe_injective
    have h35 : ((3:ℕ) : ℝ≥0) / ((5:ℕ) : ℝ≥0) ≤ 1 := by
      rw [div_le_one (by norm_num)]; norm_num
    rw [NNReal.coe_sub h35]; push_cast; norm_num
  rw [hrad, epsMCA_window_eq, show Nat.choose 5 3 = 10 from rfl]
  norm_num

/-- **The concrete interior pin, derived from the family theorem.**
`mcaDeltaStar(RS[F₁₁,(1,2,3,4,5),2], 5/11) = 2/5` — an instance of
`mcaDeltaStar_family_interior_pin` at `t = 3`, with the extremal layer discharged by
`extremal_layer_F11`. Identical to `MCAWindowInteriorPin.mcaDeltaStar_window_interior_eq`,
here exhibited as a corollary of the parametric machinery. -/
theorem mcaDeltaStar_window_via_family :
    mcaDeltaStar (F := F11) (A := F11)
        (ReedSolomon.code domain5 2 : Set (Fin 5 → F11))
        (((5 : ℕ) : ℝ≥0∞) / 11) = 2/5 := by
  have hcard : Fintype.card (Fin 5) = 5 := Fintype.card_fin 5
  have hF : Fintype.card F11 = 11 := ZMod.card 11
  have hpin := mcaDeltaStar_family_interior_pin (F := F11) (A := F11)
    (ReedSolomon.code domain5 2) (t := 3)
    (by rw [hcard]; norm_num)
    (by rw [hcard]; norm_num)
    extremal_layer_F11
  rw [Fintype.card_fin, hF] at hpin
  have hrad : (1 : ℝ≥0) - ((3:ℕ) : ℝ≥0) / ((5:ℕ) : ℝ≥0) = 2/5 := by
    apply NNReal.coe_injective
    have h35 : ((3:ℕ) : ℝ≥0) / ((5:ℕ) : ℝ≥0) ≤ 1 := by
      rw [div_le_one (by norm_num)]; norm_num
    rw [NNReal.coe_sub h35]; push_cast; norm_num
  rw [hrad] at hpin
  -- C(5,4) = 5: the threshold ↑((5).choose (3+1))/11 = ↑5/11
  have hc4 : (5 : ℕ).choose (3 + 1) = 5 := by decide
  rw [hc4] at hpin
  exact hpin

end ProximityGap.MCAWindowInteriorFamilyInstance

/-! ## Axiom audit — kernel-clean. -/
#print axioms ProximityGap.MCAWindowInteriorFamilyInstance.extremal_layer_F11
#print axioms ProximityGap.MCAWindowInteriorFamilyInstance.mcaDeltaStar_window_via_family
