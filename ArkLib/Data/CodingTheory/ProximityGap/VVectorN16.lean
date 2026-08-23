/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import ArkLib.Data.CodingTheory.ProximityGap.DeltaStarSecondPinF17

/-!
# The first multi-window `δ*(ε*)` curve: `n = 16` smooth Reed–Solomon (#357, item 15)

Item 15 of the 26-thread review: assemble the landed pieces on one window-scale
instance.  The domain is the full multiplicative group `F₁₇* = ⟨3⟩` (`n = 16 = 2⁴`,
smooth), and the granularity-ladder closed form (`mcaDeltaStar_rs_eq_granularity`)
pins the threshold across **consecutive windows**:

* rate `1/4` (`k = 4`, distance `13`): **five** exact windows —
  `δ* = j/16` for `ε* ∈ [j/17, (j+1)/17)`, every `j ∈ {1,…,5}`;
* rate `1/2` (`k = 8`, distance `9`): **three** exact windows — `j ∈ {1, 2, 3}`.

This is the first complete initial segment of a `δ*(ε*)` curve at window scale: the
staircase `1/16 → 2/16 → 3/16 → 4/16 → 5/16` as `ε*` sweeps `[1/17, 6/17)`, machine-
checked end to end.  Past the last window (`3(j−1) + k > n`) the ladder's distance
condition fails and the explosion regime (item 18) governs — the boundary of the
proven curve is exactly the boundary of current knowledge.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.VVectorN16

open ProximityGap.SpikeFloor ProximityGap.DeltaStarSecondPin

/-- The full multiplicative domain: `dom16 i = 3^i`, all sixteen units of `F₁₇`. -/
def dom16 : Fin 16 → F17 := fun i => (3 : F17) ^ (i : ℕ)

theorem dom16_injective : Function.Injective dom16 := by decide

/-- The domain embedding `Fin 16 ↪ F₁₇`. -/
def dom16e : Fin 16 ↪ F17 := ⟨dom16, dom16_injective⟩

/-- **Five exact windows at rate `1/4`**: for `RS[F₁₇, ⟨3⟩, 4]` and every
`j ∈ {1,…,5}`, `δ* = j/16` on `ε* ∈ [j/17, (j+1)/17)`. -/
theorem mcaDeltaStar_rate_quarter {j : ℕ} (hj1 : 1 ≤ j) (hj5 : j ≤ 5)
    {εstar : ℝ≥0∞}
    (hlo : (j : ℝ≥0∞) / 17 ≤ εstar)
    (hhi : εstar < ((j + 1 : ℕ) : ℝ≥0∞) / 17) :
    MCAThresholdLedger.mcaDeltaStar (F := F17) (A := F17)
      ((rsCode dom16e 4 : Submodule F17 (Fin 16 → F17)) : Set (Fin 16 → F17)) εstar
      = (j : ℝ≥0) / 16 := by
  have hF : (Fintype.card F17 : ℝ≥0∞) = 17 := by
    rw [show Fintype.card F17 = 17 from by simp [ZMod.card]]
    norm_num
  have hc : (Fintype.card (Fin 16) : ℝ≥0) = 16 := by
    rw [Fintype.card_fin]
    norm_num
  rw [← hc]
  refine mcaDeltaStar_rs_eq_granularity dom16e hj1 (by omega) (by omega) ?_ ?_ ?_
  · rw [show Fintype.card F17 = 17 from by simp [ZMod.card]]
    omega
  · rw [hF]
    exact hlo
  · rw [hF]
    exact hhi

/-- **Three exact windows at rate `1/2`**: for `RS[F₁₇, ⟨3⟩, 8]` and every
`j ∈ {1, 2, 3}`, `δ* = j/16` on `ε* ∈ [j/17, (j+1)/17)`. -/
theorem mcaDeltaStar_rate_half {j : ℕ} (hj1 : 1 ≤ j) (hj3 : j ≤ 3)
    {εstar : ℝ≥0∞}
    (hlo : (j : ℝ≥0∞) / 17 ≤ εstar)
    (hhi : εstar < ((j + 1 : ℕ) : ℝ≥0∞) / 17) :
    MCAThresholdLedger.mcaDeltaStar (F := F17) (A := F17)
      ((rsCode dom16e 8 : Submodule F17 (Fin 16 → F17)) : Set (Fin 16 → F17)) εstar
      = (j : ℝ≥0) / 16 := by
  have hF : (Fintype.card F17 : ℝ≥0∞) = 17 := by
    rw [show Fintype.card F17 = 17 from by simp [ZMod.card]]
    norm_num
  have hc : (Fintype.card (Fin 16) : ℝ≥0) = 16 := by
    rw [Fintype.card_fin]
    norm_num
  rw [← hc]
  refine mcaDeltaStar_rs_eq_granularity dom16e hj1 (by omega) (by omega) ?_ ?_ ?_
  · rw [show Fintype.card F17 = 17 from by simp [ZMod.card]]
    omega
  · rw [hF]
    exact hlo
  · rw [hF]
    exact hhi

/-- The curve's deepest pinned point: `δ*(RS[F₁₇,⟨3⟩,4], ε*) = 5/16` for
`ε* ∈ [5/17, 6/17)` — the furthest window-scale exact threshold landed. -/
theorem mcaDeltaStar_deepest {εstar : ℝ≥0∞}
    (hlo : (5 : ℝ≥0∞) / 17 ≤ εstar) (hhi : εstar < (6 : ℝ≥0∞) / 17) :
    MCAThresholdLedger.mcaDeltaStar (F := F17) (A := F17)
      ((rsCode dom16e 4 : Submodule F17 (Fin 16 → F17)) : Set (Fin 16 → F17)) εstar
      = 5 / 16 := by
  have h5 : ((5 : ℕ) : ℝ≥0∞) / 17 ≤ εstar := by exact_mod_cast hlo
  have h6 : εstar < ((5 + 1 : ℕ) : ℝ≥0∞) / 17 := by
    have : ((5 + 1 : ℕ) : ℝ≥0∞) = 6 := by norm_num
    rw [this]
    exact hhi
  have := mcaDeltaStar_rate_quarter (j := 5) (by omega) (by omega) h5 h6
  rw [this]
  norm_num

end ProximityGap.VVectorN16

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.VVectorN16.mcaDeltaStar_rate_quarter
#print axioms ProximityGap.VVectorN16.mcaDeltaStar_rate_half
#print axioms ProximityGap.VVectorN16.mcaDeltaStar_deepest
