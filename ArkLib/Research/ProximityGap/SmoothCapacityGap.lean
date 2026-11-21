/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.ToleranceCircuitCriterion
import ArkLib.Research.ProximityGap.JointDyadicCeilings

/-! # Capacity gaps that persist under length scaling on smooth domains

Taking powers maps a smooth domain onto a smaller one with equal fibers.
An over-budget base line therefore gives a gap of the same relative size
at every dyadic multiple of the base length.
-/

namespace ProximityPrize.SmoothCapacityGap

open Finset Code ProximityGap FullPrizeReview
open scoped NNReal ENNReal

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]

/-- At a multiple of a dyadic base length `h`, the budget test on the base
already forces failure one `h`th below the rate complement of the lifted code. -/
theorem mca_from_base (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0)
    {b h j l m : ℕ} (hm : 0 < m) (hn : Fintype.card I = m * h) (hp : h = 2 ^ b)
    (hj : 0 < j) (hjh : j < h) [NeZero l]
    (hs : (RankReview.budget F ε + 1).choose 2 ≤ Fintype.card F)
    (hB : RankReview.budget F ε < h.choose (j + 1)) {δ : ℝ≥0}
    (hδ : 1 - ((j + 1 : ℕ) : ℝ≥0) / h ≤ δ) :
    (ε : ℝ≥0∞) < epsMCA (F := F) ((ReedSolomon.code D (j * m) : Set (I → F)) ^⋈ (Fin l)) δ := by
  classical
  obtain ⟨V, hV, _, _, sm, lift⟩ := SmoothPowerMcaDescent.exists_smooth_base D hm hn ⟨b, hp⟩
  let E := Function.Embedding.subtype (· ∈ V)
  have card : Fintype.card V = h := (Fintype.card_coe _).trans hV
  let _ : Nonempty V := Fintype.card_pos_iff.mp (card ▸ (by omega : 0 < h))
  have fails : (ε : ℝ≥0∞) < epsMCA (F := F) (ReedSolomon.code E j : Set (V → F)) 1 := by
    apply lt_of_not_ge
    intro good
    have bound := (ToleranceCircuitCriterion.endpoint_iff E hj (card ▸ hjh) ε hs).mp good
    rw [card] at bound
    exact hB.not_ge bound
  let r : ℝ≥0 := 1 - ((j + 1 : ℕ) : ℝ≥0) / h
  have plateau : epsMCA (F := F) (ReedSolomon.code E j : Set (V → F)) r =
      epsMCA (F := F) (ReedSolomon.code E j : Set (V → F)) 1 := by
    apply epsMCA_eq_epsMCA_one_of_le_succ
    simpa [r, card, Nat.cast_add_one] using (capacityPred_le_succ_hyp (ι := V) j)
  rw [epsMCA_interleaved_eq]
  exact ((fails.trans_eq plateau.symm).trans_le (lift j hj r)).trans_le (epsMCA_mono _ hδ)

/-- If the base has enough interpolation circuits to make every scalar bad on
one line, every lift has worst-case error one at the same relative radius. -/
theorem full_from_base (D : I ↪ F) [ReedSolomon.Smooth D]
    {b h j l m : ℕ} (hm : 0 < m) (hn : Fintype.card I = m * h) (hp : h = 2 ^ b)
    (hh : 1024 ≤ h) (hj : 128 ≤ j) (hjh : 128 ≤ h - (j + 1)) [NeZero l]
    (hq : Fintype.card F < 2 ^ 256) {δ : ℝ≥0} (hδ : 1 - ((j + 1 : ℕ) : ℝ≥0) / h ≤ δ) :
    epsMCA (F := F) ((ReedSolomon.code D (j * m) : Set (I → F)) ^⋈ (Fin l)) δ = 1 := by
  classical
  obtain ⟨V, hV, _, _, sm, lift⟩ := SmoothPowerMcaDescent.exists_smooth_base D hm hn ⟨b, hp⟩
  let E := Function.Embedding.subtype (· ∈ V)
  have card : Fintype.card V = h := (Fintype.card_coe _).trans hV
  let _ : Nonempty V := Fintype.card_pos_iff.mp (card ▸ (by omega : 0 < h))
  have full := (JointDyadicCeilings.dense_saturation (m := l) E (card ▸ hh) hj
    (card ▸ hjh) hq (card ▸ hδ)).1
  rw [epsMCA_interleaved_eq] at full ⊢
  apply le_antisymm (epsMCA_le_one _ _)
  exact full.symm.trans_le (lift j (by omega) δ)

end ProximityPrize.SmoothCapacityGap
