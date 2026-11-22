/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.SmoothCapacityGap
import ArkLib.Research.ProximityGap.Frontier.LocatorPadding

/-! # Equal power fibers after puncturing a smooth domain -/

namespace ProximityPrize.PuncturedSmoothMca

open Finset Polynomial ProximityGap
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Field F] [DecidableEq F]

/-- Removing a single power value removes exactly one fiber. The remaining coordinates
project onto the remaining values with the same fiber cardinality. -/
theorem exists_punctured_projection (D : I ↪ F) [ReedSolomon.Smooth D] {m h : ℕ}
    (hn : Fintype.card I = m * h) (hh : 0 < h) :
    ∃ (U : Finset F) (S : Finset I), U.card = h - 1 ∧ S.card = m * (h - 1) ∧
      ∃ π : S → U, (∀ i, (D i.val) ^ m = (π i).val) ∧
        ∀ v, (univ.filter fun i => π i = v).card = m := by
  classical
  obtain ⟨V, hV, hmem, hfib, _⟩ :=
    CodingTheory.AdditiveSetListDecoding.Smooth.exists_pow_projection_structure D hn
  obtain ⟨y, hy⟩ := card_pos.mp (hh.trans_eq hV.symm)
  let U := V.erase y
  let S := univ.filter fun i => D i ^ m ≠ y
  have hS : S.card = m * (h - 1) := by
    have sum := card_filter_add_card_filter_not (s := univ) (fun i => D i ^ m = y)
    have split : m * h = m * (h - 1) + m := by
      conv_lhs => rw [show h = h - 1 + 1 by omega, Nat.mul_add, Nat.mul_one]
    rw [hfib y hy, card_univ, hn, split] at sum
    change (univ.filter fun i => D i ^ m ≠ y).card = _
    exact Nat.add_left_cancel (sum.trans (Nat.add_comm _ _))
  let π (i : S) : U := ⟨D i.val ^ m, mem_erase.mpr ⟨(mem_filter.mp i.property).2, hmem _⟩⟩
  refine ⟨U, S, (card_erase_of_mem hy).trans (congrArg (· - 1) hV), hS, π, fun _ => rfl, ?_⟩
  intro v
  have hv := mem_erase.mp v.property
  let old := Function.Embedding.subtype (· ∈ S)
  have agrees : (univ.filter (fun i => π i = v)).map old =
      univ.filter (fun i => D i ^ m = v.val) := by
    ext i
    constructor
    · intro hi
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hi
      exact mem_filter.mpr ⟨mem_univ _, congrArg Subtype.val (mem_filter.mp ha).2⟩
    · intro hi
      have he := (mem_filter.mp hi).2
      have hiS : i ∈ S := mem_filter.mpr ⟨mem_univ _, he ▸ hv.1⟩
      exact mem_map.mpr ⟨⟨i, hiS⟩, mem_filter.mpr ⟨mem_univ _, Subtype.ext he⟩, rfl⟩
  rw [← card_map old, agrees, hfib _ hv.2]


variable [Fintype F] [Nonempty I]

private theorem support_size {n t : ℕ} (hn : 0 < n) (ht : t ≤ n) :
    (1 - (1 - (t : ℝ≥0) / n)) * n = t := by
  have hp : 0 < (n : ℝ≥0) := by exact_mod_cast hn
  rw [tsub_tsub_cancel_of_le ((div_le_one hp).mpr (by exact_mod_cast ht)), div_mul_cancel₀ _ hp.ne']

/-- A single omitted power fiber supplies enough fresh coordinates for a degree
locator of size `m-1`. Every line on the punctured base retains its bad-scalar
mass at `(j+2)m-1` agreements and dimension `jm` on the original domain. -/
theorem transfer (D : I ↪ F) [ReedSolomon.Smooth D] {m h j : ℕ} (hn : Fintype.card I = m * h)
    (hm : 0 < m) (hj : 0 < j) (hjh : j < h - 1) {δ : ℝ≥0}
    (hδ : 1 - ((((j + 2) * m - 1 : ℕ) : ℝ≥0) / Fintype.card I) ≤ δ) :
    ∃ U : Finset F, U.card = h - 1 ∧
      epsMCA (F := F) (ReedSolomon.code (Function.Embedding.subtype (· ∈ U)) j : Set (U → F))
          (1 - ((j + 1 : ℕ) : ℝ≥0) / (h - 1 : ℕ)) ≤
        epsMCA (F := F) (ReedSolomon.code D (j * m) : Set (I → F)) δ := by
  classical
  obtain ⟨U, S, hU, hS, π, hdom, hfib⟩ := exists_punctured_projection D hn (by omega)
  have cU : Fintype.card U = h - 1 := (Fintype.card_coe _).trans hU
  have cS : Fintype.card S = m * (h - 1) := (Fintype.card_coe _).trans hS
  let _ : Nonempty U := Fintype.card_pos_iff.mp (cU ▸ (by omega : 0 < h - 1))
  let _ : Nonempty S := Fintype.card_pos_iff.mp (cS ▸ Nat.mul_pos hm (by omega))
  let old := Function.Embedding.subtype (· ∈ S)
  let E := Function.Embedding.subtype (· ∈ U)
  let σ : ℝ≥0 := 1 - ((j + 1 : ℕ) : ℝ≥0) / (h - 1 : ℕ)
  let τ : ℝ≥0 := 1 - (((j + 2) * m - 1 : ℕ) : ℝ≥0) / Fintype.card I
  let K := (j - 1) * m + 1
  have dim : K + (m - 1) = j * m := by
    have add : j * m = (j - 1) * m + m := by
      conv_lhs => rw [show j = j - 1 + 1 by omega, Nat.add_mul, one_mul]
    dsimp [K]
    omega
  have lift := FullFiberMcaLift.epsMCA_le_band (old.trans D) E π (X ^ m) hm hj
    (show (j - 1) * m < K by exact Nat.lt_succ_self _) (show K ≤ j * m by omega)
    (by simp) (fun i => by simpa [old, E] using hdom i) hfib σ
  have length : m * h = m * (h - 1) + m := by
    conv_lhs => rw [show h = h - 1 + 1 by omega, Nat.mul_add, Nat.mul_one]
  have counts : (j + 2) * m - 1 = (j + 1) * m + (m - 1) := by
    rw [show j + 2 = j + 1 + 1 by omega, Nat.add_mul, one_mul]
    omega
  have fits : (j + 2) * m - 1 ≤ Fintype.card I := by
    rw [hn, Nat.mul_comm m h]
    exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_right m (by omega))
  have oldSize : (1 - σ) * (Fintype.card S : ℝ≥0) = ((j + 1) * m : ℕ) := by
    rw [cS, Nat.mul_comm m, Nat.cast_mul, ← mul_assoc, support_size (by omega) (by omega),
      Nat.cast_mul]
  have pad := LocatorPadding.epsMCA_le D old (k := K) (r := m - 1) (by dsimp [K]; omega)
    (by rw [cS, hn, length]; omega) (δ := σ) (δ' := τ) (by
      intro t ht
      rw [oldSize] at ht
      rw [show (1 - τ) * (Fintype.card I : ℝ≥0) = ((j + 2) * m - 1 : ℕ) from
        support_size Fintype.card_pos fits, counts]
      exact_mod_cast Nat.add_le_add_right (by exact_mod_cast ht : (j + 1) * m ≤ t) (m - 1))
  rw [dim] at pad
  exact ⟨U, hU, (lift.trans pad).trans (epsMCA_mono _ hδ)⟩


/-- More interpolation circuits than the tolerance budget force failure at the
padded radius. The circuit-separation hypothesis refers to the actual field. -/
theorem failure (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0) {m h j l : ℕ} [NeZero l]
    (hn : Fintype.card I = m * h) (hm : 0 < m) (hj : 0 < j) (hjh : j < h - 1)
    (sep : (RankReview.budget F ε + 1).choose 2 ≤ Fintype.card F)
    (count : RankReview.budget F ε < (h - 1).choose (j + 1)) {δ : ℝ≥0}
    (hδ : 1 - ((((j + 2) * m - 1 : ℕ) : ℝ≥0) / Fintype.card I) ≤ δ) :
    (ε : ℝ≥0∞) < epsMCA (F := F) ((ReedSolomon.code D (j * m) : Set (I → F)) ^⋈ (Fin l)) δ := by
  classical
  obtain ⟨U, hU, lift⟩ := transfer D hn hm hj hjh hδ
  have card : Fintype.card U = h - 1 := (Fintype.card_coe _).trans hU
  let _ : Nonempty U := Fintype.card_pos_iff.mp (card ▸ (by omega : 0 < h - 1))
  let E := Function.Embedding.subtype (· ∈ U)
  have bad : (ε : ℝ≥0∞) < epsMCA (F := F) (ReedSolomon.code E j : Set (U → F)) 1 := by
    apply lt_of_not_ge
    intro safe
    have bound := (ToleranceCircuitCriterion.endpoint_iff E hj (card ▸ hjh) ε sep).mp safe
    exact count.not_ge (card ▸ bound)
  have same := epsMCA_eq_epsMCA_one_of_le_succ E j (capacityPred_le_succ_hyp (ι := U) j)
  rw [card, ← Nat.cast_add_one] at same
  rw [epsMCA_interleaved_eq]
  exact (bad.trans_eq same.symm).trans_le lift

/-- Enough punctured-base circuits make every scalar bad on a single line,
and the full-fiber and locator lifts preserve that line's bad-scalar mass. -/
theorem saturated (D : I ↪ F) [ReedSolomon.Smooth D] {m h j l : ℕ} [NeZero l]
    (hn : Fintype.card I = m * h) (hm : 0 < m) (hj : 0 < j) (hjh : j < h - 1)
    (count : (Fintype.card F - 1) ^ 2 < (h - 1).choose (j + 1)) {δ : ℝ≥0}
    (hδ : 1 - ((((j + 2) * m - 1 : ℕ) : ℝ≥0) / Fintype.card I) ≤ δ) :
    epsMCA (F := F) ((ReedSolomon.code D (j * m) : Set (I → F)) ^⋈ (Fin l)) δ = 1 := by
  classical
  obtain ⟨U, hU, lift⟩ := transfer D hn hm hj hjh hδ
  have card : Fintype.card U = h - 1 := (Fintype.card_coe _).trans hU
  let _ : Nonempty U := Fintype.card_pos_iff.mp (card ▸ (by omega : 0 < h - 1))
  let _ : SampleableType F := SampleableType.ofFintype _
  let E := Function.Embedding.subtype (· ∈ U)
  let e := (Fintype.equivFin U).symm
  let x := e.toEmbedding.trans E
  let _ : NeZero (Fintype.card U) := ⟨Fintype.card_ne_zero⟩
  let r : ℝ≥0 := 1 - ((j + 1 : ℕ) : ℝ≥0) / (h - 1 : ℕ)
  have size : (1 - r) * (Fintype.card (Fin (Fintype.card U)) : ℝ≥0) = (j + 1 : ℕ) := by
    rw [Fintype.card_fin, card]
    exact support_size (by omega) (by omega)
  have full : epsMCA (F := F) (ReedSolomon.code E j : Set (U → F)) r = 1 := by
    rw [ArkLib.ProximityGap.Frontier.MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq
      e x E (fun _ => rfl), epsMCA_eq_mcaError]
    apply BoundaryFullMass.mcaError_eq_one x hj
    · rw [size]
      exact_mod_cast Nat.lt_succ_self j
    · rw [size]
    · rwa [card]
  rw [epsMCA_interleaved_eq]
  exact le_antisymm (epsMCA_le_one _ _) (full.symm.trans_le lift)

end ProximityPrize.PuncturedSmoothMca
