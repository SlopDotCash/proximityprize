/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.RankExecutable
import ArkLib.Research.ProximityGap.Frontier.ApolarMovingCount
import ArkLib.Data.CodingTheory.ProximityGap.UniversalSpikeFloor
import ArkLib.Data.CodingTheory.ProximityGap.MCAStaircaseRS
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger
import Mathlib.FieldTheory.Finite.GaloisField

/-! # A smooth sixteen-point prime-subfield grid at 128-bit tolerance

The nonzero elements of the prime subfield of `GF(17^32)` form a smooth evaluation
domain. Numbering them by the four-by-four grid will allow rows and columns to
serve as list witnesses. The scalar budget is six, and the first dimension-two
MCA failure is six errors.
-/

namespace ProximityPrize.JohnsonPrimePowerDomain

open Code ProximityGap ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open scoped NNReal ENNReal

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The extension field used for the 128-bit budget. -/
abbrev F := GaloisField 17 32

noncomputable instance : Fintype F := Fintype.ofFinite _
noncomputable instance : DecidableEq F := Classical.decEq _

/-- The four-by-four coordinate grid. -/
abbrev Grid := Fin 4 × Fin 4

theorem card_grid : Fintype.card Grid = 16 := by decide

theorem card_field : Fintype.card F = 17 ^ 32 :=
  Nat.card_eq_fintype_card.symm.trans (GaloisField.card 17 32 (by decide))

theorem field_lt : Fintype.card F < 2 ^ 256 := by rw [card_field]; decide

theorem budget : RankReview.budget F (prizeThreshold : ℝ≥0) = 6 := by
  rw [RankExecutable.prizeBudget, card_field]
  decide

private def residue (i : Grid) : ZMod 17 := 1 + (i.1.val : ZMod 17) + 4 * i.2.val

private def baseDomain : Grid ↪ ZMod 17 where
  toFun := residue
  inj' := by
    have h : ∀ i j : Grid, residue i = residue j → i = j := by decide
    exact fun {_ _} => h _ _

/-- The sixteen nonzero prime-field elements, enumerated by the row and column indices. -/
noncomputable def domain : Grid ↪ F :=
  baseDomain.trans ⟨algebraMap (ZMod 17) F, (algebraMap (ZMod 17) F).injective⟩

theorem coordinates (i : Grid) : domain i = 1 + (i.1.val : F) + 4 * (i.2.val : F) := by
  change algebraMap (ZMod 17) F (1 + (i.1.val : ZMod 17) + 4 * i.2.val) = _
  simp only [map_add, map_one, map_mul, map_natCast, map_ofNat]

/-- The grid is exactly the image of the full unit subgroup of the prime subfield. -/
noncomputable instance smoothDomain : ReedSolomon.Smooth domain where
  H := (⊤ : Subgroup (ZMod 17)ˣ).map (Units.map (algebraMap (ZMod 17) F).toMonoidHom)
  a := 1
  h_card_pow2 := ⟨4, card_grid⟩
  h_coset := by
    classical
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      have nz : ∀ i : Grid, residue i ≠ 0 := by decide
      let u := Units.mk0 (residue i) (nz i)
      exact ⟨_, ⟨u, Subgroup.mem_top _, rfl⟩, one_mul _⟩
    · rintro ⟨_, ⟨u, _, rfl⟩, rfl⟩
      have cover : ∀ z : ZMod 17, z ≠ 0 → ∃ i : Grid, residue i = z := by decide
      obtain ⟨i, hi⟩ := cover u u.ne_zero
      refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
      change algebraMap (ZMod 17) F (residue i) = 1 * algebraMap (ZMod 17) F (u : ZMod 17)
      rw [hi, one_mul]

private theorem below {δ : ℝ≥0} (hδ : δ < 6 / 16) :
    epsMCA (F := F) (ReedSolomon.code domain 2 : Set (Grid → F)) δ ≤ (prizeThreshold : ℝ≥0) := by
  rw [SimultaneousSupportRank.epsMCA_le_iff_floor_budget]
  change _ ≤ (RankReview.budget F (prizeThreshold : ℝ≥0) : ℝ≥0∞) / Fintype.card F
  rw [budget]
  apply epsMCA_le_of_badCount_le _ _ 6
  intro u
  let fam := canonicalBadScalarRichPointFamily domain δ u (by decide : 1 ≤ 2)
  change fam.G.card ≤ 6
  have count := ApolarMovingCount.count_mca_family (algebraMap F (AlgebraicClosure F))
    fam fam.G Finset.Subset.rfl (e := 5) (d := 13) (by decide) (by decide) (by decide)
    (by rw [card_grid]; decide) (by
      rw [card_grid]
      apply (Nat.add_one_le_ceil_iff (n := 10)).mpr
      have small : δ * 16 < 6 := (lt_div_iff₀ (by norm_num)).mp hδ
      rw [tsub_mul, one_mul]
      exact (lt_tsub_iff_right.mpr (by norm_num at small ⊢; linarith)))
  rw [card_grid] at count
  omega

private theorem fails :
    (prizeThreshold : ℝ≥0) < epsMCA (F := F) (ReedSolomon.code domain 2 : Set (Grid → F))
      (6 / 16) := by
  apply lt_of_not_ge
  intro safe
  rw [SimultaneousSupportRank.epsMCA_le_iff_floor_budget] at safe
  change _ ≤ (RankReview.budget F (prizeThreshold : ℝ≥0) : ℝ≥0∞) / Fintype.card F at safe
  rw [budget] at safe
  have fit : 7 ≤ Fintype.card Grid := by rw [card_grid]; decide
  obtain ⟨idx⟩ : Nonempty (Fin 7 ↪ Grid) := Function.Embedding.nonempty_of_card_le (by
    simp)
  have spike := SpikeFloor.epsMCA_ge_j_div_card (ReedSolomon.code domain 2)
    (MCAStaircaseRS.rs_noWeightLE domain (by rw [card_grid]; decide : 2 + 7 ≤ Fintype.card Grid))
    (δ := 6 / 16) (by rw [card_grid]; norm_num) (by decide) fit idx (idx.trans domain)
    (b := (1 : F)) one_ne_zero
  have h := spike.trans safe
  rw [ENNReal.div_le_iff (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _),
    ENNReal.div_mul_cancel (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _)] at h
  norm_num at h

/-- At every positive width the MCA supremum at rate one eighth is six errors out of sixteen. -/
theorem mca_supremum (m : ℕ) [NeZero m] :
    mcaDeltaStar (F := F) ((ReedSolomon.code domain 2 : Set (Grid → F)) ^⋈ (Fin m))
      (prizeThreshold : ℝ≥0) = 6 / 16 := by
  rw [mcaDeltaStar_interleaved_eq]
  exact MCAListBracketInterpolation.mcaDeltaStar_eq_of_jump _ _
    ((div_le_one (by norm_num : (0 : ℝ≥0) < 16)).mpr (by norm_num)) (fun _ => below) fails

/-- The universal MCA rank answer at 128-bit tolerance first fails at six errors. -/
theorem mca_answer : RankReview.mcaAnswer domain (prizeThreshold : ℝ≥0) 2 =
    some ⟨6, by rw [card_grid]; decide⟩ := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  apply FullPrizeReview.correctBoundary_unique Fintype.card_pos
    (RankReview.mcaAnswer_correct domain (prizeThreshold : ℝ≥0) 2)
  intro δ _
  change CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator F)
    (ReedSolomon.code domain 2) (δ : ℝ) ≤ _ ↔ δ < (6 : ℝ≥0) / Fintype.card Grid
  rw [← epsMCA_eq_mcaError, card_grid]
  exact ⟨fun good => lt_of_not_ge fun crossed =>
    (fails.trans_le (epsMCA_mono _ crossed)).not_ge good, fun h => below h⟩

end ProximityPrize.JohnsonPrimePowerDomain
