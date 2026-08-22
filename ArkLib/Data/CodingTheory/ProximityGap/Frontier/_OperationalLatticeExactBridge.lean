/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Lattice2.Witnesses
import ArkLib.Data.CodingTheory.ProximityGap.MCAListBracketInterpolation

/-!
# Exact conversion between the operational and lattice MCA thresholds

For a finite code, the operational supremum is itself quantized.  If the maximal good
lattice index is `t < n`, then the operational threshold is the *next* lattice point
`(t+1)/n`, which is the first bad radius.  If the top lattice point is good, both notions
equal one.

This is the global version of the one-rung conversion used by the KKH26 ceiling bridge.
In particular, any proposed exact real-valued formula for `mcaDeltaStar` must include the
Hamming-lattice rounding: an unrounded entropy/asymptotic expression can at most describe
the location of the threshold before this conversion.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal

namespace ProximityGap.GrandChallengesLattice

open MCAThresholdLedger MCAListBracketInterpolation

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- If the faithful maximal-good lattice index is not the top point, the operational
supremum is exactly its successor.  The successor is bad, while every smaller real radius
rounds down to a good lattice index. -/
theorem mcaDeltaStar_eq_succ_mcaThreshold
    (C : Set (ι → F)) (εstar : ℝ≥0)
    (hne : mcaThresholdExists C εstar)
    (hlt : (mcaThreshold C εstar hne).val < Fintype.card ι) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := F) C (εstar : ENNReal) =
      mcaLatticePoint (Fintype.card ι)
        ⟨(mcaThreshold C εstar hne).val + 1, by omega⟩ := by
  let t : Fin (Fintype.card ι + 1) := mcaThreshold C εstar hne
  let s : Fin (Fintype.card ι + 1) := ⟨t.val + 1, by
    change t.val + 1 < Fintype.card ι + 1
    omega⟩
  have hts : t < s := by
    rw [Fin.lt_iff_val_lt_val]
    simp only [s]
    omega
  have hsbad : (εstar : ENNReal) <
      epsMCA (F := F) (A := F) C (mcaLatticePoint (Fintype.card ι) s) := by
    by_contra hnot
    push_neg at hnot
    have hsat : mcaSatisfies C εstar s := hnot
    have hle : s ≤ t := by
      simpa only [t] using le_mcaThreshold C εstar hne hsat
    exact (not_le_of_gt hts) hle
  apply mcaDeltaStar_eq_of_jump C (εstar : ENNReal)
      (mcaLatticePoint_le_one (Fintype.card ι) s) _ hsbad
  intro δ hδ
  have hδle : δ ≤ 1 :=
    le_trans hδ.le (mcaLatticePoint_le_one (Fintype.card ι) s)
  let i : Fin (Fintype.card ι + 1) := latticeIndexOf (ι := ι) δ hδle
  have hδmul : δ * (Fintype.card ι : ℝ≥0) < (s.val : ℝ≥0) := by
    have hn : (0 : ℝ≥0) < Fintype.card ι := by
      exact_mod_cast Fintype.card_pos
    simpa only [mcaLatticePoint] using (lt_div_iff₀ hn).mp hδ
  have his : i < s := by
    rw [Fin.lt_iff_val_lt_val]
    rw [show i.val = Nat.floor (δ * (Fintype.card ι : ℝ≥0)) from rfl]
    exact (Nat.floor_lt (zero_le _)).mpr hδmul
  have hit : i ≤ t := by
    exact Fin.le_iff_val_le_val.mpr (by
      have := Fin.lt_iff_val_lt_val.mp his
      simp only [s] at this
      omega)
  have hisat : mcaSatisfies C εstar i :=
    mcaSatisfies_downward_closed C εstar hit
      (by simpa only [t] using mcaThreshold_spec C εstar hne)
  unfold mcaSatisfies at hisat
  rw [epsMCA_eq_at_latticeIndex C δ hδle]
  exact hisat

/-- If the maximal-good lattice index is the top point, the operational threshold is one. -/
theorem mcaDeltaStar_eq_one_of_mcaThreshold_eq_top
    (C : Set (ι → F)) (εstar : ℝ≥0)
    (hne : mcaThresholdExists C εstar)
    (htop : (mcaThreshold C εstar hne).val = Fintype.card ι) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := F) C (εstar : ENNReal) = 1 := by
  let top : Fin (Fintype.card ι + 1) :=
    ⟨Fintype.card ι, Nat.lt_succ_self _⟩
  have hthreshold : mcaThreshold C εstar hne = top := by
    apply Fin.ext
    simpa only [top] using htop
  have hgood : epsMCA (F := F) (A := F) C 1 ≤ (εstar : ENNReal) := by
    have hsat := mcaThreshold_spec C εstar hne
    rw [hthreshold] at hsat
    simpa [mcaSatisfies, top] using hsat
  apply le_antisymm
  · unfold MCAThresholdLedger.mcaDeltaStar
    exact csSup_le' fun _ h => h.1
  · exact le_mcaDeltaStar_of_good (F := F) (A := F) C (εstar : ENNReal) le_rfl hgood

/-- **Operational quantization.** Whenever at least one good lattice point exists, the
operational MCA threshold is one of the `n+1` Hamming lattice points.  At an interior
threshold it is the first bad point, one rung above the faithful maximal-good index. -/
theorem exists_latticePoint_eq_mcaDeltaStar
    (C : Set (ι → F)) (εstar : ℝ≥0)
    (hne : mcaThresholdExists C εstar) :
    ∃ j : Fin (Fintype.card ι + 1),
      MCAThresholdLedger.mcaDeltaStar (F := F) (A := F) C (εstar : ENNReal) =
        mcaLatticePoint (Fintype.card ι) j := by
  by_cases htop : (mcaThreshold C εstar hne).val = Fintype.card ι
  · let top : Fin (Fintype.card ι + 1) :=
      ⟨Fintype.card ι, Nat.lt_succ_self _⟩
    refine ⟨top, ?_⟩
    rw [mcaDeltaStar_eq_one_of_mcaThreshold_eq_top C εstar hne htop]
    exact (mcaLatticePoint_top ι).symm
  · have hlt : (mcaThreshold C εstar hne).val < Fintype.card ι := by
      have hle := Nat.lt_succ_iff.mp (mcaThreshold C εstar hne).isLt
      omega
    let s : Fin (Fintype.card ι + 1) :=
      ⟨(mcaThreshold C εstar hne).val + 1, by omega⟩
    exact ⟨s, by
      simpa only [s] using mcaDeltaStar_eq_succ_mcaThreshold C εstar hne hlt⟩

end ProximityGap.GrandChallengesLattice

#print axioms ProximityGap.GrandChallengesLattice.mcaDeltaStar_eq_succ_mcaThreshold
#print axioms ProximityGap.GrandChallengesLattice.mcaDeltaStar_eq_one_of_mcaThreshold_eq_top
#print axioms ProximityGap.GrandChallengesLattice.exists_latticePoint_eq_mcaDeltaStar
