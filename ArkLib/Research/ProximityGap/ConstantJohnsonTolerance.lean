/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.JointJohnsonEquality
import ArkLib.Research.ProximityGap.ToleranceCircuitCriterion
import Mathlib.NumberTheory.PrimesCongruentOne

/-! # Dimension-one simultaneous Johnson cutoffs at any positive tolerance

If the integer budget covers the length and all two-site interpolation circuits,
MCA is safe throughout and every positive-width list is safe below one.
For any positive tolerance there are arbitrarily large prime fields meeting
this condition and containing a smooth subgroup of the requested prize length.
-/

namespace ProximityPrize.ConstantJohnsonTolerance

open Code FullPrizeReview ProximityGap ProximityGap.MCAThresholdLedger RankJohnsonComparison
open scoped NNReal ENNReal

variable {F I : Type} [Field F] [Fintype F] [Fintype I] [Nonempty I]

/-- A dimension-one list has operational cutoff one precisely when its integer budget
covers all the sites. At the last grid point before one, every constant word in the
list needs a distinct site and equality is achievable. -/
theorem list_cutoff_iff (D : I ↪ F) (ε : ℝ≥0) {m : ℕ} (hm : 0 < m) :
    cutoff (RankReview.listAnswer D ε 1 m) = Fintype.card I ↔
      Fintype.card I ≤ RankReview.budget F ε := by
  classical
  have hn : 0 < Fintype.card I := Fintype.card_pos
  have spec := RankReview.listAnswer_correct D ε 1 m hn
  have h := SixteenJohnsonSeparation.safe_grid_iff spec
    (e := Fintype.card I - 1) (by omega)
  let r : ℝ := (((Fintype.card I - 1 : ℕ) : ℝ≥0) / Fintype.card I : ℝ≥0)
  have rounded := ListSupportRank.lambda_le_floor_iff (K := F)
    (ListInterpolationBoundary.words D 1 m) r ε
  have test := rounded.symm.trans h
  have count := ListInterpolationBoundary.at_dimension_agreement D (k := 1) (by decide) hn hm
  simp only [Nat.choose_one_right] at count
  change Lambda (ListInterpolationBoundary.words D 1 m) r ≤ (RankReview.budget F ε : ℕ∞) ↔ _
    at test
  simp only [r, NNReal.coe_div, NNReal.coe_natCast] at test
  rw [count, Nat.cast_le] at test
  have bound := cutoff_le (RankReview.listAnswer D ε 1 m)
  omega

/-- Every input whose integer budget covers the number of pairs of sites is MCA-safe
at all radii in dimension one. -/
theorem mca_all_safe (D : I ↪ F) (ε : ℝ≥0)
    (cover : (Fintype.card I).choose 2 ≤ RankReview.budget F ε) :
    RankReview.mcaAnswer D ε 1 = none := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  apply correctBoundary_unique Fintype.card_pos (RankReview.mcaAnswer_correct D ε 1)
  intro δ unit
  simp only [iff_true]
  rw [← epsMCA_eq_mcaError]
  apply (epsMCA_mono _ unit).trans
  rw [SimultaneousSupportRank.epsMCA_le_iff_floor_budget]
  exact (epsMCA_one_le_choose_div D 1).trans
    (ENNReal.div_le_div_right (by exact_mod_cast cover) _)

/-- For every positive tolerance and every lower bound on the field size there is
a larger prime field with a smooth prize-length domain on which both operational
cutoffs equal Johnson in dimension one. No upper bound on the field is imposed. -/
theorem arbitrarily_large {n : ℕ} (hr : hasPrizeRate n 1) (ε : ℝ≥0) (positive : 0 < ε)
    (lower : ℕ) :
    ∃ (p : ℕ) (_ : Fact p.Prime), lower < p ∧ ∃ D : Fin n ↪ ZMod p,
      Nonempty (ReedSolomon.Smooth D) ∧ RankReview.mcaAnswer D ε 1 = none ∧
        ∀ m : ℕ, 0 < m → cutoff (RankReview.listAnswer D ε 1 m) = n := by
  have sizes : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16 := by
    rcases hr with h | h | h | h <;> omega
  have hn : 0 < n := by omega
  let _ : NeZero n := ⟨hn.ne'⟩
  have dyad : ∃ j : ℕ, n = 2 ^ j := by
    rcases sizes with rfl | rfl | rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  let R := max n (n.choose 2)
  obtain ⟨b, hb⟩ := exists_nat_gt ((R : ℝ≥0) / ε)
  obtain ⟨p, prime, large, residue⟩ := Nat.exists_prime_gt_modEq_one (max b lower) hn.ne'
  let _ : Fact p.Prime := ⟨prime⟩
  obtain ⟨D, sm⟩ := SmoothPowerMcaDescent.exists_prime_domain (p := p)
    ((Nat.modEq_iff_dvd' prime.pos).mp residue.symm) dyad
  have fits : R ≤ RankReview.budget (ZMod p) ε := by
    apply Nat.le_floor
    rw [ZMod.card, mul_comm]
    apply (div_le_iff₀ positive).mp
    exact hb.le.trans (by exact_mod_cast (le_max_left b lower).trans large.le)
  refine ⟨p, inferInstance, (le_max_right b lower).trans_lt large, D, sm, ?_, ?_⟩
  · apply mca_all_safe
    simpa only [Fintype.card_fin] using (le_max_right n (n.choose 2)).trans fits
  · intro m hm
    exact ((list_cutoff_iff D ε hm).mpr (by
      simpa only [Fintype.card_fin] using (le_max_left n (n.choose 2)).trans fits)).trans
        (Fintype.card_fin n)

end ProximityPrize.ConstantJohnsonTolerance
