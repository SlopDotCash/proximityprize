/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.KKH26DeltaStarReduction
import ArkLib.Data.CodingTheory.ProximityGap.Lattice2.Spec
import ArkLib.Data.CodingTheory.ProximityGap.MCAListBracketInterpolation

/-!
# The KKH26 open ceiling as a faithful lattice threshold

The operational supremum in `KKH26DeltaStarReduction` is not attained: the KKH26 ceiling
radius is bad, while every smaller radius is good.  On the faithful `1 / n` lattice this
means that the exact threshold is the lattice point immediately before the ceiling.
-/

open scoped NNReal ENNReal

namespace ProximityGap.GrandChallengesLattice

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- If the lattice point `s / n` is bad and every smaller real radius is good, then the
faithful lattice threshold is the preceding index `s - 1`.  This is the exact one-rung
translation from an unattained operational supremum to the maximal good lattice point. -/
theorem mcaThreshold_eq_pred_of_good_below_bad_at_lattice
    (C : Set (ι → F)) (εstar : ℝ≥0) (s : ℕ)
    (hs0 : 0 < s) (hsn : s ≤ Fintype.card ι)
    (hgood : ∀ δ : ℝ≥0,
      δ < (s : ℝ≥0) / (Fintype.card ι : ℝ≥0) →
        epsMCA (F := F) (A := F) C δ ≤ (εstar : ENNReal))
    (hbad : (εstar : ENNReal) <
      epsMCA (F := F) (A := F) C
        ((s : ℝ≥0) / (Fintype.card ι : ℝ≥0))) :
    ∃ hne : mcaThresholdExists C εstar,
      mcaThreshold C εstar hne =
        (⟨s - 1, by omega⟩ : Fin (Fintype.card ι + 1)) := by
  let pred : Fin (Fintype.card ι + 1) := ⟨s - 1, by omega⟩
  let ceil : Fin (Fintype.card ι + 1) := ⟨s, by omega⟩
  have hpred_lt :
      mcaLatticePoint (Fintype.card ι) pred <
        mcaLatticePoint (Fintype.card ι) ceil := by
    unfold mcaLatticePoint
    apply (div_lt_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos)).2
    exact_mod_cast (by simp only [pred, ceil]; omega : pred.val < ceil.val)
  have hceil_radius :
      mcaLatticePoint (Fintype.card ι) ceil =
        (s : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
    rfl
  have hpred_sat : mcaSatisfies C εstar pred := by
    exact hgood _ (hceil_radius ▸ hpred_lt)
  let hne : mcaThresholdExists C εstar := ⟨pred, hpred_sat⟩
  refine ⟨hne, ?_⟩
  have hmax : ∀ i : Fin (Fintype.card ι + 1),
      mcaSatisfies C εstar i → i ≤ pred := by
    intro i hi
    by_contra hnot
    have hpredi : pred < i := lt_of_not_ge hnot
    have hceili : ceil ≤ i := by
      rw [Fin.le_iff_val_le_val]
      change s - 1 < i.val at hpredi
      change s ≤ i.val
      omega
    have hceil_sat : mcaSatisfies C εstar ceil :=
      mcaSatisfies_downward_closed C εstar hceili hi
    exact (not_lt_of_ge (hceil_radius ▸ hceil_sat)) hbad
  exact (mcaThreshold_unique C εstar hne pred hpred_sat hmax).symm

/-- The same jump data simultaneously determines the two faithful threshold notions.
The operational threshold is the (bad, unattained) boundary `s / n`, while the lattice
threshold is the preceding maximal-good index `s - 1`. -/
theorem mcaDeltaStar_and_mcaThreshold_eq_pred_of_good_below_bad_at_lattice
    (C : Set (ι → F)) (εstar : ℝ≥0) (s : ℕ)
    (hs0 : 0 < s) (hsn : s ≤ Fintype.card ι)
    (hgood : ∀ δ : ℝ≥0,
      δ < (s : ℝ≥0) / (Fintype.card ι : ℝ≥0) →
        epsMCA (F := F) (A := F) C δ ≤ (εstar : ENNReal))
    (hbad : (εstar : ENNReal) <
      epsMCA (F := F) (A := F) C
        ((s : ℝ≥0) / (Fintype.card ι : ℝ≥0))) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := F) C (εstar : ENNReal) =
        (s : ℝ≥0) / (Fintype.card ι : ℝ≥0) ∧
      ∃ hne : mcaThresholdExists C εstar,
        mcaThreshold C εstar hne =
          (⟨s - 1, by omega⟩ : Fin (Fintype.card ι + 1)) := by
  constructor
  · refine MCAListBracketInterpolation.mcaDeltaStar_eq_of_jump
      (F := F) (A := F) C (εstar : ENNReal) ?_ hgood hbad
    rw [div_le_one (by exact_mod_cast Fintype.card_pos)]
    exact_mod_cast hsn
  · exact mcaThreshold_eq_pred_of_good_below_bad_at_lattice
      C εstar s hs0 hsn hgood hbad

/-- A witness-carrying `GrandMCAResolution` cannot represent an unattained interior jump.
If its proposed cutoff is at or above the bad boundary, monotonicity contradicts its
`bound`; if it is below the boundary, an intermediate good radius contradicts its
`maximal` field. -/
theorem not_nonempty_GrandMCAResolution_of_good_below_bad_at_lattice
    (C : Set (ι → F)) (εstar : ℝ≥0) (s : ℕ)
    (hs0 : 0 < s) (hsn : s ≤ Fintype.card ι)
    (hgood : ∀ δ : ℝ≥0,
      δ < (s : ℝ≥0) / (Fintype.card ι : ℝ≥0) →
        epsMCA (F := F) (A := F) C δ ≤ (εstar : ENNReal))
    (hbad : (εstar : ENNReal) <
      epsMCA (F := F) (A := F) C
        ((s : ℝ≥0) / (Fintype.card ι : ℝ≥0))) :
    ¬ Nonempty (GrandChallenges.GrandMCAResolution C εstar) := by
  rintro ⟨R⟩
  have hboundary_le_one :
      (s : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast Fintype.card_pos)]
    exact_mod_cast hsn
  rcases lt_or_ge R.δStar
      ((s : ℝ≥0) / (Fintype.card ι : ℝ≥0)) with hbelow | hat_or_above
  · obtain ⟨δ, hRδ, hδboundary⟩ := exists_between hbelow
    have hfail := R.maximal δ hRδ (le_trans hδboundary.le hboundary_le_one)
    exact (not_lt_of_ge (hgood δ hδboundary)) hfail
  · have hboundary_good :
        epsMCA (F := F) (A := F) C
            ((s : ℝ≥0) / (Fintype.card ι : ℝ≥0)) ≤ (εstar : ENNReal) :=
      le_trans (epsMCA_mono (F := F) (A := F) C hat_or_above) R.bound
    exact (not_lt_of_ge hboundary_good) hbad

/-- Four prize-rate instances of the open-ceiling pattern resolve the faithful prize
predicate.  The proposed threshold at rate `j` is the predecessor of the first bad
lattice index `s j`. -/
theorem mcaPrizeLatticeResolved_of_good_below_bad_at_lattice
    (domain : ι ↪ F) (s : Fin 4 → ℕ)
    (hs0 : ∀ j : Fin 4, 0 < s j)
    (hsn : ∀ j : Fin 4, s j ≤ Fintype.card ι)
    (hgood : ∀ (j : Fin 4) (δ : ℝ≥0),
      δ < (s j : ℝ≥0) / (Fintype.card ι : ℝ≥0) →
        epsMCA (F := F) (A := F)
          (ReedSolomon.code domain
            ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) δ
          ≤ (epsStar : ENNReal))
    (hbad : ∀ j : Fin 4, (epsStar : ENNReal) <
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        ((s j : ℝ≥0) / (Fintype.card ι : ℝ≥0))) :
    mcaPrizeLatticeResolved domain
      (fun j => ⟨s j - 1, by have := hsn j; omega⟩) := by
  intro j
  simpa only using
    (mcaThreshold_eq_pred_of_good_below_bad_at_lattice
      (C := (ReedSolomon.code domain
        ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
      (εstar := epsStar) (s := s j) (hs0 j) (hsn j) (hgood j) (hbad j))

end ProximityGap.GrandChallengesLattice

namespace ProximityGap.KKH26DeltaStarReduction

open ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.GrandChallengesLattice

/-- The KKH26 ceiling is exactly lattice point `(n - r*m) / n`. -/
private theorem ceiling_eq_latticePoint
    {n μ m r : ℕ} (hμ : 1 ≤ μ) (hm : 1 ≤ m)
    (hn : n = 2 ^ μ * m) (hr : r ≤ 2 ^ (μ - 1)) :
    ((n - r * m : ℕ) : ℝ≥0) / (n : ℝ≥0) =
      1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  have hrpow : r ≤ 2 ^ μ :=
    le_trans hr (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hrm : r * m ≤ n := by
    rw [hn]
    exact Nat.mul_le_mul_right m hrpow
  have hfrac : (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hrpow
  apply NNReal.eq
  rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast,
    NNReal.coe_sub hfrac, NNReal.coe_one, NNReal.coe_div,
    NNReal.coe_natCast, NNReal.coe_pow]
  push_cast [Nat.cast_sub hrm]
  rw [hn]
  push_cast
  field_simp

/-- **KKH26 operational-to-lattice bridge.**  `InteriorCeiling` makes every radius below
`1 - r / 2^μ` good, while the KKH26 witness spread makes that ceiling itself bad.  Since
the ceiling is lattice index `n - r*m`, the faithful maximal good index is exactly its
predecessor `n - r*m - 1`.

The target threshold is an `ℝ≥0`, as required by the faithful lattice API; it is coerced
to `ENNReal` for the operational KKH26 estimates. -/
theorem kkh26_mcaThreshold_eq_pred_ceiling_of_bad
    {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0)
    (hceiling : InteriorCeiling p n g μ m r (εstar : ENNReal))
    (hbad_ceiling : (εstar : ENNReal) <
      epsMCA (F := ZMod p) (A := ZMod p)
        (evalCode g n ((r - 2) * m))
          (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ))) :
    ∃ hne : mcaThresholdExists
        (evalCode g n ((r - 2) * m)) εstar,
      (mcaThreshold (evalCode g n ((r - 2) * m)) εstar hne).val =
        n - r * m - 1 := by
  have hrpow_lt : r < 2 ^ μ :=
    lt_of_le_of_lt hr (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hrm_lt : r * m < n := by
    rw [hn]
    exact (Nat.mul_lt_mul_right hm).2 hrpow_lt
  have hs0 : 0 < n - r * m := Nat.sub_pos_of_lt hrm_lt
  have hsn : n - r * m ≤ Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]
    omega
  have hδeq :
      ((n - r * m : ℕ) : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0) =
        1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
    simpa only [Fintype.card_fin] using ceiling_eq_latticePoint hμ hm hn hr
  have hgood : ∀ δ : ℝ≥0,
      δ < ((n - r * m : ℕ) : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0) →
        epsMCA (F := ZMod p) (A := ZMod p)
          (evalCode g n ((r - 2) * m)) δ ≤ (εstar : ENNReal) := by
    intro δ hδ
    exact hceiling δ (hδeq ▸ hδ)
  have hbad : (εstar : ENNReal) <
      epsMCA (F := ZMod p) (A := ZMod p)
        (evalCode g n ((r - 2) * m))
          (((n - r * m : ℕ) : ℝ≥0) /
            (Fintype.card (Fin n) : ℝ≥0)) := by
    rwa [hδeq]
  obtain ⟨hne, hthreshold⟩ :=
    mcaThreshold_eq_pred_of_good_below_bad_at_lattice
      (ι := Fin n) (F := ZMod p)
      (evalCode g n ((r - 2) * m)) εstar (n - r * m)
      hs0 hsn hgood hbad
  refine ⟨hne, ?_⟩
  rw [hthreshold]

end ProximityGap.KKH26DeltaStarReduction

#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_eq_pred_of_good_below_bad_at_lattice
#print axioms ProximityGap.GrandChallengesLattice.mcaDeltaStar_and_mcaThreshold_eq_pred_of_good_below_bad_at_lattice
#print axioms ProximityGap.GrandChallengesLattice.not_nonempty_GrandMCAResolution_of_good_below_bad_at_lattice
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_of_good_below_bad_at_lattice
#print axioms ProximityGap.KKH26DeltaStarReduction.kkh26_mcaThreshold_eq_pred_ceiling_of_bad
