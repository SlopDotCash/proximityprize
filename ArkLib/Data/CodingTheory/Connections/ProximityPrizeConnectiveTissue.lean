/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Connections.SmoothDomainMCAWitness
import ArkLib.Data.CodingTheory.Connections.GKL24PetalWitnessCover

/-!
# Proximity-prize connective tissue

This file is a small checked wiring layer for the proximity-prize cone.  It does not assert the
open `δ*` breakthrough.  Instead it records reusable bridges that were previously spread across
several files:

* the GCXK25/ABF26 Johnson lift is named once as `johnsonLift`;
* any `ε_mca` bound at that lift becomes an `MCALowerWitness`, a faithful threshold existence
  proof, and a threshold lower bracket;
* the GKL24 first-moment residual surfaces, including the retired atomic maximal-domain
  false-as-stated surface
  from `Issue67Scratch`, now feed those lower-witness consumers directly.

Mathematically, the consolidation is that every route

`list-size bound + first-moment residual + second-moment slack`

has the same endpoint:

`latticeIndexOf (johnsonLift δ η) ≤ mcaThreshold`.

The individual residuals still name the hard paper-specific content; this file only makes the
shared implication path explicit.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal ProbabilityTheory
open ListDecodable CodingTheory GrandChallenges GrandChallengesLattice

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Johnson-lift normal form -/

/-- The named `johnsonLift` is definitionally the ABF26/GCXK25 radius
`1 - √(1 - δ + η)`, truncated to `ℝ≥0`. -/
theorem johnsonLift_eq_t51_radius (δ η : ℝ) :
    johnsonLift δ η =
      (1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal := rfl

/-- Any checked `ε_mca` bound at the Johnson lift is a lower witness for the MCA threshold. -/
noncomputable def GrandChallenges.MCALowerWitness.ofJohnsonLiftEpsMCABound
    (C : Set (ι → F)) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_lt : δ < 1) (hη_pos : 0 < η)
    (hε :
      epsMCA (F := F) (A := F) C (johnsonLift δ η) ≤ (ε_star : ENNReal)) :
    MCALowerWitness C ε_star :=
  MCALowerWitness.ofLe (johnsonLift_le_one hδ_lt hη_pos) hε

/-- Johnson-lift `ε_mca` control is enough to make the faithful MCA lattice threshold exist. -/
theorem mcaThresholdExists_ofJohnsonLiftEpsMCABound
    (C : Set (ι → F)) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_lt : δ < 1) (hη_pos : 0 < η)
    (hε :
      epsMCA (F := F) (A := F) C (johnsonLift δ η) ≤ (ε_star : ENNReal)) :
    mcaThresholdExists C ε_star :=
  mcaThresholdExists_of_MCALowerWitness C ε_star
    (GrandChallenges.MCALowerWitness.ofJohnsonLiftEpsMCABound
      C δ η ε_star hδ_lt hη_pos hε)

/-- The faithful MCA threshold lies above the lattice point reached by the Johnson lift. -/
theorem le_mcaThreshold_ofJohnsonLiftEpsMCABound
    (C : Set (ι → F)) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_lt : δ < 1) (hη_pos : 0 < η)
    (hε :
      epsMCA (F := F) (A := F) C (johnsonLift δ η) ≤ (ε_star : ENNReal))
    (hne : mcaThresholdExists C ε_star) :
    latticeIndexOf (ι := ι) (johnsonLift δ η) (johnsonLift_le_one hδ_lt hη_pos) ≤
      mcaThreshold C ε_star hne :=
  MCALowerWitness_le_mcaThreshold C ε_star hne
    (GrandChallenges.MCALowerWitness.ofJohnsonLiftEpsMCABound
      C δ η ε_star hδ_lt hη_pos hε)

/-- The threshold produced from Johnson-lift `ε_mca` control satisfies the MCA predicate. -/
theorem mcaThreshold_spec_ofJohnsonLiftEpsMCABound
    (C : Set (ι → F)) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_lt : δ < 1) (hη_pos : 0 < η)
    (hε :
      epsMCA (F := F) (A := F) C (johnsonLift δ η) ≤ (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_ofJohnsonLiftEpsMCABound
      C δ η ε_star hδ_lt hη_pos hε
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) := by
  exact mcaThreshold_spec C ε_star
    (mcaThresholdExists_ofJohnsonLiftEpsMCABound
      C δ η ε_star hδ_lt hη_pos hε)

/-! ## `ε_mca` bridges at the named Johnson lift -/

/-- GKL24 first-moment residual, normalized to the named Johnson lift. -/
theorem linear_listSize_to_epsMCA_gcxk25_of_gkl24_firstMoment_residual_johnsonLift
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      GKL24FirstMomentResidual C (johnsonLift δ η)
        ((L : ℝ) ^ 2) (δ * (Fintype.card ι : ℝ))) :
    epsMCA (F := F) (A := F) ((C : Set (ι → F))) (johnsonLift δ η) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) := by
  simpa [johnsonLift] using
    (linear_listSize_to_epsMCA_gcxk25_of_gkl24_firstMoment_residual
      C L δ η hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ
      (by simpa [johnsonLift] using hres))

/-- GKL24 witness-cover residual, normalized to the named Johnson lift. -/
theorem linear_listSize_to_epsMCA_gcxk25_of_gkl24_witnessCover_residual_johnsonLift
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      GKL24FirstMomentWitnessCoverResidual C (johnsonLift δ η)
        ((L : ℝ) ^ 2) (δ * (Fintype.card ι : ℝ))) :
    epsMCA (F := F) (A := F) ((C : Set (ι → F))) (johnsonLift δ η) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) := by
  simpa [johnsonLift] using
    (linear_listSize_to_epsMCA_gcxk25_of_gkl24_witnessCover_residual
      C L δ η hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ
      (by simpa [johnsonLift] using hres))

/-- Maximal-correlated-domain hypothesis, normalized to the named Johnson lift. -/
theorem linear_listSize_to_epsMCA_gcxk25_of_gkl24_maxCorr_hypothesis_johnsonLift
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      GKL24MaxCorrWitnessCoverHypothesis C (johnsonLift δ η)
        δ.toNNReal ((L : ℝ) ^ 2)) :
    epsMCA (F := F) (A := F) ((C : Set (ι → F))) (johnsonLift δ η) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) := by
  simpa [johnsonLift] using
    (linear_listSize_to_epsMCA_gcxk25_of_gkl24_maxCorr_witnessCover_hypothesis
      C L δ η hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ
      (by simpa [johnsonLift] using hres))

/-- Strict-expansion false-as-stated surface, normalized to the named Johnson lift. -/
theorem linear_listSize_to_epsMCA_gcxk25_of_gkl24_strict_falseAsStated_johnsonLift
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hstrict_radius : 2 * ((johnsonLift δ η : ℝ≥0) : ℝ) ≤ (δ.toNNReal : ℝ))
    (hres :
      GKL24MaxCorrStrictWitnessCoverFalseAsStated C (johnsonLift δ η)
        δ.toNNReal ((L : ℝ) ^ 2)) :
    epsMCA (F := F) (A := F) ((C : Set (ι → F))) (johnsonLift δ η) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) := by
  simpa [johnsonLift] using
    (linear_listSize_to_epsMCA_gcxk25_of_gkl24_strict_witnessCover_falseAsStated
      C L δ η hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ
      (by simpa [johnsonLift] using hstrict_radius)
      (by simpa [johnsonLift] using hres))

/-- The atomic maximal-domain false-as-stated surface supplies the first-moment summand at the named
Johnson lift. -/
theorem linear_listSize_to_epsMCA_gcxk25_firstMoment_of_atomic_maxDomainWitnessCover
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hη_pos : 0 < η) (_hη_lt : η < 1) (_hη_le_δ : η ≤ δ)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      Issue67Scratch.GKL24MaxDomainWitnessCoverFalseAsStated C (johnsonLift δ η)
        ((L : ℝ) ^ 2) δ.toNNReal) :
    epsMCA (F := F) (A := F) ((C : Set (ι → F))) (johnsonLift δ η) ≤
      ENNReal.ofReal (((L : ℝ) ^ 2 * (δ * Fintype.card ι)) / Fintype.card F) := by
  have h := Issue67Scratch.epsMCA_le_ofReal_t51_firstMoment_of_maxDomainWitnessCover
    C (johnsonLift δ η) hres
  simpa [Real.toNNReal_of_nonneg (le_of_lt hδ_pos), mul_assoc] using h

/-- Atomic maximal-domain false-as-stated front door for the full ABF26/GCXK25 T5.1 bound. -/
theorem linear_listSize_to_epsMCA_gcxk25_of_atomic_maxDomainWitnessCover
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      Issue67Scratch.GKL24MaxDomainWitnessCoverFalseAsStated C (johnsonLift δ η)
        ((L : ℝ) ^ 2) δ.toNNReal) :
    epsMCA (F := F) (A := F) ((C : Set (ι → F))) (johnsonLift δ η) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) := by
  simpa [johnsonLift] using
    (linear_listSize_to_epsMCA_gcxk25_of_bad_count C L δ η
      hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ
      (fun u => by
        change
          ((mcaBad (F := F) ((C : Set (ι → F))) (johnsonLift δ η) (u 0) (u 1)).card : ℝ) ≤
            (L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η
        have hfirst :
            ((mcaBad (F := F) ((C : Set (ι → F))) (johnsonLift δ η) (u 0) (u 1)).card : ℝ) ≤
              (L : ℝ) ^ 2 * ((δ.toNNReal : ℝ) * (Fintype.card ι : ℝ)) :=
          Issue67Scratch.mcaBad_card_le_t51_firstMoment_of_maxDomainWitnessCover
            C (johnsonLift δ η) hres u
        calc
          ((mcaBad (F := F) ((C : Set (ι → F))) (johnsonLift δ η) (u 0) (u 1)).card : ℝ)
              ≤ (L : ℝ) ^ 2 * ((δ.toNNReal : ℝ) * (Fintype.card ι : ℝ)) := hfirst
          _ = (L : ℝ) ^ 2 * δ * Fintype.card ι := by
            rw [Real.toNNReal_of_nonneg (le_of_lt hδ_pos)]
            simp only [NNReal.coe_mk]
            ring_nf
          _ ≤ (L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η :=
            le_add_of_nonneg_right (by positivity)))

/-- Prop-level T5.1 wrapper from the atomic maximal-domain false-as-stated surface. -/
theorem linear_listSize_to_epsMCA_gcxk25_of_atomic_maxDomainWitnessCover_prop
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      Issue67Scratch.GKL24MaxDomainWitnessCoverFalseAsStated C (johnsonLift δ η)
        ((L : ℝ) ^ 2) δ.toNNReal) :
    linear_listSize_to_epsMCA_gcxk25 C L δ η
      hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ := by
  simpa [linear_listSize_to_epsMCA_gcxk25, johnsonLift] using
    (linear_listSize_to_epsMCA_gcxk25_of_atomic_maxDomainWitnessCover
      C L δ η hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres)

/-! ## Lower witnesses and faithful threshold brackets -/

/-- GKL24 first-moment residual data produce an MCA lower witness at the Johnson lift. -/
noncomputable def GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_gkl24_firstMoment_residual
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      GKL24FirstMomentResidual C (johnsonLift δ η)
        ((L : ℝ) ^ 2) (δ * (Fintype.card ι : ℝ)))
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal)) :
    MCALowerWitness ((C : Set (ι → F))) ε_star :=
  GrandChallenges.MCALowerWitness.ofJohnsonLiftEpsMCABound
    ((C : Set (ι → F))) δ η ε_star hδ_lt hη_pos
    (le_trans
      (linear_listSize_to_epsMCA_gcxk25_of_gkl24_firstMoment_residual_johnsonLift
        C L δ η hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres)
      hle)

/-- GKL24 first-moment residual data make the faithful MCA lattice threshold exist. -/
theorem mcaThresholdExists_ofListSizeGCXK25_of_gkl24_firstMoment_residual
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      GKL24FirstMomentResidual C (johnsonLift δ η)
        ((L : ℝ) ^ 2) (δ * (Fintype.card ι : ℝ)))
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal)) :
    mcaThresholdExists ((C : Set (ι → F))) ε_star :=
  mcaThresholdExists_of_MCALowerWitness _ _
    (GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_gkl24_firstMoment_residual
      C L δ η ε_star hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres hle)

/-- GKL24 first-moment residual data lower-bound the faithful MCA threshold. -/
theorem le_mcaThreshold_ofListSizeGCXK25_of_gkl24_firstMoment_residual
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      GKL24FirstMomentResidual C (johnsonLift δ η)
        ((L : ℝ) ^ 2) (δ * (Fintype.card ι : ℝ)))
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal))
    (hne : mcaThresholdExists ((C : Set (ι → F))) ε_star) :
    latticeIndexOf (ι := ι) (johnsonLift δ η) (johnsonLift_le_one hδ_lt hη_pos) ≤
      mcaThreshold ((C : Set (ι → F))) ε_star hne :=
  MCALowerWitness_le_mcaThreshold _ _ hne
    (GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_gkl24_firstMoment_residual
      C L δ η ε_star hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres hle)

/-- The threshold obtained from GKL24 first-moment residual data satisfies the MCA predicate. -/
theorem mcaThreshold_spec_ofListSizeGCXK25_of_gkl24_firstMoment_residual
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      GKL24FirstMomentResidual C (johnsonLift δ η)
        ((L : ℝ) ^ 2) (δ * (Fintype.card ι : ℝ)))
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_ofListSizeGCXK25_of_gkl24_firstMoment_residual
      C L δ η ε_star hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres hle
    mcaSatisfies ((C : Set (ι → F))) ε_star
      (mcaThreshold ((C : Set (ι → F))) ε_star hne) := by
  exact mcaThreshold_spec _ _
    (mcaThresholdExists_ofListSizeGCXK25_of_gkl24_firstMoment_residual
      C L δ η ε_star hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres hle)

/-- Witness-cover GKL24 residual data produce an MCA lower witness at the Johnson lift. -/
noncomputable def GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_gkl24_witnessCover_residual
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      GKL24FirstMomentWitnessCoverResidual C (johnsonLift δ η)
        ((L : ℝ) ^ 2) (δ * (Fintype.card ι : ℝ)))
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal)) :
    MCALowerWitness ((C : Set (ι → F))) ε_star :=
  GrandChallenges.MCALowerWitness.ofJohnsonLiftEpsMCABound
    ((C : Set (ι → F))) δ η ε_star hδ_lt hη_pos
    (le_trans
      (linear_listSize_to_epsMCA_gcxk25_of_gkl24_witnessCover_residual_johnsonLift
        C L δ η hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres)
      hle)

/-- Witness-cover GKL24 residual data make the faithful MCA lattice threshold exist. -/
theorem mcaThresholdExists_ofListSizeGCXK25_of_gkl24_witnessCover_residual
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      GKL24FirstMomentWitnessCoverResidual C (johnsonLift δ η)
        ((L : ℝ) ^ 2) (δ * (Fintype.card ι : ℝ)))
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal)) :
    mcaThresholdExists ((C : Set (ι → F))) ε_star :=
  mcaThresholdExists_of_MCALowerWitness _ _
    (GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_gkl24_witnessCover_residual
      C L δ η ε_star hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres hle)

/-- Witness-cover GKL24 residual data lower-bound the faithful MCA threshold. -/
theorem le_mcaThreshold_ofListSizeGCXK25_of_gkl24_witnessCover_residual
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      GKL24FirstMomentWitnessCoverResidual C (johnsonLift δ η)
        ((L : ℝ) ^ 2) (δ * (Fintype.card ι : ℝ)))
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal))
    (hne : mcaThresholdExists ((C : Set (ι → F))) ε_star) :
    latticeIndexOf (ι := ι) (johnsonLift δ η) (johnsonLift_le_one hδ_lt hη_pos) ≤
      mcaThreshold ((C : Set (ι → F))) ε_star hne :=
  MCALowerWitness_le_mcaThreshold _ _ hne
    (GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_gkl24_witnessCover_residual
      C L δ η ε_star hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres hle)

/-- Max-correlation GKL24 hypothesis data produce an MCA lower witness at the Johnson lift. -/
noncomputable def GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_gkl24_maxCorr_hypothesis
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      GKL24MaxCorrWitnessCoverHypothesis C (johnsonLift δ η)
        δ.toNNReal ((L : ℝ) ^ 2))
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal)) :
    MCALowerWitness ((C : Set (ι → F))) ε_star :=
  GrandChallenges.MCALowerWitness.ofJohnsonLiftEpsMCABound
    ((C : Set (ι → F))) δ η ε_star hδ_lt hη_pos
    (le_trans
      (linear_listSize_to_epsMCA_gcxk25_of_gkl24_maxCorr_hypothesis_johnsonLift
        C L δ η hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres)
      hle)

/-- Max-correlation GKL24 hypothesis data make the faithful MCA lattice threshold exist. -/
theorem mcaThresholdExists_ofListSizeGCXK25_of_gkl24_maxCorr_hypothesis
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      GKL24MaxCorrWitnessCoverHypothesis C (johnsonLift δ η)
        δ.toNNReal ((L : ℝ) ^ 2))
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal)) :
    mcaThresholdExists ((C : Set (ι → F))) ε_star :=
  mcaThresholdExists_of_MCALowerWitness _ _
    (GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_gkl24_maxCorr_hypothesis
      C L δ η ε_star hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres hle)

/-- Max-correlation GKL24 hypothesis data lower-bound the faithful MCA threshold. -/
theorem le_mcaThreshold_ofListSizeGCXK25_of_gkl24_maxCorr_hypothesis
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      GKL24MaxCorrWitnessCoverHypothesis C (johnsonLift δ η)
        δ.toNNReal ((L : ℝ) ^ 2))
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal))
    (hne : mcaThresholdExists ((C : Set (ι → F))) ε_star) :
    latticeIndexOf (ι := ι) (johnsonLift δ η) (johnsonLift_le_one hδ_lt hη_pos) ≤
      mcaThreshold ((C : Set (ι → F))) ε_star hne :=
  MCALowerWitness_le_mcaThreshold _ _ hne
    (GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_gkl24_maxCorr_hypothesis
      C L δ η ε_star hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres hle)

/-- Strict-cover GKL24 false-as-stated data produce an MCA lower witness at the Johnson lift. -/
noncomputable def GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_gkl24_strict_falseAsStated
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hstrict_radius : 2 * ((johnsonLift δ η : ℝ≥0) : ℝ) ≤ (δ.toNNReal : ℝ))
    (hres :
      GKL24MaxCorrStrictWitnessCoverFalseAsStated C (johnsonLift δ η)
        δ.toNNReal ((L : ℝ) ^ 2))
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal)) :
    MCALowerWitness ((C : Set (ι → F))) ε_star :=
  GrandChallenges.MCALowerWitness.ofJohnsonLiftEpsMCABound
    ((C : Set (ι → F))) δ η ε_star hδ_lt hη_pos
    (le_trans
      (linear_listSize_to_epsMCA_gcxk25_of_gkl24_strict_falseAsStated_johnsonLift
        C L δ η hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hstrict_radius hres)
      hle)

/-- Strict-cover GKL24 false-as-stated data make the faithful MCA lattice threshold exist. -/
theorem mcaThresholdExists_ofListSizeGCXK25_of_gkl24_strict_falseAsStated
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hstrict_radius : 2 * ((johnsonLift δ η : ℝ≥0) : ℝ) ≤ (δ.toNNReal : ℝ))
    (hres :
      GKL24MaxCorrStrictWitnessCoverFalseAsStated C (johnsonLift δ η)
        δ.toNNReal ((L : ℝ) ^ 2))
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal)) :
    mcaThresholdExists ((C : Set (ι → F))) ε_star :=
  mcaThresholdExists_of_MCALowerWitness _ _
    (GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_gkl24_strict_falseAsStated
      C L δ η ε_star hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ
      hstrict_radius hres hle)

/-- Strict-cover GKL24 false-as-stated data lower-bound the faithful MCA threshold. -/
theorem le_mcaThreshold_ofListSizeGCXK25_of_gkl24_strict_falseAsStated
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hstrict_radius : 2 * ((johnsonLift δ η : ℝ≥0) : ℝ) ≤ (δ.toNNReal : ℝ))
    (hres :
      GKL24MaxCorrStrictWitnessCoverFalseAsStated C (johnsonLift δ η)
        δ.toNNReal ((L : ℝ) ^ 2))
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal))
    (hne : mcaThresholdExists ((C : Set (ι → F))) ε_star) :
    latticeIndexOf (ι := ι) (johnsonLift δ η) (johnsonLift_le_one hδ_lt hη_pos) ≤
      mcaThreshold ((C : Set (ι → F))) ε_star hne :=
  MCALowerWitness_le_mcaThreshold _ _ hne
    (GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_gkl24_strict_falseAsStated
      C L δ η ε_star hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ
      hstrict_radius hres hle)

/-- Atomic maximal-domain false-as-stated data produce an MCA lower witness at the Johnson lift. -/
noncomputable def GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_atomic_maxDomainWitnessCover
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      Issue67Scratch.GKL24MaxDomainWitnessCoverFalseAsStated C (johnsonLift δ η)
        ((L : ℝ) ^ 2) δ.toNNReal)
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal)) :
    MCALowerWitness ((C : Set (ι → F))) ε_star :=
  GrandChallenges.MCALowerWitness.ofJohnsonLiftEpsMCABound
    ((C : Set (ι → F))) δ η ε_star hδ_lt hη_pos
    (le_trans
      (linear_listSize_to_epsMCA_gcxk25_of_atomic_maxDomainWitnessCover
        C L δ η hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres)
      hle)

/-- Atomic maximal-domain false-as-stated data make the faithful MCA lattice threshold exist. -/
theorem mcaThresholdExists_ofListSizeGCXK25_of_atomic_maxDomainWitnessCover
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      Issue67Scratch.GKL24MaxDomainWitnessCoverFalseAsStated C (johnsonLift δ η)
        ((L : ℝ) ^ 2) δ.toNNReal)
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal)) :
    mcaThresholdExists ((C : Set (ι → F))) ε_star :=
  mcaThresholdExists_of_MCALowerWitness _ _
    (GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_atomic_maxDomainWitnessCover
      C L δ η ε_star hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres hle)

/-- Atomic maximal-domain false-as-stated data lower-bound the faithful MCA threshold. -/
theorem le_mcaThreshold_ofListSizeGCXK25_of_atomic_maxDomainWitnessCover
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      Issue67Scratch.GKL24MaxDomainWitnessCoverFalseAsStated C (johnsonLift δ η)
        ((L : ℝ) ^ 2) δ.toNNReal)
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal))
    (hne : mcaThresholdExists ((C : Set (ι → F))) ε_star) :
    latticeIndexOf (ι := ι) (johnsonLift δ η) (johnsonLift_le_one hδ_lt hη_pos) ≤
      mcaThreshold ((C : Set (ι → F))) ε_star hne :=
  MCALowerWitness_le_mcaThreshold _ _ hne
    (GrandChallenges.MCALowerWitness.ofListSizeGCXK25_of_atomic_maxDomainWitnessCover
      C L δ η ε_star hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres hle)

/-- The threshold obtained from atomic maximal-domain false-as-stated data satisfies the MCA
predicate. -/
theorem mcaThreshold_spec_ofListSizeGCXK25_of_atomic_maxDomainWitnessCover
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hres :
      Issue67Scratch.GKL24MaxDomainWitnessCoverFalseAsStated C (johnsonLift δ η)
        ((L : ℝ) ^ 2) δ.toNNReal)
    (hle :
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
          (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_ofListSizeGCXK25_of_atomic_maxDomainWitnessCover
      C L δ η ε_star hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres hle
    mcaSatisfies ((C : Set (ι → F))) ε_star
      (mcaThreshold ((C : Set (ι → F))) ε_star hne) := by
  exact mcaThreshold_spec _ _
    (mcaThresholdExists_ofListSizeGCXK25_of_atomic_maxDomainWitnessCover
      C L δ η ε_star hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hres hle)

end ProximityGap
