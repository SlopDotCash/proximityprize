/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingSpec

/-!
# Resolved selected-threshold prize specifications for repaired line-decoding data

This module packages the selected-threshold bracket wrappers from
`LineDecodingGrandChallengesPrizeSpec` with the faithful MCA lattice-resolution predicate.
-/

namespace ProximityGap

open scoped NNReal

namespace GrandChallengesLattice

open GrandChallenges

section LineDecodingResolvedPrizeSpec

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_spec_and_lower
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (h : ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          ∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  rcases h with ⟨τ, hspec, hlower⟩
  exact ⟨τ, (mcaPrizeLatticeResolved_iff domain τ).mpr hspec, hspec, hlower⟩

private theorem exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_spec_and_brackets
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (h : ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j)) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          (∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
            ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases h with ⟨τ, hspec, hlower, hupper⟩
  exact ⟨τ, (mcaPrizeLatticeResolved_iff domain τ).mpr hspec, hspec, hlower, hupper⟩

private theorem
    mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_of_threshold_data
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hdata : ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
            mcaThreshold C epsStar hne) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) ∧
                latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  let C : Fin 4 → Set (ι → F) := fun j =>
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  have hdata' : ∀ j : Fin 4,
      ∃ hne : mcaThresholdExists (C j) epsStar,
        mcaSatisfies (C j) epsStar (mcaThreshold (C j) epsStar hne) ∧
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
            mcaThreshold (C j) epsStar hne := by
    intro j
    simpa [C] using hdata j
  choose hne hspec using hdata'
  let τ : Fin 4 → Fin (Fintype.card ι + 1) := fun j =>
    mcaThreshold (C j) epsStar (hne j)
  refine ⟨τ, ?_, ?_⟩
  · refine (mcaPrizeLatticeResolved_iff domain τ).mpr ?_
    intro j
    refine ⟨hne j, ?_, ?_⟩
    · simpa [τ, C] using (hspec j).1
    · intro i hi
      simpa [τ, C] using le_mcaThreshold (C j) epsStar (hne j) hi
  · intro j
    refine ⟨hne j, ?_, ?_, ?_⟩
    · simp [τ, C]
    · simpa [τ] using (hspec j).1
    · simpa [τ] using (hspec j).2

private theorem
    mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_of_threshold_data
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hdata : ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
              mcaThreshold C epsStar hne ∧
            mcaThreshold C epsStar hne <
              latticeIndexOf (ι := ι) (whi j).δ (hδhi j)) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) ∧
                latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                  τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  let C : Fin 4 → Set (ι → F) := fun j =>
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  have hdata' : ∀ j : Fin 4,
      ∃ hne : mcaThresholdExists (C j) epsStar,
        mcaSatisfies (C j) epsStar (mcaThreshold (C j) epsStar hne) ∧
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
              mcaThreshold (C j) epsStar hne ∧
            mcaThreshold (C j) epsStar hne <
              latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
    intro j
    simpa [C] using hdata j
  choose hne hspec using hdata'
  let τ : Fin 4 → Fin (Fintype.card ι + 1) := fun j =>
    mcaThreshold (C j) epsStar (hne j)
  refine ⟨τ, ?_, ?_⟩
  · refine (mcaPrizeLatticeResolved_iff domain τ).mpr ?_
    intro j
    refine ⟨hne j, ?_, ?_⟩
    · simpa [τ, C] using (hspec j).1
    · intro i hi
      simpa [τ, C] using le_mcaThreshold (C j) epsStar (hne j) hi
  · intro j
    refine ⟨hne j, ?_, ?_, ?_, ?_⟩
    · simp [τ, C]
    · simpa [τ] using (hspec j).1
    · simpa [τ] using (hspec j).2.1
    · simpa [τ] using (hspec j).2.2

/-- Repaired double-cover data supplies a selected-threshold lattice resolution, the exact
threshold specification, and lower lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          ∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_spec_and_lower
    domain δ hδ_le_one <|
      exists_mcaPrizeLatticeSpec_and_lower_brackets_ofDoubleCover
        domain δ hδ_le_one hcov

/-- Named bad-scalar double-cover obligations supply a selected-threshold lattice resolution, the
exact threshold specification, and lower lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          ∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_spec_and_lower
    domain δ hδ_le_one <|
      exists_mcaPrizeLatticeSpec_and_lower_brackets_ofBadScalarDoubleCover
        domain δ hδ_le_one hcov

/-- Zero bad-scalar counts supply a selected-threshold lattice resolution, the exact threshold
specification, and lower lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          ∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_spec_and_lower
    domain δ hδ_le_one <|
      exists_mcaPrizeLatticeSpec_and_lower_brackets_of_mcaBadCount_zero
        domain δ hδ_le_one hzero

/-- Direct no-bad-event frontiers supply a selected-threshold lattice resolution, the exact
threshold specification, and lower lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          ∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_spec_and_lower
    domain δ hδ_le_one <|
      exists_mcaPrizeLatticeSpec_and_lower_brackets_of_forall_not_mcaEvent
        domain δ hδ_le_one hno

/-- Direct vanishing `ε_mca` frontiers supply a selected-threshold lattice resolution, the exact
threshold specification, and lower lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_epsMCA_eq_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          ∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_spec_and_lower
    domain δ hδ_le_one <|
      exists_mcaPrizeLatticeSpec_and_lower_brackets_of_epsMCA_eq_zero
        domain δ hδ_le_one heps

/-- Named bad-scalar double-cover obligations supply a selected-threshold lattice resolution, the
exact threshold specification, and two-sided lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_brackets_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          (∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
            ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_spec_and_brackets
    domain δ hδ_le_one whi hδhi <|
      exists_mcaPrizeLatticeSpec_and_brackets_ofBadScalarDoubleCover
        domain δ hδ_le_one hcov whi hδhi

/-- Zero bad-scalar counts supply a selected-threshold lattice resolution, the exact threshold
specification, and two-sided lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          (∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
            ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_spec_and_brackets
    domain δ hδ_le_one whi hδhi <|
      exists_mcaPrizeLatticeSpec_and_brackets_of_mcaBadCount_zero
        domain δ hδ_le_one hzero whi hδhi

/-- Direct no-bad-event frontiers supply a selected-threshold lattice resolution, the exact
threshold specification, and two-sided lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          (∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
            ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_spec_and_brackets
    domain δ hδ_le_one whi hδhi <|
      exists_mcaPrizeLatticeSpec_and_brackets_of_forall_not_mcaEvent
        domain δ hδ_le_one hno whi hδhi

/-- Project a selected-threshold resolved package with exact threshold specifications and lower
lattice brackets to the lower-bracket-only package. -/
theorem exists_mcaPrizeLatticeResolved_with_lower_brackets_of_spec_and_lower_brackets
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (h : ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          ∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  rcases h with ⟨τ, hτ, _hspec, hlower⟩
  exact ⟨τ, hτ, hlower⟩

/-- Project a selected-threshold resolved package with exact threshold specifications and two-sided
lattice brackets to the bracket-only package. -/
theorem exists_mcaPrizeLatticeResolved_with_brackets_of_spec_and_brackets
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (h : ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          (∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
            ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j)) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases h with ⟨τ, hτ, _hspec, hlower, hupper⟩
  exact ⟨τ, hτ, hlower, hupper⟩

set_option linter.style.longLine false in
/-- Repaired double-cover data supplies a selected-threshold lattice resolution and lower lattice
brackets, dropping the threshold-specification payload. -/
theorem exists_mcaPrizeLatticeResolved_with_lower_brackets_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  exact exists_mcaPrizeLatticeResolved_with_lower_brackets_of_spec_and_lower_brackets
    domain δ hδ_le_one <|
      exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_ofDoubleCover
        domain δ hδ_le_one hcov

set_option linter.style.longLine false in
/-- Named bad-scalar double-cover obligations supply a selected-threshold lattice resolution and
lower lattice brackets, dropping the threshold-specification payload. -/
theorem exists_mcaPrizeLatticeResolved_with_lower_brackets_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  exact exists_mcaPrizeLatticeResolved_with_lower_brackets_of_spec_and_lower_brackets
    domain δ hδ_le_one <|
      exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_ofBadScalarDoubleCover
        domain δ hδ_le_one hcov

set_option linter.style.longLine false in
/-- Zero bad-scalar counts supply a selected-threshold lattice resolution and lower lattice
brackets, dropping the threshold-specification payload. -/
theorem exists_mcaPrizeLatticeResolved_with_lower_brackets_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  exact exists_mcaPrizeLatticeResolved_with_lower_brackets_of_spec_and_lower_brackets
    domain δ hδ_le_one <|
      exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_mcaBadCount_zero
        domain δ hδ_le_one hzero

set_option linter.style.longLine false in
/-- Direct no-bad-event frontiers supply a selected-threshold lattice resolution and lower
lattice brackets, dropping the threshold-specification payload. -/
theorem exists_mcaPrizeLatticeResolved_with_lower_brackets_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  exact exists_mcaPrizeLatticeResolved_with_lower_brackets_of_spec_and_lower_brackets
    domain δ hδ_le_one <|
      exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_forall_not_mcaEvent
        domain δ hδ_le_one hno

set_option linter.style.longLine false in
/-- Direct vanishing `ε_mca` frontiers supply a selected-threshold lattice resolution and lower
lattice brackets, dropping the threshold-specification payload. -/
theorem exists_mcaPrizeLatticeResolved_with_lower_brackets_of_epsMCA_eq_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  exact exists_mcaPrizeLatticeResolved_with_lower_brackets_of_spec_and_lower_brackets
    domain δ hδ_le_one <|
      exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_epsMCA_eq_zero
        domain δ hδ_le_one heps

set_option linter.style.longLine false in
/-- Repaired double-cover data and explicit upper witnesses supply a selected-threshold lattice
resolution and two-sided lattice brackets, dropping the threshold-specification payload. -/
theorem exists_mcaPrizeLatticeResolved_with_brackets_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j))
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  exact exists_mcaPrizeLatticeResolved_with_brackets_of_spec_and_brackets
    domain δ hδ_le_one whi hδhi <|
      exists_mcaPrizeLatticeResolved_with_spec_and_brackets_ofDoubleCover
        domain δ hδ_le_one hcov whi hδhi

set_option linter.style.longLine false in
/-- Named bad-scalar double-cover data and explicit upper witnesses supply a selected-threshold
lattice resolution and two-sided lattice brackets, dropping the threshold-specification payload. -/
theorem exists_mcaPrizeLatticeResolved_with_brackets_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  exact exists_mcaPrizeLatticeResolved_with_brackets_of_spec_and_brackets
    domain δ hδ_le_one whi hδhi <|
      exists_mcaPrizeLatticeResolved_with_spec_and_brackets_ofBadScalarDoubleCover
        domain δ hδ_le_one hcov whi hδhi

set_option linter.style.longLine false in
/-- Zero bad-scalar counts and explicit upper witnesses supply a selected-threshold lattice
resolution and two-sided lattice brackets, dropping the threshold-specification payload. -/
theorem exists_mcaPrizeLatticeResolved_with_brackets_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  exact exists_mcaPrizeLatticeResolved_with_brackets_of_spec_and_brackets
    domain δ hδ_le_one whi hδhi <|
      exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_mcaBadCount_zero
        domain δ hδ_le_one hzero whi hδhi

set_option linter.style.longLine false in
/-- Direct no-bad-event frontiers and explicit upper witnesses supply a selected-threshold
lattice resolution and two-sided lattice brackets, dropping the threshold-specification payload. -/
theorem exists_mcaPrizeLatticeResolved_with_brackets_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  exact exists_mcaPrizeLatticeResolved_with_brackets_of_spec_and_brackets
    domain δ hδ_le_one whi hδhi <|
      exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_forall_not_mcaEvent
        domain δ hδ_le_one hno whi hδhi

set_option linter.style.longLine false in
/-- Direct vanishing `ε_mca` frontiers and explicit upper witnesses supply a selected-threshold
lattice resolution and two-sided lattice brackets, dropping the threshold-specification payload. -/
theorem exists_mcaPrizeLatticeResolved_with_brackets_of_epsMCA_eq_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  exact exists_mcaPrizeLatticeResolved_with_brackets_of_spec_and_brackets
    domain δ hδ_le_one whi hδhi <|
      exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_epsMCA_eq_zero
        domain δ hδ_le_one heps whi hδhi

set_option linter.style.longLine false in
/-- Repaired double-cover data resolves the faithful prize lattice at the concrete
`mcaThreshold` indices and preserves threshold facts plus lower lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) ∧
                latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_of_threshold_data
    domain δ hδ_le_one <|
      mcaThreshold_spec_and_lower_bracket_prize_allRates_ofDoubleCover
        domain δ hδ_le_one hcov

set_option linter.style.longLine false in
/-- Named bad-scalar double-cover data resolves the faithful prize lattice at the concrete
`mcaThreshold` indices and preserves threshold facts plus lower lattice brackets. -/
theorem
    mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) ∧
                latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_of_threshold_data
    domain δ hδ_le_one <|
      mcaThreshold_spec_and_lower_bracket_prize_allRates_ofBadScalarDoubleCover
        domain δ hδ_le_one hcov

set_option linter.style.longLine false in
/-- Zero bad-scalar counts resolve the faithful prize lattice at the concrete `mcaThreshold`
indices and preserve threshold facts plus lower lattice brackets. -/
theorem
    mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) ∧
                latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_of_threshold_data
    domain δ hδ_le_one <|
      mcaThreshold_spec_and_lower_bracket_prize_allRates_of_mcaBadCount_zero
        domain δ hδ_le_one hzero

set_option linter.style.longLine false in
/-- Direct no-bad-event frontiers resolve the faithful prize lattice at the concrete
`mcaThreshold` indices and preserve threshold facts plus lower lattice brackets. -/
theorem
    mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) ∧
                latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_of_threshold_data
    domain δ hδ_le_one <|
      mcaThreshold_spec_and_lower_bracket_prize_allRates_of_forall_not_mcaEvent
        domain δ hδ_le_one hno

set_option linter.style.longLine false in
/-- Direct vanishing `ε_mca` frontiers resolve the faithful prize lattice at the concrete
`mcaThreshold` indices and preserve threshold facts plus lower lattice brackets. -/
theorem
    mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_of_epsMCA_eq_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) ∧
                latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_ofDoubleCover
    domain δ hδ_le_one
    (indexed_MCAForallDoubleCover_of_epsMCA_eq_zero
      (fun j : Fin 4 =>
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
      δ heps)

set_option linter.style.longLine false in
/-- Repaired double-cover data resolves the faithful prize lattice at the concrete
`mcaThreshold` indices and preserves only the threshold equality and satisfy facts. -/
theorem mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) := by
  rcases mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_ofDoubleCover
      domain δ hδ_le_one hcov with ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, hsat, _hlower⟩
  exact ⟨hne, heq, hsat⟩

set_option linter.style.longLine false in
/-- Named bad-scalar double-cover data resolves the faithful prize lattice at concrete
`mcaThreshold` indices and preserves only the threshold equality and satisfy facts. -/
theorem mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) := by
  rcases
      mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_ofBadScalarDoubleCover
        domain δ hδ_le_one hcov with
    ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, hsat, _hlower⟩
  exact ⟨hne, heq, hsat⟩

set_option linter.style.longLine false in
/-- Zero bad-scalar counts resolve the faithful prize lattice at concrete `mcaThreshold` indices
and preserve only the threshold equality and satisfy facts. -/
theorem mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) := by
  rcases
      mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_of_mcaBadCount_zero
        domain δ hδ_le_one hzero with
    ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, hsat, _hlower⟩
  exact ⟨hne, heq, hsat⟩

set_option linter.style.longLine false in
/-- Direct no-bad-event frontiers resolve the faithful prize lattice at concrete `mcaThreshold`
indices and preserve only the threshold equality and satisfy facts. -/
theorem mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) := by
  rcases
      mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_of_forall_not_mcaEvent
        domain δ hδ_le_one hno with
    ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, hsat, _hlower⟩
  exact ⟨hne, heq, hsat⟩

set_option linter.style.longLine false in
/-- Direct vanishing `ε_mca` frontiers resolve the faithful prize lattice at concrete
`mcaThreshold` indices and preserve only the threshold equality and satisfy facts. -/
theorem mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_of_epsMCA_eq_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) := by
  rcases
      mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_of_epsMCA_eq_zero
        domain δ hδ_le_one heps with
    ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, hsat, _hlower⟩
  exact ⟨hne, heq, hsat⟩

set_option linter.style.longLine false in
/-- Repaired double-cover data resolves the faithful prize lattice at the concrete
`mcaThreshold` indices and preserves only the threshold equality witnesses. -/
theorem mcaPrizeLatticeResolved_with_threshold_prize_allRates_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne := by
  rcases mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_ofDoubleCover
      domain δ hδ_le_one hcov with ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat⟩
  exact ⟨hne, heq⟩

set_option linter.style.longLine false in
/-- Named bad-scalar double-cover data resolves the faithful prize lattice at concrete
`mcaThreshold` indices and preserves only the threshold equality witnesses. -/
theorem mcaPrizeLatticeResolved_with_threshold_prize_allRates_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne := by
  rcases mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_ofBadScalarDoubleCover
      domain δ hδ_le_one hcov with ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat⟩
  exact ⟨hne, heq⟩

set_option linter.style.longLine false in
/-- Zero bad-scalar counts resolve the faithful prize lattice at concrete `mcaThreshold` indices
and preserve only the threshold equality witnesses. -/
theorem mcaPrizeLatticeResolved_with_threshold_prize_allRates_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne := by
  rcases mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_of_mcaBadCount_zero
      domain δ hδ_le_one hzero with ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat⟩
  exact ⟨hne, heq⟩

set_option linter.style.longLine false in
/-- Direct no-bad-event frontiers resolve the faithful prize lattice at concrete `mcaThreshold`
indices and preserve only the threshold equality witnesses. -/
theorem mcaPrizeLatticeResolved_with_threshold_prize_allRates_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne := by
  rcases mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_of_forall_not_mcaEvent
      domain δ hδ_le_one hno with ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat⟩
  exact ⟨hne, heq⟩

set_option linter.style.longLine false in
/-- Direct vanishing `ε_mca` frontiers resolve the faithful prize lattice at concrete
`mcaThreshold` indices and preserve only the threshold equality witnesses. -/
theorem mcaPrizeLatticeResolved_with_threshold_prize_allRates_of_epsMCA_eq_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne := by
  rcases mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_of_epsMCA_eq_zero
      domain δ hδ_le_one heps with ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat⟩
  exact ⟨hne, heq⟩

set_option linter.style.longLine false in
/-- Repaired double-cover data resolves the faithful prize lattice at concrete `mcaThreshold`
indices and preserves threshold equalities plus lower lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_lower_brackets_prize_allRates_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  rcases mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_ofDoubleCover
      domain δ hδ_le_one hcov with ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat, hlower⟩
  exact ⟨hne, heq, hlower⟩

set_option linter.style.longLine false in
/-- Named bad-scalar double-cover data resolves the faithful prize lattice at concrete
`mcaThreshold` indices and preserves threshold equalities plus lower lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_lower_brackets_prize_allRates_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  rcases
      mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_ofBadScalarDoubleCover
        domain δ hδ_le_one hcov with
    ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat, hlower⟩
  exact ⟨hne, heq, hlower⟩

set_option linter.style.longLine false in
/-- Zero bad-scalar counts resolve the faithful prize lattice at concrete `mcaThreshold` indices
and preserve threshold equalities plus lower lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_lower_brackets_prize_allRates_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  rcases
      mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_of_mcaBadCount_zero
        domain δ hδ_le_one hzero with
    ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat, hlower⟩
  exact ⟨hne, heq, hlower⟩

set_option linter.style.longLine false in
/-- Direct no-bad-event frontiers resolve the faithful prize lattice at concrete `mcaThreshold`
indices and preserve threshold equalities plus lower lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_lower_brackets_prize_allRates_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  rcases
      mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_of_forall_not_mcaEvent
        domain δ hδ_le_one hno with
    ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat, hlower⟩
  exact ⟨hne, heq, hlower⟩

set_option linter.style.longLine false in
/-- Direct vanishing `ε_mca` frontiers resolve the faithful prize lattice at concrete
`mcaThreshold` indices and preserve threshold equalities plus lower lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_lower_brackets_prize_allRates_of_epsMCA_eq_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  rcases
      mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_of_epsMCA_eq_zero
        domain δ hδ_le_one heps with
    ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat, hlower⟩
  exact ⟨hne, heq, hlower⟩

set_option linter.style.longLine false in
/-- Repaired double-cover data and explicit upper witnesses resolve the faithful prize lattice at
the concrete `mcaThreshold` indices and preserve threshold facts plus both lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j))
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) ∧
                latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                  τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_of_threshold_data
    domain δ hδ_le_one whi hδhi <|
      mcaThreshold_spec_and_bracket_prize_allRates_ofDoubleCover
        domain δ hδ_le_one hcov whi hδhi

set_option linter.style.longLine false in
/-- Named bad-scalar double-cover data and explicit upper witnesses resolve the faithful prize
lattice at concrete `mcaThreshold` indices and preserve threshold facts plus both brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) ∧
                latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                  τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_of_threshold_data
    domain δ hδ_le_one whi hδhi <|
      mcaThreshold_spec_and_bracket_prize_allRates_ofBadScalarDoubleCover
        domain δ hδ_le_one hcov whi hδhi

set_option linter.style.longLine false in
/-- Zero bad-scalar counts and explicit upper witnesses resolve the faithful prize lattice at
concrete `mcaThreshold` indices and preserve threshold facts plus both lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) ∧
                latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                  τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_of_threshold_data
    domain δ hδ_le_one whi hδhi <|
      mcaThreshold_spec_and_bracket_prize_allRates_of_mcaBadCount_zero
        domain δ hδ_le_one hzero whi hδhi

set_option linter.style.longLine false in
/-- Direct no-bad-event frontiers and explicit upper witnesses resolve the faithful prize lattice
at concrete `mcaThreshold` indices and preserve threshold facts plus both lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) ∧
                latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                  τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_of_threshold_data
    domain δ hδ_le_one whi hδhi <|
      mcaThreshold_spec_and_bracket_prize_allRates_of_forall_not_mcaEvent
        domain δ hδ_le_one hno whi hδhi

set_option linter.style.longLine false in
/-- Direct vanishing `ε_mca` frontiers and explicit upper witnesses resolve the faithful prize
lattice at concrete `mcaThreshold` indices and preserve threshold facts plus both brackets. -/
theorem
    mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_of_epsMCA_eq_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              mcaSatisfies (C j) epsStar (τ j) ∧
                latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                  τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_ofDoubleCover
    domain δ hδ_le_one
    (indexed_MCAForallDoubleCover_of_epsMCA_eq_zero
      (fun j : Fin 4 =>
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
      δ heps)
    whi hδhi

set_option linter.style.longLine false in
/-- Repaired double-cover data and explicit upper witnesses resolve the faithful prize lattice at
concrete `mcaThreshold` indices and preserve equality plus both lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_brackets_prize_allRates_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j))
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_ofDoubleCover
      domain δ hδ_le_one hcov whi hδhi with ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat, hlower, hupper⟩
  exact ⟨hne, heq, hlower, hupper⟩

set_option linter.style.longLine false in
/-- Named bad-scalar double-cover data and explicit upper witnesses resolve the faithful prize
lattice at concrete `mcaThreshold` indices and preserve equality plus both lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_brackets_prize_allRates_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases
      mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_ofBadScalarDoubleCover
        domain δ hδ_le_one hcov whi hδhi with
    ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat, hlower, hupper⟩
  exact ⟨hne, heq, hlower, hupper⟩

set_option linter.style.longLine false in
/-- Zero bad-scalar counts and explicit upper witnesses resolve the faithful prize lattice at
concrete `mcaThreshold` indices and preserve equality plus both lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_brackets_prize_allRates_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases
      mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_of_mcaBadCount_zero
        domain δ hδ_le_one hzero whi hδhi with
    ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat, hlower, hupper⟩
  exact ⟨hne, heq, hlower, hupper⟩

set_option linter.style.longLine false in
/-- Direct no-bad-event frontiers and explicit upper witnesses resolve the faithful prize lattice
at concrete `mcaThreshold` indices and preserve equality plus both lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_brackets_prize_allRates_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases
      mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_of_forall_not_mcaEvent
        domain δ hδ_le_one hno whi hδhi with
    ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat, hlower, hupper⟩
  exact ⟨hne, heq, hlower, hupper⟩

set_option linter.style.longLine false in
/-- Direct vanishing `ε_mca` frontiers and explicit upper witnesses resolve the faithful prize
lattice at concrete `mcaThreshold` indices and preserve equality plus both lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_brackets_prize_allRates_of_epsMCA_eq_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    let C : Fin 4 → Set (ι → F) := fun j =>
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          ∃ hne : mcaThresholdExists (C j) epsStar,
            τ j = mcaThreshold (C j) epsStar hne ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_of_epsMCA_eq_zero
      domain δ hδ_le_one heps whi hδhi with ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, heq, _hsat, hlower, hupper⟩
  exact ⟨hne, heq, hlower, hupper⟩

end LineDecodingResolvedPrizeSpec

set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_brackets_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_lower_brackets_of_spec_and_lower_brackets
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_brackets_of_spec_and_brackets
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_lower_brackets_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_lower_brackets_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_lower_brackets_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_lower_brackets_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_lower_brackets_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_brackets_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_brackets_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_brackets_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_brackets_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_brackets_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_prize_allRates_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_prize_allRates_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_prize_allRates_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_prize_allRates_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_prize_allRates_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_lower_brackets_prize_allRates_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_lower_brackets_prize_allRates_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_lower_brackets_prize_allRates_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_lower_brackets_prize_allRates_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_lower_brackets_prize_allRates_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_brackets_prize_allRates_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_brackets_prize_allRates_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_brackets_prize_allRates_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_brackets_prize_allRates_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_threshold_brackets_prize_allRates_of_epsMCA_eq_zero

end GrandChallengesLattice

end ProximityGap
