/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LatticeSpec
import ArkLib.Data.CodingTheory.ProximityGap.LineDecoding3

/-!
# Prize-lattice specifications for repaired line-decoding data

This module packages the repaired line-decoding double-cover route with the faithful
satisfy/maximality specification for the four selected MCA prize lattice thresholds.
-/

set_option linter.style.longFile 2100

namespace ProximityGap

open scoped NNReal

set_option linter.unusedDecidableInType false

namespace GrandChallengesLattice

open GrandChallenges

section LineDecodingPrizeSpec

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Per-rate repaired double-cover data resolves the faithful MCA prize and exposes the
satisfy/maximality specification for the selected lattice thresholds.  This is the prize-spec
version of `exists_mcaPrizeLatticeResolved_ofDoubleCover`. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses domain fun j =>
    MCALowerWitness.ofDoubleCover
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hcov j)

/-- Per-rate named bad-scalar double-cover obligations resolve the faithful MCA prize and expose
the satisfy/maximality specification for the selected lattice thresholds. This is the prize-spec
version of `exists_mcaPrizeLatticeResolved_ofBadScalarDoubleCover`. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses domain fun j =>
    MCALowerWitness.ofBadScalarDoubleCover
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hcov j)

/-- Per-rate zero bad-scalar counts resolve the faithful MCA prize and expose the
satisfy/maximality specification for the selected lattice thresholds. This is the prize-spec
version of the #140 count-frontier route. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses domain fun j =>
    MCALowerWitness.ofLe (hδ_le_one j) <| by
      rw [epsMCA_eq_zero_of_forall_mcaBadCount_eq_zero (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (hzero j)]
      simp

/-- Per-rate direct no-bad-event frontiers resolve the faithful MCA prize and expose the
satisfy/maximality specification for the selected lattice thresholds. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEvent
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
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses domain fun j =>
    MCALowerWitness.ofLe (hδ_le_one j) <| by
      rw [epsMCA_eq_zero_of_forall_not_mcaEvent (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (hno j)]
      simp

/-- Project the per-rate threshold specification from repaired double-cover data. -/
theorem exists_mcaPrizeLatticeSpec_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  rcases exists_mcaPrizeLatticeResolved_with_spec_ofDoubleCover
      domain δ hδ_le_one hcov with
    ⟨τ, _hτ, hspec⟩
  exact ⟨τ, hspec⟩

/-- Project the per-rate threshold specification from named bad-scalar double-cover data. -/
theorem exists_mcaPrizeLatticeSpec_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  rcases exists_mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCover
      domain δ hδ_le_one hcov with
    ⟨τ, _hτ, hspec⟩
  exact ⟨τ, hspec⟩

/-- Project the per-rate threshold specification from zero bad-scalar counts. -/
theorem exists_mcaPrizeLatticeSpec_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  rcases exists_mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zero
      domain δ hδ_le_one hzero with
    ⟨τ, _hτ, hspec⟩
  exact ⟨τ, hspec⟩

/-- Project the per-rate threshold specification from direct no-bad-event frontiers. -/
theorem exists_mcaPrizeLatticeSpec_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  rcases exists_mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEvent
      domain δ hδ_le_one hno with
    ⟨τ, _hτ, hspec⟩
  exact ⟨τ, hspec⟩

/-- Package repaired double-cover data into all four per-rate threshold lower brackets. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_allRates_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
            mcaThreshold C epsStar hne := by
  intro j
  exact mcaThreshold_spec_and_lower_bracket_prize_ofDoubleCover
    domain j (δ j) (hδ_le_one j) (hcov j)

/-- Package named per-bad-scalar double-cover data into all four per-rate threshold lower
brackets. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_allRates_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
            mcaThreshold C epsStar hne := by
  intro j
  exact mcaThreshold_spec_and_lower_bracket_prize_ofBadScalarDoubleCover
    domain j (δ j) (hδ_le_one j) (hcov j)

/-- Package zero bad-scalar counts into all four per-rate threshold lower brackets. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_allRates_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
            mcaThreshold C epsStar hne := by
  intro j
  exact mcaThreshold_spec_and_lower_bracket_prize_of_mcaBadCount_zero
    domain j (δ j) (hδ_le_one j) (hzero j)

/-- Package direct no-bad-event frontiers into all four per-rate threshold lower brackets. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_allRates_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
            mcaThreshold C epsStar hne := by
  intro j
  exact mcaThreshold_spec_and_lower_bracket_prize_of_forall_not_mcaEvent
    domain j (δ j) (hδ_le_one j) (hno j)

/-- Package repaired double-cover data and explicit upper witnesses into all four per-rate
threshold two-sided brackets. -/
theorem mcaThreshold_spec_and_bracket_prize_allRates_ofDoubleCover
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
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
              mcaThreshold C epsStar hne ∧
            mcaThreshold C epsStar hne <
              latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  intro j
  exact mcaThreshold_spec_and_bracket_prize_ofDoubleCover
    domain j (δ j) (hδ_le_one j) (hcov j) (whi j) (hδhi j)

/-- Package named per-bad-scalar double-cover data and explicit upper witnesses into all four
per-rate threshold two-sided brackets. -/
theorem mcaThreshold_spec_and_bracket_prize_allRates_ofBadScalarDoubleCover
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
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
              mcaThreshold C epsStar hne ∧
            mcaThreshold C epsStar hne <
              latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  intro j
  exact mcaThreshold_spec_and_bracket_prize_ofBadScalarDoubleCover
    domain j (δ j) (hδ_le_one j) (hcov j) (whi j) (hδhi j)

/-- Package zero bad-scalar counts and explicit upper witnesses into all four per-rate threshold
two-sided brackets. -/
theorem mcaThreshold_spec_and_bracket_prize_allRates_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
              mcaThreshold C epsStar hne ∧
            mcaThreshold C epsStar hne <
              latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  intro j
  exact mcaThreshold_spec_and_bracket_prize_of_mcaBadCount_zero
    domain j (δ j) (hδ_le_one j) (hzero j) (whi j) (hδhi j)

/-- Package direct no-bad-event frontiers and explicit upper witnesses into all four per-rate
threshold two-sided brackets. -/
theorem mcaThreshold_spec_and_bracket_prize_allRates_of_forall_not_mcaEvent
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
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
              mcaThreshold C epsStar hne ∧
            mcaThreshold C epsStar hne <
              latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  intro j
  exact mcaThreshold_spec_and_bracket_prize_of_forall_not_mcaEvent
    domain j (δ j) (hδ_le_one j) (hno j) (whi j) (hδhi j)

private theorem exists_lineDecoding_mcaPrizeLatticeSpec_and_lower_brackets_of_lowerWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (w : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
          Set (ι → F)) epsStar)
    (hwδ : ∀ j : Fin 4, (w j).δ = δ j) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  rcases exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses domain w with
    ⟨τ, _hτ, hspec⟩
  refine ⟨τ, hspec, ?_⟩
  intro j
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  rcases hspec j with ⟨hne, _hsat, hmax⟩
  have hle_lower :
      latticeIndexOf (ι := ι) (w j).δ (w j).le_one ≤ mcaThreshold C epsStar hne := by
    exact MCALowerWitness_le_mcaThreshold C epsStar hne (w j)
  have hle_threshold : mcaThreshold C epsStar hne ≤ τ j := by
    exact hmax _ (mcaThreshold_spec C epsStar hne)
  have hidx :
      latticeIndexOf (ι := ι) (w j).δ (w j).le_one =
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) := by
    apply Fin.ext
    simp [latticeIndexOf_val, hwδ j]
  exact hidx ▸ le_trans hle_lower hle_threshold

/-- Project the per-rate threshold specification and lower lattice brackets from repaired
double-cover data. -/
theorem exists_mcaPrizeLatticeSpec_and_lower_brackets_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_lineDecoding_mcaPrizeLatticeSpec_and_lower_brackets_of_lowerWitnesses
    domain δ hδ_le_one
    (fun j => MCALowerWitness.ofDoubleCover
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hcov j))
    (fun _ => rfl)

/-- Project the per-rate threshold specification and lower lattice brackets from named
bad-scalar double-cover data. -/
theorem exists_mcaPrizeLatticeSpec_and_lower_brackets_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_lineDecoding_mcaPrizeLatticeSpec_and_lower_brackets_of_lowerWitnesses
    domain δ hδ_le_one
    (fun j => MCALowerWitness.ofBadScalarDoubleCover
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hcov j))
    (fun _ => rfl)

/-- Project the per-rate threshold specification and lower lattice brackets from zero
bad-scalar counts. -/
theorem exists_mcaPrizeLatticeSpec_and_lower_brackets_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_lineDecoding_mcaPrizeLatticeSpec_and_lower_brackets_of_lowerWitnesses
    domain δ hδ_le_one
    (fun j => MCALowerWitness.of_mcaBadCount_zero
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hzero j))
    (fun _ => rfl)

/-- Project the per-rate threshold specification and lower lattice brackets from direct
no-bad-event frontiers. -/
theorem exists_mcaPrizeLatticeSpec_and_lower_brackets_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_lineDecoding_mcaPrizeLatticeSpec_and_lower_brackets_of_lowerWitnesses
    domain δ hδ_le_one
    (fun j => MCALowerWitness.of_forall_not_mcaEvent
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hno j))
    (fun _ => rfl)

/-- Project the per-rate threshold specification and lower lattice brackets from direct
vanishing `ε_mca` frontiers. -/
theorem exists_mcaPrizeLatticeSpec_and_lower_brackets_of_epsMCA_eq_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_mcaPrizeLatticeSpec_and_lower_brackets_ofDoubleCover domain δ hδ_le_one <|
    indexed_MCAForallDoubleCover_of_epsMCA_eq_zero
      (fun j : Fin 4 =>
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
      δ heps

private theorem exists_lineDecoding_mcaPrizeLatticeSpec_and_brackets_of_lowerWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (w : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
          Set (ι → F)) epsStar)
    (hwδ : ∀ j : Fin 4, (w j).δ = δ j)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
          Set (ι → F)) epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases exists_lineDecoding_mcaPrizeLatticeSpec_and_lower_brackets_of_lowerWitnesses
      domain δ hδ_le_one w hwδ with
    ⟨τ, hspec, hlower⟩
  refine ⟨τ, hspec, hlower, ?_⟩
  intro j
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  rcases hspec j with ⟨hne, hsat, _hmax⟩
  have hτ_le_threshold : τ j ≤ mcaThreshold C epsStar hne :=
    le_mcaThreshold C epsStar hne hsat
  have hthreshold_lt_upper :
      mcaThreshold C epsStar hne < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
    mcaThreshold_lt_MCAUpperWitness C epsStar hne (whi j) (hδhi j)
  exact lt_of_le_of_lt hτ_le_threshold hthreshold_lt_upper

/-- Project the selected-threshold specification and two-sided lattice brackets from repaired
double-cover data and explicit upper witnesses. -/
theorem exists_mcaPrizeLatticeSpec_and_brackets_ofDoubleCover
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
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  exists_lineDecoding_mcaPrizeLatticeSpec_and_brackets_of_lowerWitnesses
    domain δ hδ_le_one
    (fun j => MCALowerWitness.ofDoubleCover
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hcov j))
    (fun _ => rfl) whi hδhi

/-- Project the selected-threshold specification and two-sided lattice brackets from named
bad-scalar double-cover data and explicit upper witnesses. -/
theorem exists_mcaPrizeLatticeSpec_and_brackets_ofBadScalarDoubleCover
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
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  exists_lineDecoding_mcaPrizeLatticeSpec_and_brackets_of_lowerWitnesses
    domain δ hδ_le_one
    (fun j => MCALowerWitness.ofBadScalarDoubleCover
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hcov j))
    (fun _ => rfl) whi hδhi

/-- Project the selected-threshold specification and two-sided lattice brackets from zero
bad-count data and explicit upper witnesses. -/
theorem exists_mcaPrizeLatticeSpec_and_brackets_of_mcaBadCount_zero
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
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  exists_lineDecoding_mcaPrizeLatticeSpec_and_brackets_of_lowerWitnesses
    domain δ hδ_le_one
    (fun j => MCALowerWitness.of_mcaBadCount_zero
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hzero j))
    (fun _ => rfl) whi hδhi

/-- Project the selected-threshold specification and two-sided lattice brackets from no-event
data and explicit upper witnesses. -/
theorem exists_mcaPrizeLatticeSpec_and_brackets_of_forall_not_mcaEvent
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
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  exists_lineDecoding_mcaPrizeLatticeSpec_and_brackets_of_lowerWitnesses
    domain δ hδ_le_one
    (fun j => MCALowerWitness.of_forall_not_mcaEvent
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hno j))
    (fun _ => rfl) whi hδhi

/-- Project the selected-threshold specification and two-sided lattice brackets from direct
vanishing `ε_mca` frontiers and explicit upper witnesses. -/
theorem exists_mcaPrizeLatticeSpec_and_brackets_of_epsMCA_eq_zero
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
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  exists_mcaPrizeLatticeSpec_and_brackets_ofDoubleCover domain δ hδ_le_one
    (indexed_MCAForallDoubleCover_of_epsMCA_eq_zero
      (fun j : Fin 4 =>
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
      δ heps)
    whi hδhi

/-- Project the selected-threshold specification and two-sided lattice brackets from repaired
double-cover data, and also expose the corresponding prize-lattice resolution for the selected
threshold family. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_brackets_ofDoubleCover
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
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          (∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
            ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases exists_mcaPrizeLatticeSpec_and_brackets_ofDoubleCover
      domain δ hδ_le_one hcov whi hδhi with
    ⟨τ, hspec, hlower, hupper⟩
  exact ⟨τ, (mcaPrizeLatticeResolved_iff domain τ).mpr hspec, hspec, hlower, hupper⟩

/-- Direct vanishing `ε_mca` frontiers and explicit upper witnesses supply a
selected-threshold lattice resolution, exact threshold specs, and two-sided lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_epsMCA_eq_zero
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
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
          (∀ j : Fin 4,
            latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
            ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  exists_mcaPrizeLatticeResolved_with_spec_and_brackets_ofDoubleCover domain δ hδ_le_one
    (indexed_MCAForallDoubleCover_of_epsMCA_eq_zero
      (fun j : Fin 4 =>
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
      δ heps)
    whi hδhi

/-- Package repaired double-cover frontiers and explicit adjacent upper witnesses into the generic
four-rate adjacent-witness frontier. -/
noncomputable def mcaPrizeAdjacentWitnessFrontier_ofDoubleCover_and_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    MCAPrizeAdjacentWitnessFrontier (F := F) domain where
  lower := fun j =>
    GrandChallenges.MCALowerWitness.ofDoubleCover
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hcov j)
  upper := whi
  upper_le_one := hδhi
  adjacent := by
    intro j
    exact hadj j

/-- Repaired double-cover adjacent frontiers resolve the four-rate MCA prize via the generic
adjacent-frontier API. -/
theorem mcaPrizeLatticeResolved_ofDoubleCoverAdjacentFrontier
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)) := by
  simpa using
    mcaPrizeLatticeResolved_of_adjacent_frontier domain
      (mcaPrizeAdjacentWitnessFrontier_ofDoubleCover_and_upperWitnesses
        domain δ hδ_le_one hcov whi hδhi hadj)

/-- Package named bad-scalar double-cover frontiers and explicit adjacent upper witnesses into the
generic four-rate adjacent-witness frontier. -/
noncomputable def mcaPrizeAdjacentWitnessFrontier_ofBadScalarDoubleCover_and_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    MCAPrizeAdjacentWitnessFrontier (F := F) domain where
  lower := fun j =>
    GrandChallenges.MCALowerWitness.ofBadScalarDoubleCover
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hcov j)
  upper := whi
  upper_le_one := hδhi
  adjacent := by
    intro j
    exact hadj j

/-- Named bad-scalar double-cover adjacent frontiers resolve the four-rate MCA prize via the
generic adjacent-frontier API. -/
theorem mcaPrizeLatticeResolved_ofBadScalarDoubleCoverAdjacentFrontier
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)) := by
  simpa using
    mcaPrizeLatticeResolved_of_adjacent_frontier domain
      (mcaPrizeAdjacentWitnessFrontier_ofBadScalarDoubleCover_and_upperWitnesses
        domain δ hδ_le_one hcov whi hδhi hadj)

/-- Package zero bad-scalar count frontiers and explicit adjacent upper witnesses into the generic
four-rate adjacent-witness frontier. -/
noncomputable def mcaPrizeAdjacentWitnessFrontier_of_mcaBadCount_zero_and_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    MCAPrizeAdjacentWitnessFrontier (F := F) domain where
  lower := fun j =>
    GrandChallenges.MCALowerWitness.of_mcaBadCount_zero
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hzero j)
  upper := whi
  upper_le_one := hδhi
  adjacent := by
    intro j
    exact hadj j

/-- Zero bad-scalar count adjacent frontiers resolve the four-rate MCA prize via the generic
adjacent-frontier API. -/
theorem mcaPrizeLatticeResolved_of_mcaBadCount_zeroAdjacentFrontier
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)) := by
  simpa using
    mcaPrizeLatticeResolved_of_adjacent_frontier domain
      (mcaPrizeAdjacentWitnessFrontier_of_mcaBadCount_zero_and_upperWitnesses
        domain δ hδ_le_one hzero whi hδhi hadj)

/-- Package direct no-bad-event frontiers and explicit adjacent upper witnesses into the generic
four-rate adjacent-witness frontier. -/
noncomputable def mcaPrizeAdjacentWitnessFrontier_of_forall_not_mcaEvent_and_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    MCAPrizeAdjacentWitnessFrontier (F := F) domain where
  lower := fun j =>
    GrandChallenges.MCALowerWitness.of_forall_not_mcaEvent
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hno j)
  upper := whi
  upper_le_one := hδhi
  adjacent := by
    intro j
    exact hadj j

/-- Direct no-bad-event adjacent frontiers resolve the four-rate MCA prize via the generic
adjacent-frontier API. -/
theorem mcaPrizeLatticeResolved_of_forall_not_mcaEventAdjacentFrontier
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)) := by
  simpa using
    mcaPrizeLatticeResolved_of_adjacent_frontier domain
      (mcaPrizeAdjacentWitnessFrontier_of_forall_not_mcaEvent_and_upperWitnesses
        domain δ hδ_le_one hno whi hδhi hadj)

/-- Repaired double-cover adjacent frontiers resolve the four-rate MCA prize through the generic
adjacent-frontier API and expose the satisfy/maximality specification for those concrete
thresholds. -/
theorem mcaPrizeLatticeResolved_with_spec_ofDoubleCoverAdjacentFrontier
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hτ : mcaPrizeLatticeResolved domain τ :=
    mcaPrizeLatticeResolved_ofDoubleCoverAdjacentFrontier
      domain δ hδ_le_one hcov whi hδhi hadj
  exact ⟨hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

/-- Named bad-scalar double-cover adjacent frontiers resolve the four-rate MCA prize through the
generic adjacent-frontier API and expose the satisfy/maximality specification for those concrete
thresholds. -/
theorem mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCoverAdjacentFrontier
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hτ : mcaPrizeLatticeResolved domain τ :=
    mcaPrizeLatticeResolved_ofBadScalarDoubleCoverAdjacentFrontier
      domain δ hδ_le_one hcov whi hδhi hadj
  exact ⟨hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

/-- Zero bad-scalar count adjacent frontiers resolve the four-rate MCA prize through the generic
adjacent-frontier API and expose the satisfy/maximality specification for those concrete
thresholds. -/
theorem mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zeroAdjacentFrontier
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hτ : mcaPrizeLatticeResolved domain τ :=
    mcaPrizeLatticeResolved_of_mcaBadCount_zeroAdjacentFrontier
      domain δ hδ_le_one hzero whi hδhi hadj
  exact ⟨hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

/-- Direct no-bad-event adjacent frontiers resolve the four-rate MCA prize through the generic
adjacent-frontier API and expose the satisfy/maximality specification for those concrete
thresholds. -/
theorem mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEventAdjacentFrontier
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hτ : mcaPrizeLatticeResolved domain τ :=
    mcaPrizeLatticeResolved_of_forall_not_mcaEventAdjacentFrontier
      domain δ hδ_le_one hno whi hδhi hadj
  exact ⟨hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

/-- Adjacent repaired double-cover frontiers resolve the four-rate MCA prize at the repaired
lower-frontier lattice indices and expose the satisfy/maximality specification for those concrete
thresholds. -/
theorem mcaPrizeLatticeResolved_with_spec_ofDoubleCover_and_adjacent_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hτ : mcaPrizeLatticeResolved domain τ :=
    mcaPrizeLatticeResolved_ofDoubleCover_and_adjacent_upperWitnesses
      domain δ hδ_le_one hcov whi hδhi hadj
  exact ⟨hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

/-- Adjacent named bad-scalar double-cover frontiers resolve the four-rate MCA prize at the repaired
lower-frontier lattice indices and expose the satisfy/maximality specification for those concrete
thresholds. -/
theorem mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hτ : mcaPrizeLatticeResolved domain τ :=
    mcaPrizeLatticeResolved_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
      domain δ hδ_le_one hcov whi hδhi hadj
  exact ⟨hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

/-- Adjacent zero bad-scalar count frontiers resolve the four-rate MCA prize at the repaired
lower-frontier lattice indices and expose the satisfy/maximality specification for those concrete
thresholds. -/
theorem mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zero_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hτ : mcaPrizeLatticeResolved domain τ :=
    mcaPrizeLatticeResolved_of_mcaBadCount_zero_and_adjacent_upperWitnesses
      domain δ hδ_le_one hzero whi hδhi hadj
  exact ⟨hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

/-- Adjacent direct no-bad-event frontiers resolve the four-rate MCA prize at the repaired
lower-frontier lattice indices and expose the satisfy/maximality specification for those concrete
thresholds. -/
theorem mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hτ : mcaPrizeLatticeResolved domain τ :=
    mcaPrizeLatticeResolved_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
      domain δ hδ_le_one hno whi hδhi hadj
  exact ⟨hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

set_option linter.style.longLine false in
/-- Adjacent repaired double-cover frontiers resolve the four-rate MCA prize, expose the exact
threshold specification, and package the lower bracket at the same concrete lower lattice index. -/
theorem mcaPrizeLatticeResolved_with_spec_and_lower_brackets_ofDoubleCover_and_adjacent_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
      ∀ j : Fin 4,
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hspec :=
    mcaPrizeLatticeResolved_with_spec_ofDoubleCover_and_adjacent_upperWitnesses
      domain δ hδ_le_one hcov whi hδhi hadj
  exact ⟨hspec.1, hspec.2, fun _ => le_rfl⟩

set_option linter.style.longLine false in
/-- Adjacent named bad-scalar double-cover frontiers resolve the four-rate MCA prize, expose the
exact threshold specification, and package the lower bracket at the same concrete lower index. -/
theorem
    mcaPrizeLatticeResolved_with_spec_and_lower_brackets_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
      ∀ j : Fin 4,
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hspec :=
    mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
      domain δ hδ_le_one hcov whi hδhi hadj
  exact ⟨hspec.1, hspec.2, fun _ => le_rfl⟩

set_option linter.style.longLine false in
/-- Adjacent zero bad-scalar count frontiers resolve the four-rate MCA prize, expose the exact
threshold specification, and package the lower bracket at the same concrete lower lattice index. -/
theorem
    mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_mcaBadCount_zero_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
      ∀ j : Fin 4,
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hspec :=
    mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zero_and_adjacent_upperWitnesses
      domain δ hδ_le_one hzero whi hδhi hadj
  exact ⟨hspec.1, hspec.2, fun _ => le_rfl⟩

set_option linter.style.longLine false in
/-- Adjacent direct no-bad-event frontiers resolve the four-rate MCA prize, expose the exact
threshold specification, and package the lower bracket at the same concrete lower lattice index. -/
theorem
    mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
      ∀ j : Fin 4,
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  have hspec :=
    mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
      domain δ hδ_le_one hno whi hδhi hadj
  exact ⟨hspec.1, hspec.2, fun _ => le_rfl⟩

/-- Add the immediate lower and adjacent upper lattice brackets to a concrete adjacent
`mcaPrizeLatticeResolved ∧ spec` witness. -/
private theorem mcaPrizeLatticeResolved_with_spec_and_adjacent_brackets_of_with_spec
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1)
    (hspec :
      let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
        fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            (∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
  refine ⟨hspec.1, ?_⟩
  intro j
  rcases hspec.2 j with ⟨hne, hsat, hmax⟩
  refine ⟨hne, hsat, hmax, le_rfl, ?_⟩
  have hval :
      (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val <
        (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val := by
    have h := hadj j
    omega
  simpa [τ] using (Fin.lt_def.mpr hval)

/-- Adjacent repaired double-cover frontiers expose the exact threshold specification together
with both lattice brackets for the concrete lower-index threshold family. -/
theorem mcaPrizeLatticeResolved_with_spec_and_brackets_ofDoubleCover_and_adjacent_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            (∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  mcaPrizeLatticeResolved_with_spec_and_adjacent_brackets_of_with_spec
    domain δ hδ_le_one whi hδhi hadj
    (mcaPrizeLatticeResolved_with_spec_ofDoubleCover_and_adjacent_upperWitnesses
      domain δ hδ_le_one hcov whi hδhi hadj)

set_option linter.style.longLine false in
/-- Adjacent named bad-scalar double-cover frontiers expose the exact threshold specification
together with both lattice brackets for the concrete lower-index threshold family. -/
theorem mcaPrizeLatticeResolved_with_spec_and_brackets_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            (∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  mcaPrizeLatticeResolved_with_spec_and_adjacent_brackets_of_with_spec
    domain δ hδ_le_one whi hδhi hadj
    (mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
      domain δ hδ_le_one hcov whi hδhi hadj)

set_option linter.style.longLine false in
/-- Adjacent zero bad-scalar count frontiers expose the exact threshold specification together
with both lattice brackets for the concrete lower-index threshold family. -/
theorem mcaPrizeLatticeResolved_with_spec_and_brackets_of_mcaBadCount_zero_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            (∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  mcaPrizeLatticeResolved_with_spec_and_adjacent_brackets_of_with_spec
    domain δ hδ_le_one whi hδhi hadj
    (mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zero_and_adjacent_upperWitnesses
      domain δ hδ_le_one hzero whi hδhi hadj)

set_option linter.style.longLine false in
/-- Adjacent direct no-bad-event frontiers expose the exact threshold specification together
with both lattice brackets for the concrete lower-index threshold family. -/
theorem mcaPrizeLatticeResolved_with_spec_and_brackets_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            (∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
              latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j ∧
                τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  mcaPrizeLatticeResolved_with_spec_and_adjacent_brackets_of_with_spec
    domain δ hδ_le_one whi hδhi hadj
    (mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
      domain δ hδ_le_one hno whi hδhi hadj)

/-- Project the exact threshold specification from adjacent repaired double-cover frontiers. -/
theorem mcaPrizeLatticeSpec_ofDoubleCover_and_adjacent_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ _ : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (τ j) ∧
          ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  (mcaPrizeLatticeResolved_with_spec_ofDoubleCover_and_adjacent_upperWitnesses
    domain δ hδ_le_one hcov whi hδhi hadj).2

/-- Project the exact threshold specification from adjacent named bad-scalar double-cover
frontiers. -/
theorem mcaPrizeLatticeSpec_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ _ : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (τ j) ∧
          ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  (mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
    domain δ hδ_le_one hcov whi hδhi hadj).2

/-- Project the exact threshold specification from adjacent zero bad-scalar count frontiers. -/
theorem mcaPrizeLatticeSpec_of_mcaBadCount_zero_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ _ : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (τ j) ∧
          ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  (mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zero_and_adjacent_upperWitnesses
    domain δ hδ_le_one hzero whi hδhi hadj).2

/-- Project the exact threshold specification from adjacent direct no-bad-event frontiers. -/
theorem mcaPrizeLatticeSpec_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ _ : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (τ j) ∧
          ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  (mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
    domain δ hδ_le_one hno whi hδhi hadj).2

/-- Project the exact threshold specification from the generic repaired double-cover adjacent
frontier route. -/
theorem mcaPrizeLatticeSpec_ofDoubleCoverAdjacentFrontier
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ _ : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (τ j) ∧
          ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  (mcaPrizeLatticeResolved_with_spec_ofDoubleCoverAdjacentFrontier
    domain δ hδ_le_one hcov whi hδhi hadj).2

/-- Project the exact threshold specification from the generic named bad-scalar double-cover
adjacent frontier route. -/
theorem mcaPrizeLatticeSpec_ofBadScalarDoubleCoverAdjacentFrontier
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ _ : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (τ j) ∧
          ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  (mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCoverAdjacentFrontier
    domain δ hδ_le_one hcov whi hδhi hadj).2

/-- Project the exact threshold specification from the generic zero bad-scalar count adjacent
frontier route. -/
theorem mcaPrizeLatticeSpec_of_mcaBadCount_zeroAdjacentFrontier
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ _ : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (τ j) ∧
          ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  (mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zeroAdjacentFrontier
    domain δ hδ_le_one hzero whi hδhi hadj).2

/-- Project the exact threshold specification from the generic direct no-bad-event adjacent
frontier route. -/
theorem mcaPrizeLatticeSpec_of_forall_not_mcaEventAdjacentFrontier
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
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ _ : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (τ j) ∧
          ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  (mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEventAdjacentFrontier
    domain δ hδ_le_one hno whi hδhi hadj).2

end LineDecodingPrizeSpec

set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_lower_bracket_prize_allRates_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_lower_bracket_prize_allRates_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_lower_bracket_prize_allRates_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_lower_bracket_prize_allRates_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_bracket_prize_allRates_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_bracket_prize_allRates_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_bracket_prize_allRates_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_bracket_prize_allRates_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_lower_brackets_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_lower_brackets_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_lower_brackets_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_lower_brackets_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_lower_brackets_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_brackets_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_brackets_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_brackets_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_brackets_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_brackets_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_brackets_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeAdjacentWitnessFrontier_ofDoubleCover_and_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_ofDoubleCoverAdjacentFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeAdjacentWitnessFrontier_ofBadScalarDoubleCover_and_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_ofBadScalarDoubleCoverAdjacentFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeAdjacentWitnessFrontier_of_mcaBadCount_zero_and_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_of_mcaBadCount_zeroAdjacentFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeAdjacentWitnessFrontier_of_forall_not_mcaEvent_and_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_of_forall_not_mcaEventAdjacentFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_ofDoubleCoverAdjacentFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCoverAdjacentFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zeroAdjacentFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEventAdjacentFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_ofDoubleCover_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_mcaBadCount_zero_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_and_lower_brackets_ofDoubleCover_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_and_lower_brackets_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_mcaBadCount_zero_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_and_brackets_ofDoubleCover_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_and_brackets_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_and_brackets_of_mcaBadCount_zero_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_and_brackets_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeSpec_ofDoubleCover_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeSpec_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeSpec_of_mcaBadCount_zero_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeSpec_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeSpec_ofDoubleCoverAdjacentFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeSpec_ofBadScalarDoubleCoverAdjacentFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeSpec_of_mcaBadCount_zeroAdjacentFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeSpec_of_forall_not_mcaEventAdjacentFrontier

end GrandChallengesLattice

end ProximityGap
