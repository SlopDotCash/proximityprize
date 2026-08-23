/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingSpec

/-!
# Low-output line-decoding prize-threshold wrappers

This companion module keeps `LineDecodingGrandChallengesPrizeSpec.lean` stable while exposing
weaker consumers of its concrete-`mcaThreshold` bracket packages. The repaired line-decoding
hypotheses remain explicit throughout; these declarations only forget the threshold
satisfy/maximality payload from already-proved wrappers.
-/

set_option linter.style.longLine false

namespace ProximityGap

open scoped NNReal

namespace GrandChallengesLattice

open GrandChallenges

section LineDecodingPrizeSpec

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

set_option linter.unusedDecidableInType false in
/-- Repaired double-cover data supplies a prize-rate `MCALowerWitness`, forgetting only the
radius-equality payload from the witness-producing theorem. -/
theorem nonempty_prize_mcaLowerWitness_ofDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) δ) :
    Nonempty (GrandChallenges.MCALowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar) := by
  rcases GrandChallenges.exists_prize_mcaLowerWitness_ofDoubleCover
      domain j δ hδ_le_one hcov with ⟨w, _hwδ⟩
  exact ⟨w⟩

set_option linter.unusedDecidableInType false in
/-- Named per-bad-scalar double-cover data supplies a prize-rate `MCALowerWitness`, forgetting
only the radius-equality payload from the witness-producing theorem. -/
theorem nonempty_prize_mcaLowerWitness_ofBadScalarDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    Nonempty (GrandChallenges.MCALowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar) := by
  rcases GrandChallenges.exists_prize_mcaLowerWitness_ofBadScalarDoubleCover
      domain j δ hδ_le_one hcov with ⟨w, _hwδ⟩
  exact ⟨w⟩

set_option linter.unusedDecidableInType false in
/-- Zero bad-scalar counts supply a prize-rate `MCALowerWitness`, forgetting only the
radius-equality payload from the witness-producing theorem. -/
theorem nonempty_prize_mcaLowerWitness_of_mcaBadCount_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) = 0) :
    Nonempty (GrandChallenges.MCALowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar) := by
  rcases GrandChallenges.exists_prize_mcaLowerWitness_of_mcaBadCount_zero
      domain j δ hδ_le_one hzero with ⟨w, _hwδ⟩
  exact ⟨w⟩

set_option linter.unusedDecidableInType false in
/-- Direct no-bad-event frontiers supply a prize-rate `MCALowerWitness`, forgetting only the
radius-equality payload from the witness-producing theorem. -/
theorem nonempty_prize_mcaLowerWitness_of_forall_not_mcaEvent
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    Nonempty (GrandChallenges.MCALowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar) := by
  rcases GrandChallenges.exists_prize_mcaLowerWitness_of_forall_not_mcaEvent
      domain j δ hδ_le_one hno with ⟨w, _hwδ⟩
  exact ⟨w⟩

set_option linter.unusedDecidableInType false in
/-- Direct vanishing `ε_mca` supplies a prize-rate `MCALowerWitness`, forgetting only the
radius-equality payload from the witness-producing theorem. -/
theorem nonempty_prize_mcaLowerWitness_of_epsMCA_eq_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (heps : epsMCA (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      δ = 0) :
    Nonempty (GrandChallenges.MCALowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar) := by
  rcases GrandChallenges.exists_prize_mcaLowerWitness_of_epsMCA_eq_zero
      domain j δ hδ_le_one heps with ⟨w, _hwδ⟩
  exact ⟨w⟩

set_option linter.unusedDecidableInType false in
/-- Repaired double-cover data supplies all four prize-rate `MCALowerWitness` nonemptiness
facts, dropping the witness radius-equality payloads. -/
theorem nonempty_prize_mcaLowerWitnesses_allRates_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    ∀ j : Fin 4,
      Nonempty (GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) := by
  intro j
  exact nonempty_prize_mcaLowerWitness_ofDoubleCover
    domain j (δ j) (hδ_le_one j) (hcov j)

set_option linter.unusedDecidableInType false in
/-- Named per-bad-scalar double-cover data supplies all four prize-rate `MCALowerWitness`
nonemptiness facts, dropping the witness radius-equality payloads. -/
theorem nonempty_prize_mcaLowerWitnesses_allRates_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∀ j : Fin 4,
      Nonempty (GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) := by
  intro j
  exact nonempty_prize_mcaLowerWitness_ofBadScalarDoubleCover
    domain j (δ j) (hδ_le_one j) (hcov j)

set_option linter.unusedDecidableInType false in
/-- Zero bad-scalar counts supply all four prize-rate `MCALowerWitness` nonemptiness facts,
dropping the witness radius-equality payloads. -/
theorem nonempty_prize_mcaLowerWitnesses_allRates_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    ∀ j : Fin 4,
      Nonempty (GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) := by
  intro j
  exact nonempty_prize_mcaLowerWitness_of_mcaBadCount_zero
    domain j (δ j) (hδ_le_one j) (hzero j)

set_option linter.unusedDecidableInType false in
/-- Direct no-bad-event frontiers supply all four prize-rate `MCALowerWitness` nonemptiness
facts, dropping the witness radius-equality payloads. -/
theorem nonempty_prize_mcaLowerWitnesses_allRates_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∀ j : Fin 4,
      Nonempty (GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) := by
  intro j
  exact nonempty_prize_mcaLowerWitness_of_forall_not_mcaEvent
    domain j (δ j) (hδ_le_one j) (hno j)

set_option linter.unusedDecidableInType false in
/-- Direct vanishing `ε_mca` supplies all four prize-rate `MCALowerWitness` nonemptiness facts,
dropping the witness radius-equality payloads. -/
theorem nonempty_prize_mcaLowerWitnesses_allRates_of_epsMCA_eq_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0) :
    ∀ j : Fin 4,
      Nonempty (GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) := by
  intro j
  exact nonempty_prize_mcaLowerWitness_of_epsMCA_eq_zero
    domain j (δ j) (hδ_le_one j) (heps j)

set_option linter.unusedDecidableInType false in
/-- Repaired double-cover data makes all four concrete prize-rate `mcaThreshold`s exist,
dropping all threshold-specification and bracket payload. -/
theorem mcaThresholdExists_prize_allRates_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    ∀ j : Fin 4,
      mcaThresholdExists
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar := by
  intro j
  exact mcaThresholdExists_prize_ofDoubleCover domain j (δ j) (hδ_le_one j) (hcov j)

set_option linter.unusedDecidableInType false in
/-- Named per-bad-scalar double-cover data makes all four concrete prize-rate `mcaThreshold`s
exist, dropping all threshold-specification and bracket payload. -/
theorem mcaThresholdExists_prize_allRates_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∀ j : Fin 4,
      mcaThresholdExists
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar := by
  intro j
  exact mcaThresholdExists_prize_ofBadScalarDoubleCover
    domain j (δ j) (hδ_le_one j) (hcov j)

set_option linter.unusedDecidableInType false in
/-- Zero bad-scalar counts make all four concrete prize-rate `mcaThreshold`s exist, dropping all
threshold-specification and bracket payload. -/
theorem mcaThresholdExists_prize_allRates_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    ∀ j : Fin 4,
      mcaThresholdExists
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar := by
  intro j
  exact mcaThresholdExists_prize_of_mcaBadCount_zero
    domain j (δ j) (hδ_le_one j) (hzero j)

set_option linter.unusedDecidableInType false in
/-- Direct no-bad-event frontiers make all four concrete prize-rate `mcaThreshold`s exist,
dropping all threshold-specification and bracket payload. -/
theorem mcaThresholdExists_prize_allRates_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∀ j : Fin 4,
      mcaThresholdExists
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar := by
  intro j
  exact mcaThresholdExists_prize_of_forall_not_mcaEvent
    domain j (δ j) (hδ_le_one j) (hno j)

set_option linter.unusedDecidableInType false in
/-- Direct vanishing `ε_mca` makes all four concrete prize-rate `mcaThreshold`s exist,
dropping all threshold-specification and bracket payload. -/
theorem mcaThresholdExists_prize_allRates_of_epsMCA_eq_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0) :
    ∀ j : Fin 4,
      mcaThresholdExists
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar := by
  intro j
  exact mcaThresholdExists_prize_of_epsMCA_eq_zero
    domain j (δ j) (hδ_le_one j) (heps j)

/-- Repaired double-cover data supplies all four concrete `mcaThreshold` lower brackets, dropping
the threshold satisfy/maximality payload. -/
theorem mcaThreshold_lower_bracket_prize_allRates_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
          mcaThreshold C epsStar hne := by
  intro j
  rcases mcaThreshold_spec_and_lower_bracket_prize_allRates_ofDoubleCover
      domain δ hδ_le_one hcov j with
    ⟨hne, _hsat, hlower⟩
  exact ⟨hne, hlower⟩

/-- Named per-bad-scalar double-cover data supplies all four concrete `mcaThreshold` lower
brackets, dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_lower_bracket_prize_allRates_ofBadScalarDoubleCover
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
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
          mcaThreshold C epsStar hne := by
  intro j
  rcases mcaThreshold_spec_and_lower_bracket_prize_allRates_ofBadScalarDoubleCover
      domain δ hδ_le_one hcov j with
    ⟨hne, _hsat, hlower⟩
  exact ⟨hne, hlower⟩

/-- Zero bad-scalar counts supply all four concrete `mcaThreshold` lower brackets, dropping the
threshold satisfy/maximality payload. -/
theorem mcaThreshold_lower_bracket_prize_allRates_of_mcaBadCount_zero
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
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
          mcaThreshold C epsStar hne := by
  intro j
  rcases mcaThreshold_spec_and_lower_bracket_prize_allRates_of_mcaBadCount_zero
      domain δ hδ_le_one hzero j with
    ⟨hne, _hsat, hlower⟩
  exact ⟨hne, hlower⟩

/-- Direct no-bad-event frontiers supply all four concrete `mcaThreshold` lower brackets, dropping
the threshold satisfy/maximality payload. -/
theorem mcaThreshold_lower_bracket_prize_allRates_of_forall_not_mcaEvent
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
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
          mcaThreshold C epsStar hne := by
  intro j
  rcases mcaThreshold_spec_and_lower_bracket_prize_allRates_of_forall_not_mcaEvent
      domain δ hδ_le_one hno j with
    ⟨hne, _hsat, hlower⟩
  exact ⟨hne, hlower⟩

/-- Direct vanishing `ε_mca` supplies all four concrete `mcaThreshold` lower brackets, dropping
the threshold satisfy/maximality payload. -/
theorem mcaThreshold_lower_bracket_prize_allRates_of_epsMCA_eq_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
          mcaThreshold C epsStar hne := by
  intro j
  rcases mcaThreshold_spec_and_lower_bracket_prize_of_epsMCA_eq_zero
      domain j (δ j) (hδ_le_one j) (heps j) with
    ⟨hne, _hsat, hlower⟩
  exact ⟨hne, hlower⟩

/-- Repaired double-cover data and explicit upper witnesses supply all four concrete
`mcaThreshold` two-sided brackets, dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_bracket_prize_allRates_ofDoubleCover
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
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
            mcaThreshold C epsStar hne ∧
          mcaThreshold C epsStar hne <
            latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  intro j
  rcases mcaThreshold_spec_and_bracket_prize_allRates_ofDoubleCover
      domain δ hδ_le_one hcov whi hδhi j with
    ⟨hne, _hsat, hlower, hupper⟩
  exact ⟨hne, hlower, hupper⟩

/-- Named per-bad-scalar double-cover data and explicit upper witnesses supply all four concrete
`mcaThreshold` two-sided brackets, dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_bracket_prize_allRates_ofBadScalarDoubleCover
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
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
            mcaThreshold C epsStar hne ∧
          mcaThreshold C epsStar hne <
            latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  intro j
  rcases mcaThreshold_spec_and_bracket_prize_allRates_ofBadScalarDoubleCover
      domain δ hδ_le_one hcov whi hδhi j with
    ⟨hne, _hsat, hlower, hupper⟩
  exact ⟨hne, hlower, hupper⟩

/-- Zero bad-scalar counts and explicit upper witnesses supply all four concrete `mcaThreshold`
two-sided brackets, dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_bracket_prize_allRates_of_mcaBadCount_zero
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
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
            mcaThreshold C epsStar hne ∧
          mcaThreshold C epsStar hne <
            latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  intro j
  rcases mcaThreshold_spec_and_bracket_prize_allRates_of_mcaBadCount_zero
      domain δ hδ_le_one hzero whi hδhi j with
    ⟨hne, _hsat, hlower, hupper⟩
  exact ⟨hne, hlower, hupper⟩

/-- Direct no-bad-event frontiers and explicit upper witnesses supply all four concrete
`mcaThreshold` two-sided brackets, dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_bracket_prize_allRates_of_forall_not_mcaEvent
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
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
            mcaThreshold C epsStar hne ∧
          mcaThreshold C epsStar hne <
            latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  intro j
  rcases mcaThreshold_spec_and_bracket_prize_allRates_of_forall_not_mcaEvent
      domain δ hδ_le_one hno whi hδhi j with
    ⟨hne, _hsat, hlower, hupper⟩
  exact ⟨hne, hlower, hupper⟩

/-- Direct vanishing `ε_mca` and explicit upper witnesses supply all four concrete
`mcaThreshold` two-sided brackets, dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_bracket_prize_allRates_of_epsMCA_eq_zero
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
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
            mcaThreshold C epsStar hne ∧
          mcaThreshold C epsStar hne <
            latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  intro j
  rcases mcaThreshold_spec_and_bracket_prize_of_epsMCA_eq_zero
      domain j (δ j) (hδ_le_one j) (heps j) (whi j) (hδhi j) with
    ⟨hne, _hsat, hlower, hupper⟩
  exact ⟨hne, hlower, hupper⟩

/-- Repaired double-cover data supplies a single prize-rate concrete `mcaThreshold` lower bracket,
dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_lower_bracket_prize_ofDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) δ) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne := by
  rcases mcaThreshold_spec_and_lower_bracket_prize_ofDoubleCover
      domain j δ hδ_le_one hcov with
    ⟨hne, _hsat, hlower⟩
  exact ⟨hne, hlower⟩

/-- Named per-bad-scalar double-cover data supplies a single prize-rate concrete `mcaThreshold`
lower bracket, dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_lower_bracket_prize_ofBadScalarDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne := by
  rcases mcaThreshold_spec_and_lower_bracket_prize_ofBadScalarDoubleCover
      domain j δ hδ_le_one hcov with
    ⟨hne, _hsat, hlower⟩
  exact ⟨hne, hlower⟩

/-- Zero bad-scalar counts supply a single prize-rate concrete `mcaThreshold` lower bracket,
dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_lower_bracket_prize_of_mcaBadCount_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) = 0) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne := by
  rcases mcaThreshold_spec_and_lower_bracket_prize_of_mcaBadCount_zero
      domain j δ hδ_le_one hzero with
    ⟨hne, _hsat, hlower⟩
  exact ⟨hne, hlower⟩

/-- Direct no-bad-event frontiers supply a single prize-rate concrete `mcaThreshold` lower bracket,
dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_lower_bracket_prize_of_forall_not_mcaEvent
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne := by
  rcases mcaThreshold_spec_and_lower_bracket_prize_of_forall_not_mcaEvent
      domain j δ hδ_le_one hno with
    ⟨hne, _hsat, hlower⟩
  exact ⟨hne, hlower⟩

/-- Direct vanishing `ε_mca` supplies a single prize-rate concrete `mcaThreshold` lower bracket,
dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_lower_bracket_prize_of_epsMCA_eq_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (heps : epsMCA (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      δ = 0) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne := by
  rcases mcaThreshold_spec_and_lower_bracket_prize_of_epsMCA_eq_zero
      domain j δ hδ_le_one heps with
    ⟨hne, _hsat, hlower⟩
  exact ⟨hne, hlower⟩

/-- Repaired double-cover data and an explicit upper witness supply a single prize-rate concrete
`mcaThreshold` two-sided bracket, dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_bracket_prize_ofDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) δ)
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar)
    (hδhi : whi.δ ≤ 1) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne ∧
        mcaThreshold C epsStar hne < latticeIndexOf (ι := ι) whi.δ hδhi := by
  rcases mcaThreshold_spec_and_bracket_prize_ofDoubleCover
      domain j δ hδ_le_one hcov whi hδhi with
    ⟨hne, _hsat, hlower, hupper⟩
  exact ⟨hne, hlower, hupper⟩

/-- Named per-bad-scalar double-cover data and an explicit upper witness supply a single
prize-rate concrete `mcaThreshold` two-sided bracket, dropping the threshold satisfy/maximality
payload. -/
theorem mcaThreshold_bracket_prize_ofBadScalarDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ)
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar)
    (hδhi : whi.δ ≤ 1) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne ∧
        mcaThreshold C epsStar hne < latticeIndexOf (ι := ι) whi.δ hδhi := by
  rcases mcaThreshold_spec_and_bracket_prize_ofBadScalarDoubleCover
      domain j δ hδ_le_one hcov whi hδhi with
    ⟨hne, _hsat, hlower, hupper⟩
  exact ⟨hne, hlower, hupper⟩

/-- Zero bad-scalar counts and an explicit upper witness supply a single prize-rate concrete
`mcaThreshold` two-sided bracket, dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_bracket_prize_of_mcaBadCount_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) = 0)
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar)
    (hδhi : whi.δ ≤ 1) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne ∧
        mcaThreshold C epsStar hne < latticeIndexOf (ι := ι) whi.δ hδhi := by
  rcases mcaThreshold_spec_and_bracket_prize_of_mcaBadCount_zero
      domain j δ hδ_le_one hzero whi hδhi with
    ⟨hne, _hsat, hlower, hupper⟩
  exact ⟨hne, hlower, hupper⟩

/-- Direct no-bad-event frontiers and an explicit upper witness supply a single prize-rate concrete
`mcaThreshold` two-sided bracket, dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_bracket_prize_of_forall_not_mcaEvent
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ)
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar)
    (hδhi : whi.δ ≤ 1) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne ∧
        mcaThreshold C epsStar hne < latticeIndexOf (ι := ι) whi.δ hδhi := by
  rcases mcaThreshold_spec_and_bracket_prize_of_forall_not_mcaEvent
      domain j δ hδ_le_one hno whi hδhi with
    ⟨hne, _hsat, hlower, hupper⟩
  exact ⟨hne, hlower, hupper⟩

/-- Direct vanishing `ε_mca` and an explicit upper witness supply a single prize-rate concrete
`mcaThreshold` two-sided bracket, dropping the threshold satisfy/maximality payload. -/
theorem mcaThreshold_bracket_prize_of_epsMCA_eq_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (heps : epsMCA (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      δ = 0)
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar)
    (hδhi : whi.δ ≤ 1) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne ∧
        mcaThreshold C epsStar hne < latticeIndexOf (ι := ι) whi.δ hδhi := by
  rcases mcaThreshold_spec_and_bracket_prize_of_epsMCA_eq_zero
      domain j δ hδ_le_one heps whi hδhi with
    ⟨hne, _hsat, hlower, hupper⟩
  exact ⟨hne, hlower, hupper⟩

end LineDecodingPrizeSpec

#print axioms ProximityGap.GrandChallengesLattice.nonempty_prize_mcaLowerWitness_ofDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.nonempty_prize_mcaLowerWitness_ofBadScalarDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.nonempty_prize_mcaLowerWitness_of_mcaBadCount_zero
#print axioms ProximityGap.GrandChallengesLattice.nonempty_prize_mcaLowerWitness_of_forall_not_mcaEvent
#print axioms ProximityGap.GrandChallengesLattice.nonempty_prize_mcaLowerWitness_of_epsMCA_eq_zero
#print axioms ProximityGap.GrandChallengesLattice.nonempty_prize_mcaLowerWitnesses_allRates_ofDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.nonempty_prize_mcaLowerWitnesses_allRates_ofBadScalarDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.nonempty_prize_mcaLowerWitnesses_allRates_of_mcaBadCount_zero
#print axioms ProximityGap.GrandChallengesLattice.nonempty_prize_mcaLowerWitnesses_allRates_of_forall_not_mcaEvent
#print axioms ProximityGap.GrandChallengesLattice.nonempty_prize_mcaLowerWitnesses_allRates_of_epsMCA_eq_zero
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_prize_allRates_ofDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_prize_allRates_ofBadScalarDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_prize_allRates_of_mcaBadCount_zero
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_prize_allRates_of_forall_not_mcaEvent
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_prize_allRates_of_epsMCA_eq_zero
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lower_bracket_prize_allRates_ofDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lower_bracket_prize_allRates_ofBadScalarDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lower_bracket_prize_allRates_of_mcaBadCount_zero
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lower_bracket_prize_allRates_of_forall_not_mcaEvent
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lower_bracket_prize_allRates_of_epsMCA_eq_zero
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_bracket_prize_allRates_ofDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_bracket_prize_allRates_ofBadScalarDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_bracket_prize_allRates_of_mcaBadCount_zero
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_bracket_prize_allRates_of_forall_not_mcaEvent
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_bracket_prize_allRates_of_epsMCA_eq_zero
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lower_bracket_prize_ofDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lower_bracket_prize_ofBadScalarDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lower_bracket_prize_of_mcaBadCount_zero
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lower_bracket_prize_of_forall_not_mcaEvent
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lower_bracket_prize_of_epsMCA_eq_zero
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_bracket_prize_ofDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_bracket_prize_ofBadScalarDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_bracket_prize_of_mcaBadCount_zero
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_bracket_prize_of_forall_not_mcaEvent
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_bracket_prize_of_epsMCA_eq_zero

end GrandChallengesLattice

end ProximityGap
