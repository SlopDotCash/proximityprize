/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Lattice2

/-!
# Prize-lattice specification adapters

This lightweight module keeps the long faithful-lattice file from growing while exposing the
checked satisfy/maximality specification of the conjectural four-rate MCA prize aggregation.
-/

namespace ProximityGap

open scoped NNReal

namespace GrandChallengesLattice

open GrandChallenges

section PrizeSpec

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Project per-rate threshold existence from a concrete faithful MCA prize-lattice resolution. -/
theorem mcaPrizeLatticeResolved.thresholdExists
    (domain : ι ↪ F) {τ : Fin 4 → Fin (Fintype.card ι + 1)}
    (hτ : mcaPrizeLatticeResolved domain τ) (j : Fin 4) :
    mcaThresholdExists
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar := by
  rcases (mcaPrizeLatticeResolved_iff domain τ).mp hτ j with ⟨hne, _⟩
  exact hne

/-- Project the per-rate satisfy fact from a concrete faithful MCA prize-lattice resolution. -/
theorem mcaPrizeLatticeResolved.satisfies
    (domain : ι ↪ F) {τ : Fin 4 → Fin (Fintype.card ι + 1)}
    (hτ : mcaPrizeLatticeResolved domain τ) (j : Fin 4) :
    mcaSatisfies
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar (τ j) := by
  rcases (mcaPrizeLatticeResolved_iff domain τ).mp hτ j with ⟨_, hsatisfies, _⟩
  exact hsatisfies

/-- Project the per-rate maximality fact from a concrete faithful MCA prize-lattice resolution. -/
theorem mcaPrizeLatticeResolved.maximal
    (domain : ι ↪ F) {τ : Fin 4 → Fin (Fintype.card ι + 1)}
    (hτ : mcaPrizeLatticeResolved domain τ) (j : Fin 4)
    (i : Fin (Fintype.card ι + 1))
    (hi : mcaSatisfies
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar i) :
    i ≤ τ j := by
  rcases (mcaPrizeLatticeResolved_iff domain τ).mp hτ j with ⟨_, _, hmax⟩
  exact hmax i hi

/-- Radius-one bad-count bounds resolve the faithful MCA prize lattice at the top index and
expose the full satisfy/maximality specification for that concrete threshold function. -/
theorem mcaPrizeLatticeResolved_with_spec_top_of_radiusOne_bounds
    (domain : ι ↪ F)
    (hbound : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) 1
        ≤ (epsStar : ENNReal)) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩
  have hτ : mcaPrizeLatticeResolved domain τ :=
    mcaPrizeLatticeResolved_top_of_radiusOne_bounds domain hbound
  simpa [τ] using And.intro hτ ((mcaPrizeLatticeResolved_iff domain τ).mp hτ)

/-- The combinatorial choose-bound family resolves the faithful MCA prize lattice at the top
index and exposes the full satisfy/maximality specification for that concrete threshold
function. -/
theorem mcaPrizeLatticeResolved_with_spec_top_of_choose_bounds
    (domain : ι ↪ F)
    (hbound : ∀ j : Fin 4,
      (Nat.choose (Fintype.card ι)
          (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ENNReal)
        / (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal)) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩
    mcaPrizeLatticeResolved domain τ ∧
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩
  have hτ : mcaPrizeLatticeResolved domain τ :=
    mcaPrizeLatticeResolved_top_of_choose_bounds domain hbound
  simpa [τ] using And.intro hτ ((mcaPrizeLatticeResolved_iff domain τ).mp hτ)

omit [DecidableEq ι] [DecidableEq F] in
/-- Low-output projection of `mcaPrizeLatticeResolved_with_spec_top_of_radiusOne_bounds`: it
keeps only the per-rate satisfy/maximality specification for the concrete all-top threshold
function. -/
theorem mcaPrizeLatticeSpec_top_of_radiusOne_bounds
    (domain : ι ↪ F)
    (hbound : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) 1
        ≤ (epsStar : ENNReal)) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ _ : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (τ j) ∧
          ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  classical
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩
  rcases mcaPrizeLatticeResolved_with_spec_top_of_radiusOne_bounds domain hbound with
    ⟨_hτ, hspec⟩
  simpa [τ] using hspec

omit [DecidableEq ι] [DecidableEq F] in
/-- Low-output projection of `mcaPrizeLatticeResolved_with_spec_top_of_choose_bounds`: it keeps
only the per-rate satisfy/maximality specification for the concrete all-top threshold function. -/
theorem mcaPrizeLatticeSpec_top_of_choose_bounds
    (domain : ι ↪ F)
    (hbound : ∀ j : Fin 4,
      (Nat.choose (Fintype.card ι)
          (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ENNReal)
        / (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal)) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ _ : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (τ j) ∧
          ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  classical
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩
  rcases mcaPrizeLatticeResolved_with_spec_top_of_choose_bounds domain hbound with
    ⟨_hτ, hspec⟩
  simpa [τ] using hspec

/-- Radius-one bad-count bounds expose the concrete top-threshold equality at every ABF26
prize rate, without carrying the full resolved predicate. -/
theorem mcaThreshold_eq_top_prize_allRates_of_radiusOne_bounds
    (domain : ι ↪ F)
    (hbound : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) 1
        ≤ (epsStar : ENNReal)) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaThreshold C epsStar hne = ⟨Fintype.card ι, Nat.lt_succ_self _⟩ := by
  intro j
  exact mcaPrizeLatticeResolved_top_of_radiusOne_bounds domain hbound j

/-- The combinatorial choose-bound family exposes the concrete top-threshold equality at every
ABF26 prize rate, without carrying the full resolved predicate. -/
theorem mcaThreshold_eq_top_prize_allRates_of_choose_bounds
    (domain : ι ↪ F)
    (hbound : ∀ j : Fin 4,
      (Nat.choose (Fintype.card ι)
          (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ENNReal)
        / (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal)) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaThreshold C epsStar hne = ⟨Fintype.card ι, Nat.lt_succ_self _⟩ := by
  intro j
  exact mcaPrizeLatticeResolved_top_of_choose_bounds domain hbound j

omit [DecidableEq ι] [DecidableEq F] in
/-- Radius-one bad-count bounds expose the all-top prize specification together with the
endpoint lower bracket `⌊1 · n⌋ ≤ τ j` at every ABF26 prize rate. -/
theorem mcaPrizeLatticeSpec_and_lower_brackets_top_of_radiusOne_bounds
    (domain : ι ↪ F)
    (hbound : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) 1
        ≤ (epsStar : ENNReal)) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩
    (∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ _ : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (τ j) ∧
          ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
      ∀ j : Fin 4, latticeIndexOf (ι := ι) (1 : ℝ≥0) le_rfl ≤ τ j := by
  classical
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩
  have hspec := mcaPrizeLatticeSpec_top_of_radiusOne_bounds domain hbound
  have htop : latticeIndexOf (ι := ι) (1 : ℝ≥0) le_rfl =
      (⟨Fintype.card ι, Nat.lt_succ_self _⟩ : Fin (Fintype.card ι + 1)) := by
    ext
    simp [latticeIndexOf_val]
  refine ⟨by simpa [τ] using hspec, ?_⟩
  intro j
  simpa [τ, htop]

omit [DecidableEq ι] [DecidableEq F] in
/-- The combinatorial choose-bound family exposes the all-top prize specification together
with the endpoint lower bracket `⌊1 · n⌋ ≤ τ j` at every ABF26 prize rate. -/
theorem mcaPrizeLatticeSpec_and_lower_brackets_top_of_choose_bounds
    (domain : ι ↪ F)
    (hbound : ∀ j : Fin 4,
      (Nat.choose (Fintype.card ι)
          (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ENNReal)
        / (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal)) :
    let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
      fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩
    (∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ _ : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (τ j) ∧
          ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
      ∀ j : Fin 4, latticeIndexOf (ι := ι) (1 : ℝ≥0) le_rfl ≤ τ j := by
  classical
  let τ : Fin 4 → Fin (Fintype.card ι + 1) :=
    fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩
  have hspec := mcaPrizeLatticeSpec_top_of_choose_bounds domain hbound
  have htop : latticeIndexOf (ι := ι) (1 : ℝ≥0) le_rfl =
      (⟨Fintype.card ι, Nat.lt_succ_self _⟩ : Fin (Fintype.card ι + 1)) := by
    ext
    simp [latticeIndexOf_val]
  refine ⟨by simpa [τ] using hspec, ?_⟩
  intro j
  simpa [τ, htop]

/-- Per-rate lower MCA witnesses resolve the faithful MCA prize and expose the
satisfy/maximality specification for the selected lattice thresholds. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses
    (domain : ι ↪ F)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  rcases exists_mcaPrizeLatticeResolved_of_lowerWitnesses domain w with ⟨τ, hτ⟩
  exact ⟨τ, hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

omit [DecidableEq ι] [DecidableEq F] in
/-- Per-rate lower MCA witnesses expose only the selected-threshold satisfy/maximality
specification for the faithful MCA prize lattice. -/
theorem exists_mcaPrizeLatticeSpec_of_lowerWitnesses
    (domain : ι ↪ F)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  classical
  rcases exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses domain w with
    ⟨τ, _hτ, hspec⟩
  exact ⟨τ, hspec⟩

omit [DecidableEq ι] [DecidableEq F] in
/-- Per-rate lower MCA witnesses expose the selected-threshold specification and lower lattice
brackets for the faithful MCA prize lattice. -/
theorem exists_mcaPrizeLatticeSpec_and_lower_brackets_of_lowerWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
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
  classical
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

/-- Per-rate lower MCA witnesses resolve the faithful MCA prize lattice and expose the
selected-threshold specification together with lower lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_lowerWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hwδ : ∀ j : Fin 4, (w j).δ = δ j) :
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
  rcases exists_mcaPrizeLatticeSpec_and_lower_brackets_of_lowerWitnesses
      domain δ hδ_le_one w hwδ with
    ⟨τ, hspec, hlower⟩
  exact ⟨τ, (mcaPrizeLatticeResolved_iff domain τ).mpr hspec, hspec, hlower⟩

/-- Per-rate lower MCA witnesses resolve the faithful MCA prize lattice and expose only lower
lattice brackets, dropping the selected-threshold specification payload. -/
theorem exists_mcaPrizeLatticeResolved_with_lower_brackets_of_lowerWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hwδ : ∀ j : Fin 4, (w j).δ = δ j) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j := by
  rcases exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_lowerWitnesses
      domain δ hδ_le_one w hwδ with
    ⟨τ, hτ, _hspec, hlower⟩
  exact ⟨τ, hτ, hlower⟩

omit [DecidableEq ι] [DecidableEq F] in
/-- Per-rate lower and upper MCA witnesses expose the selected-threshold specification and
two-sided lattice brackets for the faithful MCA prize lattice. -/
theorem exists_mcaPrizeLatticeSpec_and_brackets_of_lowerWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hwδ : ∀ j : Fin 4, (w j).δ = δ j)
    (whi : ∀ j : Fin 4,
      MCAUpperWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
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
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  classical
  rcases exists_mcaPrizeLatticeSpec_and_lower_brackets_of_lowerWitnesses
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

/-- Per-rate lower and upper MCA witnesses resolve the faithful MCA prize lattice and expose the
selected-threshold specification together with two-sided lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_lowerWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hwδ : ∀ j : Fin 4, (w j).δ = δ j)
    (whi : ∀ j : Fin 4,
      MCAUpperWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
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
  rcases exists_mcaPrizeLatticeSpec_and_brackets_of_lowerWitnesses
      domain δ hδ_le_one w hwδ whi hδhi with
    ⟨τ, hspec, hlower, hupper⟩
  exact ⟨τ, (mcaPrizeLatticeResolved_iff domain τ).mpr hspec, hspec, hlower, hupper⟩

/-- Per-rate lower and upper MCA witnesses resolve the faithful MCA prize lattice and expose only
two-sided lattice brackets, dropping the selected-threshold specification payload. -/
theorem exists_mcaPrizeLatticeResolved_with_brackets_of_lowerWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hwδ : ∀ j : Fin 4, (w j).δ = δ j)
    (whi : ∀ j : Fin 4,
      MCAUpperWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        (∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j) ∧
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_lowerWitnesses
      domain δ hδ_le_one w hwδ whi hδhi with
    ⟨τ, hτ, _hspec, hlower, hupper⟩
  exact ⟨τ, hτ, hlower, hupper⟩

set_option linter.unusedDecidableInType false in
/-- A single explicit prize-rate lower MCA witness gives concrete faithful-threshold
nonemptiness. -/
theorem mcaThresholdExists_prize_of_lowerWitness
    (domain : ι ↪ F) (j : Fin 4)
    (w : MCALowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    mcaThresholdExists C epsStar := by
  dsimp only
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  exact mcaThresholdExists_of_MCALowerWitness C epsStar w

/-- A single explicit prize-rate lower MCA witness gives the concrete faithful threshold and its
satisfy fact. -/
theorem mcaThreshold_spec_prize_of_lowerWitness
    (domain : ι ↪ F) (j : Fin 4)
    (w : MCALowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      mcaSatisfies C epsStar (mcaThreshold C epsStar hne) := by
  dsimp only
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let hne : mcaThresholdExists C epsStar :=
    mcaThresholdExists_of_MCALowerWitness C epsStar w
  exact ⟨hne, mcaThreshold_spec C epsStar hne⟩

set_option linter.unusedDecidableInType false in
/-- Explicit lower MCA witnesses at all four prize rates give concrete faithful-threshold
nonemptiness. -/
theorem mcaThresholdExists_prize_allRates_of_lowerWitnesses
    (domain : ι ↪ F)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      mcaThresholdExists C epsStar := by
  intro j
  exact mcaThresholdExists_prize_of_lowerWitness domain j (w j)

/-- Explicit lower MCA witnesses at all four prize rates give the concrete faithful thresholds and
their satisfy facts. -/
theorem mcaThreshold_spec_prize_allRates_of_lowerWitnesses
    (domain : ι ↪ F)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (mcaThreshold C epsStar hne) := by
  intro j
  exact mcaThreshold_spec_prize_of_lowerWitness domain j (w j)

/-- A single explicit prize-rate lower MCA witness gives the concrete faithful threshold, its
satisfy fact, and the lower lattice bracket at the witness radius. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_of_lowerWitness
    (domain : ι ↪ F) (j : Fin 4)
    (w : MCALowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
        latticeIndexOf (ι := ι) w.δ w.le_one ≤ mcaThreshold C epsStar hne := by
  dsimp only
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let hne : mcaThresholdExists C epsStar :=
    mcaThresholdExists_of_MCALowerWitness C epsStar w
  exact ⟨hne, mcaThreshold_spec C epsStar hne, MCALowerWitness_le_mcaThreshold C epsStar hne w⟩

/-- Low-output projection of `mcaThreshold_spec_and_lower_bracket_prize_of_lowerWitness`: it keeps
only the concrete lower lattice bracket at the witness radius. -/
theorem mcaThreshold_lower_bracket_prize_of_lowerWitness
    (domain : ι ↪ F) (j : Fin 4)
    (w : MCALowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      latticeIndexOf (ι := ι) w.δ w.le_one ≤ mcaThreshold C epsStar hne := by
  rcases mcaThreshold_spec_and_lower_bracket_prize_of_lowerWitness domain j w with
    ⟨hne, _hsat, hlower⟩
  exact ⟨hne, hlower⟩

/-- Explicit lower MCA witnesses at all four prize rates give the concrete faithful thresholds,
their satisfy facts, and lower lattice brackets at the witness radii. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_allRates_of_lowerWitnesses
    (domain : ι ↪ F)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
          latticeIndexOf (ι := ι) (w j).δ (w j).le_one ≤
            mcaThreshold C epsStar hne := by
  intro j
  exact mcaThreshold_spec_and_lower_bracket_prize_of_lowerWitness domain j (w j)

/-- Low-output projection of
`mcaThreshold_spec_and_lower_bracket_prize_allRates_of_lowerWitnesses`: it keeps only the concrete
lower lattice bracket at each prize-rate witness radius. -/
theorem mcaThreshold_lower_bracket_prize_allRates_of_lowerWitnesses
    (domain : ι ↪ F)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        latticeIndexOf (ι := ι) (w j).δ (w j).le_one ≤ mcaThreshold C epsStar hne := by
  intro j
  rcases mcaThreshold_spec_and_lower_bracket_prize_allRates_of_lowerWitnesses domain w j with
    ⟨hne, _hsat, hlower⟩
  exact ⟨hne, hlower⟩

/-- A single explicit lower MCA witness and explicit upper MCA witness give the concrete faithful
threshold, its satisfy fact, and two-sided lattice brackets at the witness radii. -/
theorem mcaThreshold_spec_and_bracket_prize_of_lowerWitness
    (domain : ι ↪ F) (j : Fin 4)
    (w : MCALowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar)
    (whi : MCAUpperWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar)
    (hδhi : whi.δ ≤ 1) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
        latticeIndexOf (ι := ι) w.δ w.le_one ≤ mcaThreshold C epsStar hne ∧
          mcaThreshold C epsStar hne < latticeIndexOf (ι := ι) whi.δ hδhi := by
  rcases mcaThreshold_spec_and_lower_bracket_prize_of_lowerWitness domain j w with
    ⟨hne, hsat, hlower⟩
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  have hupper : mcaThreshold C epsStar hne < latticeIndexOf (ι := ι) whi.δ hδhi :=
    mcaThreshold_lt_MCAUpperWitness C epsStar hne whi hδhi
  exact ⟨hne, hsat, hlower, hupper⟩

/-- Low-output projection of `mcaThreshold_spec_and_bracket_prize_of_lowerWitness`: it keeps only
the concrete two-sided lattice bracket at the lower and upper witness radii. -/
theorem mcaThreshold_bracket_prize_of_lowerWitness
    (domain : ι ↪ F) (j : Fin 4)
    (w : MCALowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar)
    (whi : MCAUpperWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar)
    (hδhi : whi.δ ≤ 1) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      latticeIndexOf (ι := ι) w.δ w.le_one ≤ mcaThreshold C epsStar hne ∧
        mcaThreshold C epsStar hne < latticeIndexOf (ι := ι) whi.δ hδhi := by
  rcases mcaThreshold_spec_and_bracket_prize_of_lowerWitness domain j w whi hδhi with
    ⟨hne, _hsat, hlower, hupper⟩
  exact ⟨hne, hlower, hupper⟩

/-- Explicit lower and upper MCA witnesses at all four prize rates give the concrete faithful
thresholds, their satisfy facts, and two-sided lattice brackets at the witness radii. -/
theorem mcaThreshold_spec_and_bracket_prize_allRates_of_lowerWitnesses
    (domain : ι ↪ F)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (whi : ∀ j : Fin 4,
      MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
          latticeIndexOf (ι := ι) (w j).δ (w j).le_one ≤
            mcaThreshold C epsStar hne ∧
            mcaThreshold C epsStar hne <
              latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  intro j
  exact mcaThreshold_spec_and_bracket_prize_of_lowerWitness domain j (w j) (whi j)
    (hδhi j)

/-- Low-output projection of
`mcaThreshold_spec_and_bracket_prize_allRates_of_lowerWitnesses`: it keeps only the concrete
two-sided lattice bracket at each lower and upper witness radius. -/
theorem mcaThreshold_bracket_prize_allRates_of_lowerWitnesses
    (domain : ι ↪ F)
    (w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (whi : ∀ j : Fin 4,
      MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      ∃ hne : mcaThresholdExists C epsStar,
        latticeIndexOf (ι := ι) (w j).δ (w j).le_one ≤ mcaThreshold C epsStar hne ∧
          mcaThreshold C epsStar hne <
            latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  intro j
  rcases mcaThreshold_spec_and_bracket_prize_allRates_of_lowerWitnesses
      domain w whi hδhi j with
    ⟨hne, _hsat, hlower, hupper⟩
  exact ⟨hne, hlower, hupper⟩

/-- The ignored-source MCA conjecture gives an existential faithful four-rate MCA prize
resolution together with the satisfy/maximality specification for the selected lattice
thresholds. The conjecture and all numeric side conditions remain explicit; this only packages the
existing existential aggregation with `mcaPrizeLatticeResolved_iff`. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) →
        (∀ j : Fin 4, (δ j : ℝ) <
          1 - (⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : ℝ) / Fintype.card ιC) →
        (∀ j : Fin 4, δ j ≤ 1) →
        (∀ j : Fin 4,
          ENNReal.ofReal
              (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC)
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ (δ j) c₁ c₂ c₃) ≤
            (epsStar : ENNReal)) →
        ∃ τ : Fin 4 → Fin (Fintype.card ιC + 1),
          mcaPrizeLatticeResolved domain τ ∧
            ∀ j : Fin 4,
              let C : Set (ιC → FC) :=
                ReedSolomon.code domain
                  ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
              ∃ _ : mcaThresholdExists C epsStar,
                mcaSatisfies C epsStar (τ j) ∧
                  ∀ i : Fin (Fintype.card ιC + 1),
                    mcaSatisfies C epsStar i → i ≤ τ j := by
  obtain ⟨c₁, c₂, c₃, hResolve⟩ :=
    exists_mcaPrizeLatticeResolved_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain δ hk hδ hδ1 hbound
  rcases hResolve domain δ hk hδ hδ1 hbound with ⟨τ, hτ⟩
  exact ⟨τ, hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

/-- Pointwise prize-rate consequences of the ignored-source MCA conjecture expose only the
selected-threshold satisfy/maximality specification. The conjecture remains an explicit
hypothesis, and all numeric side conditions are supplied separately for each prize rate. -/
theorem exists_mcaPrizeLatticeSpec_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) →
        (∀ j : Fin 4, (δ j : ℝ) <
          1 - (⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : ℝ) / Fintype.card ιC) →
        (∀ j : Fin 4, δ j ≤ 1) →
        (∀ j : Fin 4,
          ENNReal.ofReal
              (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC)
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ (δ j) c₁ c₂ c₃) ≤
            (epsStar : ENNReal)) →
        ∃ τ : Fin 4 → Fin (Fintype.card ιC + 1),
          ∀ j : Fin 4,
            let C : Set (ιC → FC) :=
              ReedSolomon.code domain
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
            ∃ _ : mcaThresholdExists C epsStar,
              mcaSatisfies C epsStar (τ j) ∧
                ∀ i : Fin (Fintype.card ιC + 1),
                  mcaSatisfies C epsStar i → i ≤ τ j := by
  obtain ⟨c₁, c₂, c₃, hSpec⟩ :=
    exists_mcaPrizeLatticeResolved_with_spec_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain δ hk hδ hδ1 hbound
  rcases hSpec domain δ hk hδ hδ1 hbound with ⟨τ, _hτ, hspec⟩
  exact ⟨τ, hspec⟩

/-- Single prize-rate consequence of the ignored-source MCA conjecture: the concrete faithful
threshold satisfies the MCA target and lies above the supplied lattice radius. The conjecture
remains explicit, and all numeric side conditions are supplied separately. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (j : Fin 4) (δ : ℝ≥0),
        let k : ℕ := ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC →
        (hδ_le_one : δ ≤ 1) →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (epsStar : ENNReal) →
        let C : Set (ιC → FC) := ReedSolomon.code domain k
        ∃ hne : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
            latticeIndexOf (ι := ιC) δ hδ_le_one ≤ mcaThreshold C epsStar hne := by
  classical
  obtain ⟨c₁, c₂, c₃, hLower⟩ :=
    GrandChallenges.exists_prize_mcaLowerWitness_of_ignored_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain j δ
  dsimp only
  intro hk hδ hδ_le_one hbound
  let k : ℕ := ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
  let C : Set (ιC → FC) := ReedSolomon.code domain k
  rcases hLower domain j δ hk hδ hδ_le_one hbound with ⟨w, hwδ⟩
  let hne : mcaThresholdExists C epsStar :=
    mcaThresholdExists_of_MCALowerWitness C epsStar w
  have hidx :
      latticeIndexOf (ι := ιC) w.δ w.le_one =
        latticeIndexOf (ι := ιC) δ hδ_le_one := by
    apply Fin.ext
    simp [latticeIndexOf_val, hwδ]
  have hlower : latticeIndexOf (ι := ιC) δ hδ_le_one ≤ mcaThreshold C epsStar hne := by
    rw [← hidx]
    exact MCALowerWitness_le_mcaThreshold C epsStar hne w
  exact ⟨hne, mcaThreshold_spec C epsStar hne, hlower⟩

/-- Low-output projection of
`mcaThreshold_spec_and_lower_bracket_prize_of_ignoredSource_mcaConjecture`: it keeps only the
concrete lower lattice bracket for a single prize-rate threshold. -/
theorem mcaThreshold_lower_bracket_prize_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (j : Fin 4) (δ : ℝ≥0),
        let k : ℕ := ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC →
        (hδ_le_one : δ ≤ 1) →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (epsStar : ENNReal) →
        let C : Set (ιC → FC) := ReedSolomon.code domain k
        ∃ hne : mcaThresholdExists C epsStar,
          latticeIndexOf (ι := ιC) δ hδ_le_one ≤ mcaThreshold C epsStar hne := by
  obtain ⟨c₁, c₂, c₃, hsingle⟩ :=
    mcaThreshold_spec_and_lower_bracket_prize_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain j δ
  dsimp only
  intro hk hδ hδ_le_one hbound
  rcases hsingle domain j δ hk hδ hδ_le_one hbound with
    ⟨hne, _hsat, hlower⟩
  exact ⟨hne, hlower⟩

/-- All-rate prize consequence of the ignored-source MCA conjecture: every concrete faithful
threshold satisfies the MCA target and lies above its supplied lattice radius. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_allRates_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) →
        (∀ j : Fin 4, (δ j : ℝ) <
          1 - (⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : ℝ) / Fintype.card ιC) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        (∀ j : Fin 4,
          ENNReal.ofReal
              (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC)
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ (δ j) c₁ c₂ c₃) ≤
            (epsStar : ENNReal)) →
        ∀ j : Fin 4,
          let C : Set (ιC → FC) :=
            ReedSolomon.code domain
              ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
          ∃ hne : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
              latticeIndexOf (ι := ιC) (δ j) (hδ_le_one j) ≤
                mcaThreshold C epsStar hne := by
  obtain ⟨c₁, c₂, c₃, hsingle⟩ :=
    mcaThreshold_spec_and_lower_bracket_prize_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain δ hk hδ hδ_le_one hbound j
  exact hsingle domain j (δ j) (hk j) (hδ j) (hδ_le_one j) (hbound j)

/-- Low-output projection of
`mcaThreshold_spec_and_lower_bracket_prize_allRates_of_ignoredSource_mcaConjecture`: it keeps
only the concrete lower lattice bracket at each prize-rate threshold. -/
theorem mcaThreshold_lower_bracket_prize_allRates_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) →
        (∀ j : Fin 4, (δ j : ℝ) <
          1 - (⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : ℝ) / Fintype.card ιC) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        (∀ j : Fin 4,
          ENNReal.ofReal
              (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC)
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ (δ j) c₁ c₂ c₃) ≤
            (epsStar : ENNReal)) →
        ∀ j : Fin 4,
          let C : Set (ιC → FC) :=
            ReedSolomon.code domain
              ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
          ∃ hne : mcaThresholdExists C epsStar,
            latticeIndexOf (ι := ιC) (δ j) (hδ_le_one j) ≤
              mcaThreshold C epsStar hne := by
  obtain ⟨c₁, c₂, c₃, hall⟩ :=
    mcaThreshold_spec_and_lower_bracket_prize_allRates_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain δ hk hδ hδ_le_one hbound j
  rcases hall domain δ hk hδ hδ_le_one hbound j with
    ⟨hne, _hsat, hlower⟩
  exact ⟨hne, hlower⟩

/-- Single prize-rate consequence of the ignored-source MCA conjecture, plus an explicit upper
MCA witness: the concrete faithful threshold satisfies the MCA target and lies between the lower
and upper lattice radii. -/
theorem mcaThreshold_spec_and_bracket_prize_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (j : Fin 4) (δ : ℝ≥0),
        let k : ℕ := ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC →
        (hδ_le_one : δ ≤ 1) →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (epsStar : ENNReal) →
        (whi : MCAUpperWitness (ReedSolomon.code domain k : Set (ιC → FC)) epsStar) →
        (hδhi : whi.δ ≤ 1) →
        let C : Set (ιC → FC) := ReedSolomon.code domain k
        ∃ hne : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
            latticeIndexOf (ι := ιC) δ hδ_le_one ≤ mcaThreshold C epsStar hne ∧
              mcaThreshold C epsStar hne < latticeIndexOf (ι := ιC) whi.δ hδhi := by
  obtain ⟨c₁, c₂, c₃, hsingle⟩ :=
    mcaThreshold_spec_and_lower_bracket_prize_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain j δ
  dsimp only
  intro hk hδ hδ_le_one hbound whi hδhi
  let k : ℕ := ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
  let C : Set (ιC → FC) := ReedSolomon.code domain k
  rcases hsingle domain j δ hk hδ hδ_le_one hbound with
    ⟨hne, hsat, hlower⟩
  have hupper : mcaThreshold C epsStar hne < latticeIndexOf (ι := ιC) whi.δ hδhi :=
    mcaThreshold_lt_MCAUpperWitness C epsStar hne whi hδhi
  exact ⟨hne, hsat, hlower, hupper⟩

/-- Low-output projection of
`mcaThreshold_spec_and_bracket_prize_of_ignoredSource_mcaConjecture`: it keeps only the concrete
two-sided lattice bracket for a single prize-rate threshold. -/
theorem mcaThreshold_bracket_prize_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (j : Fin 4) (δ : ℝ≥0),
        let k : ℕ := ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC →
        (hδ_le_one : δ ≤ 1) →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (epsStar : ENNReal) →
        (whi : MCAUpperWitness (ReedSolomon.code domain k : Set (ιC → FC)) epsStar) →
        (hδhi : whi.δ ≤ 1) →
        let C : Set (ιC → FC) := ReedSolomon.code domain k
        ∃ hne : mcaThresholdExists C epsStar,
          latticeIndexOf (ι := ιC) δ hδ_le_one ≤ mcaThreshold C epsStar hne ∧
            mcaThreshold C epsStar hne < latticeIndexOf (ι := ιC) whi.δ hδhi := by
  obtain ⟨c₁, c₂, c₃, hsingle⟩ :=
    mcaThreshold_spec_and_bracket_prize_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain j δ
  dsimp only
  intro hk hδ hδ_le_one hbound whi hδhi
  rcases hsingle domain j δ hk hδ hδ_le_one hbound whi hδhi with
    ⟨hne, _hsat, hlower, hupper⟩
  exact ⟨hne, hlower, hupper⟩

/-- All-rate prize consequence of the ignored-source MCA conjecture, plus explicit upper MCA
witnesses: every concrete faithful threshold satisfies the MCA target and lies between the lower
and upper lattice radii. -/
theorem mcaThreshold_spec_and_bracket_prize_allRates_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) →
        (∀ j : Fin 4, (δ j : ℝ) <
          1 - (⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : ℝ) / Fintype.card ιC) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        (∀ j : Fin 4,
          ENNReal.ofReal
              (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC)
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ (δ j) c₁ c₂ c₃) ≤
            (epsStar : ENNReal)) →
        (whi : ∀ j : Fin 4,
          MCAUpperWitness
            (ReedSolomon.code domain
              ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : Set (ιC → FC))
            epsStar) →
        (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) →
        ∀ j : Fin 4,
          let C : Set (ιC → FC) :=
            ReedSolomon.code domain
              ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
          ∃ hne : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
              latticeIndexOf (ι := ιC) (δ j) (hδ_le_one j) ≤
                mcaThreshold C epsStar hne ∧
                mcaThreshold C epsStar hne <
                  latticeIndexOf (ι := ιC) (whi j).δ (hδhi j) := by
  obtain ⟨c₁, c₂, c₃, hsingle⟩ :=
    mcaThreshold_spec_and_bracket_prize_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain δ hk hδ hδ_le_one hbound whi hδhi j
  exact hsingle domain j (δ j) (hk j) (hδ j) (hδ_le_one j) (hbound j)
    (whi j) (hδhi j)

/-- Low-output projection of
`mcaThreshold_spec_and_bracket_prize_allRates_of_ignoredSource_mcaConjecture`: it keeps only the
concrete two-sided lattice bracket at each prize-rate threshold. -/
theorem mcaThreshold_bracket_prize_allRates_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) →
        (∀ j : Fin 4, (δ j : ℝ) <
          1 - (⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : ℝ) / Fintype.card ιC) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        (∀ j : Fin 4,
          ENNReal.ofReal
              (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC)
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ (δ j) c₁ c₂ c₃) ≤
            (epsStar : ENNReal)) →
        (whi : ∀ j : Fin 4,
          MCAUpperWitness
            (ReedSolomon.code domain
              ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : Set (ιC → FC))
            epsStar) →
        (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) →
        ∀ j : Fin 4,
          let C : Set (ιC → FC) :=
            ReedSolomon.code domain
              ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
          ∃ hne : mcaThresholdExists C epsStar,
            latticeIndexOf (ι := ιC) (δ j) (hδ_le_one j) ≤
              mcaThreshold C epsStar hne ∧
              mcaThreshold C epsStar hne <
                latticeIndexOf (ι := ιC) (whi j).δ (hδhi j) := by
  obtain ⟨c₁, c₂, c₃, hall⟩ :=
    mcaThreshold_spec_and_bracket_prize_allRates_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain δ hk hδ hδ_le_one hbound whi hδhi j
  rcases hall domain δ hk hδ hδ_le_one hbound whi hδhi j with
    ⟨hne, _hsat, hlower, hupper⟩
  exact ⟨hne, hlower, hupper⟩

/-- Pointwise prize-rate consequences of the ignored-source MCA conjecture expose the
selected-threshold specification together with lower lattice brackets. The conjecture remains an
explicit hypothesis, and all numeric side conditions are supplied separately for each prize rate. -/
theorem exists_mcaPrizeLatticeSpec_and_lower_brackets_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) →
        (∀ j : Fin 4, (δ j : ℝ) <
          1 - (⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : ℝ) / Fintype.card ιC) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        (∀ j : Fin 4,
          ENNReal.ofReal
              (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC)
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ (δ j) c₁ c₂ c₃) ≤
            (epsStar : ENNReal)) →
        ∃ τ : Fin 4 → Fin (Fintype.card ιC + 1),
          (∀ j : Fin 4,
            let C : Set (ιC → FC) :=
              ReedSolomon.code domain
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
            ∃ _ : mcaThresholdExists C epsStar,
              mcaSatisfies C epsStar (τ j) ∧
                ∀ i : Fin (Fintype.card ιC + 1),
                  mcaSatisfies C epsStar i → i ≤ τ j) ∧
            ∀ j : Fin 4,
              latticeIndexOf (ι := ιC) (δ j) (hδ_le_one j) ≤ τ j := by
  obtain ⟨c₁, c₂, c₃, hLower⟩ :=
    GrandChallenges.exists_prize_mcaLowerWitnesses_allRates_of_ignored_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain δ hk hδ hδ_le_one hbound
  have hw : ∀ j : Fin 4,
      ∃ w : MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : Set (ιC → FC))
        epsStar,
        w.δ = δ j :=
    hLower domain δ hk hδ hδ_le_one hbound
  let w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : Set (ιC → FC))
        epsStar :=
    fun j => Classical.choose (hw j)
  exact exists_mcaPrizeLatticeSpec_and_lower_brackets_of_lowerWitnesses
    domain δ hδ_le_one w fun j => Classical.choose_spec (hw j)

/-- Pointwise prize-rate consequences of the ignored-source MCA conjecture resolve the faithful
MCA prize lattice and expose the selected-threshold specification together with lower lattice
brackets. The conjecture remains an explicit hypothesis, and all numeric side conditions are
supplied separately for each prize rate. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) →
        (∀ j : Fin 4, (δ j : ℝ) <
          1 - (⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : ℝ) / Fintype.card ιC) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        (∀ j : Fin 4,
          ENNReal.ofReal
              (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC)
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ (δ j) c₁ c₂ c₃) ≤
            (epsStar : ENNReal)) →
        ∃ τ : Fin 4 → Fin (Fintype.card ιC + 1),
          mcaPrizeLatticeResolved domain τ ∧
            (∀ j : Fin 4,
              let C : Set (ιC → FC) :=
                ReedSolomon.code domain
                  ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
              ∃ _ : mcaThresholdExists C epsStar,
                mcaSatisfies C epsStar (τ j) ∧
                  ∀ i : Fin (Fintype.card ιC + 1),
                    mcaSatisfies C epsStar i → i ≤ τ j) ∧
              ∀ j : Fin 4,
                latticeIndexOf (ι := ιC) (δ j) (hδ_le_one j) ≤ τ j := by
  obtain ⟨c₁, c₂, c₃, hLower⟩ :=
    exists_mcaPrizeLatticeSpec_and_lower_brackets_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain δ hk hδ hδ_le_one hbound
  rcases hLower domain δ hk hδ hδ_le_one hbound with ⟨τ, hspec, hlower⟩
  exact ⟨τ, (mcaPrizeLatticeResolved_iff domain τ).mpr hspec, hspec, hlower⟩

/-- Pointwise prize-rate consequences of the ignored-source MCA conjecture resolve the faithful
MCA prize lattice and expose only lower lattice brackets, dropping the selected-threshold
specification payload. -/
theorem exists_mcaPrizeLatticeResolved_with_lower_brackets_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) →
        (∀ j : Fin 4, (δ j : ℝ) <
          1 - (⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : ℝ) / Fintype.card ιC) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        (∀ j : Fin 4,
          ENNReal.ofReal
              (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC)
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ (δ j) c₁ c₂ c₃) ≤
            (epsStar : ENNReal)) →
        ∃ τ : Fin 4 → Fin (Fintype.card ιC + 1),
          mcaPrizeLatticeResolved domain τ ∧
            ∀ j : Fin 4,
              latticeIndexOf (ι := ιC) (δ j) (hδ_le_one j) ≤ τ j := by
  obtain ⟨c₁, c₂, c₃, hLower⟩ :=
    exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain δ hk hδ hδ_le_one hbound
  rcases hLower domain δ hk hδ hδ_le_one hbound with
    ⟨τ, hτ, _hspec, hlower⟩
  exact ⟨τ, hτ, hlower⟩

/-- Pointwise prize-rate consequences of the ignored-source MCA conjecture, plus explicit upper
MCA witnesses, expose the selected-threshold specification together with two-sided lattice
brackets. The conjecture remains an explicit hypothesis, and all numeric side conditions are
supplied separately for each prize rate. -/
theorem exists_mcaPrizeLatticeSpec_and_brackets_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) →
        (∀ j : Fin 4, (δ j : ℝ) <
          1 - (⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : ℝ) / Fintype.card ιC) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        (∀ j : Fin 4,
          ENNReal.ofReal
              (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC)
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ (δ j) c₁ c₂ c₃) ≤
            (epsStar : ENNReal)) →
        (whi : ∀ j : Fin 4,
          MCAUpperWitness
            (ReedSolomon.code domain
              ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : Set (ιC → FC))
            epsStar) →
        (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) →
        ∃ τ : Fin 4 → Fin (Fintype.card ιC + 1),
          (∀ j : Fin 4,
            let C : Set (ιC → FC) :=
              ReedSolomon.code domain
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
            ∃ _ : mcaThresholdExists C epsStar,
              mcaSatisfies C epsStar (τ j) ∧
                ∀ i : Fin (Fintype.card ιC + 1),
                  mcaSatisfies C epsStar i → i ≤ τ j) ∧
            (∀ j : Fin 4,
              latticeIndexOf (ι := ιC) (δ j) (hδ_le_one j) ≤ τ j) ∧
              ∀ j : Fin 4, τ j < latticeIndexOf (ι := ιC) (whi j).δ (hδhi j) := by
  obtain ⟨c₁, c₂, c₃, hLower⟩ :=
    GrandChallenges.exists_prize_mcaLowerWitnesses_allRates_of_ignored_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain δ hk hδ hδ_le_one hbound whi hδhi
  have hw : ∀ j : Fin 4,
      ∃ w : MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : Set (ιC → FC))
        epsStar,
        w.δ = δ j :=
    hLower domain δ hk hδ hδ_le_one hbound
  let w : ∀ j : Fin 4,
      MCALowerWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : Set (ιC → FC))
        epsStar :=
    fun j => Classical.choose (hw j)
  exact exists_mcaPrizeLatticeSpec_and_brackets_of_lowerWitnesses
    domain δ hδ_le_one w (fun j => Classical.choose_spec (hw j)) whi hδhi

/-- Pointwise prize-rate consequences of the ignored-source MCA conjecture, plus explicit upper
MCA witnesses, resolve the faithful MCA prize lattice and expose the selected-threshold
specification together with two-sided lattice brackets. The conjecture remains an explicit
hypothesis, and all numeric side conditions are supplied separately for each prize rate. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) →
        (∀ j : Fin 4, (δ j : ℝ) <
          1 - (⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : ℝ) / Fintype.card ιC) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        (∀ j : Fin 4,
          ENNReal.ofReal
              (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC)
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ (δ j) c₁ c₂ c₃) ≤
            (epsStar : ENNReal)) →
        (whi : ∀ j : Fin 4,
          MCAUpperWitness
            (ReedSolomon.code domain
              ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : Set (ιC → FC))
            epsStar) →
        (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) →
        ∃ τ : Fin 4 → Fin (Fintype.card ιC + 1),
          mcaPrizeLatticeResolved domain τ ∧
            (∀ j : Fin 4,
              let C : Set (ιC → FC) :=
                ReedSolomon.code domain
                  ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
              ∃ _ : mcaThresholdExists C epsStar,
                mcaSatisfies C epsStar (τ j) ∧
                  ∀ i : Fin (Fintype.card ιC + 1),
                    mcaSatisfies C epsStar i → i ≤ τ j) ∧
              (∀ j : Fin 4,
                latticeIndexOf (ι := ιC) (δ j) (hδ_le_one j) ≤ τ j) ∧
                ∀ j : Fin 4, τ j < latticeIndexOf (ι := ιC) (whi j).δ (hδhi j) := by
  obtain ⟨c₁, c₂, c₃, hBracket⟩ :=
    exists_mcaPrizeLatticeSpec_and_brackets_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain δ hk hδ hδ_le_one hbound whi hδhi
  rcases hBracket domain δ hk hδ hδ_le_one hbound whi hδhi with
    ⟨τ, hspec, hlower, hupper⟩
  exact ⟨τ, (mcaPrizeLatticeResolved_iff domain τ).mpr hspec, hspec, hlower, hupper⟩

/-- Pointwise prize-rate consequences of the ignored-source MCA conjecture, plus explicit upper
MCA witnesses, resolve the faithful MCA prize lattice and expose only two-sided lattice brackets,
dropping the selected-threshold specification payload. -/
theorem exists_mcaPrizeLatticeResolved_with_brackets_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) →
        (∀ j : Fin 4, (δ j : ℝ) <
          1 - (⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : ℝ) / Fintype.card ιC) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        (∀ j : Fin 4,
          ENNReal.ofReal
              (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC)
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ (δ j) c₁ c₂ c₃) ≤
            (epsStar : ENNReal)) →
        (whi : ∀ j : Fin 4,
          MCAUpperWitness
            (ReedSolomon.code domain
              ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : Set (ιC → FC))
            epsStar) →
        (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) →
        ∃ τ : Fin 4 → Fin (Fintype.card ιC + 1),
          mcaPrizeLatticeResolved domain τ ∧
            (∀ j : Fin 4,
              latticeIndexOf (ι := ιC) (δ j) (hδ_le_one j) ≤ τ j) ∧
              ∀ j : Fin 4, τ j < latticeIndexOf (ι := ιC) (whi j).δ (hδhi j) := by
  obtain ⟨c₁, c₂, c₃, hBracket⟩ :=
    exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain δ hk hδ hδ_le_one hbound whi hδhi
  rcases hBracket domain δ hk hδ hδ_le_one hbound whi hδhi with
    ⟨τ, hτ, _hspec, hlower, hupper⟩
  exact ⟨τ, hτ, hlower, hupper⟩

end PrizeSpec

set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved.thresholdExists
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved.satisfies
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved.maximal
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_top_of_radiusOne_bounds
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_top_of_choose_bounds
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeSpec_top_of_radiusOne_bounds
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeSpec_top_of_choose_bounds
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_eq_top_prize_allRates_of_radiusOne_bounds
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_eq_top_prize_allRates_of_choose_bounds
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeSpec_and_lower_brackets_top_of_radiusOne_bounds
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeSpec_and_lower_brackets_top_of_choose_bounds
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_lower_brackets_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_lower_brackets_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_brackets_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_brackets_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_prize_of_lowerWitness
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_prize_of_lowerWitness
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_prize_allRates_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_prize_allRates_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_lower_bracket_prize_of_lowerWitness
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lower_bracket_prize_of_lowerWitness
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_lower_bracket_prize_allRates_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lower_bracket_prize_allRates_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_bracket_prize_of_lowerWitness
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_bracket_prize_of_lowerWitness
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_bracket_prize_allRates_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_bracket_prize_allRates_of_lowerWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_lower_bracket_prize_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lower_bracket_prize_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_lower_bracket_prize_allRates_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_lower_bracket_prize_allRates_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_bracket_prize_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_bracket_prize_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_bracket_prize_allRates_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_bracket_prize_allRates_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_lower_brackets_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_lower_brackets_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_brackets_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_brackets_of_ignoredSource_mcaConjecture
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_ignoredSource_mcaConjecture

end GrandChallengesLattice

end ProximityGap
