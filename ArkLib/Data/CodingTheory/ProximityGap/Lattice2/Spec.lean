/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Lattice2.ListThreshold

/-!
# Faithful §1 Grand-Challenge lattice thresholds — prize-resolution targets

The faithful prize-resolution predicates `mcaPrizeLatticeResolved` /
`listPrizeLatticeResolved`, their four-rate brackets, the `OrdinaryRSCapacityAtPrizeRates`
frontier and the concrete numeric-certificate brackets. Part 4 of the
`GrandChallengesLattice` split; see the `GrandChallengesLattice.lean` umbrella.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal ProbabilityTheory BigOperators
open Code

namespace GrandChallengesLattice

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open GrandChallenges
open ListDecodable

/-! ## Faithful prize-resolution targets

The collapse-broken `GrandChallenges.mcaPrize` / `GrandChallenges.listDecodingPrize` predicates
ask only for existence of real thresholds.  The lattice formulation exposes the actual finite
quantities the paper asks to determine: one lattice index for each prize rate.  The predicates
below let a downstream proof state "these are the four thresholds" and immediately unfold that
claim to the verified satisfy/maximality characterization. -/

/-- A proposed solution of the MCA prize lattice problem: for every prize rate, the faithful
MCA lattice threshold is the supplied index `τ j`. -/
def mcaPrizeLatticeResolved (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1)) : Prop :=
  ∀ j : Fin 4,
    ∃ hne : mcaThresholdExists
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar,
      mcaThreshold
          (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))
          epsStar hne = τ j

/-- The faithful MCA prize-resolution predicate is exactly the per-rate statement that the
proposed lattice index satisfies the MCA bound and is maximal among satisfying lattice points. -/
theorem mcaPrizeLatticeResolved_iff (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1)) :
    mcaPrizeLatticeResolved domain τ ↔
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  constructor
  · intro h j
    rcases h j with ⟨hne, heq⟩
    refine ⟨hne, ?_, ?_⟩
    · simpa [heq] using mcaThreshold_spec
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar hne
    · intro i hi
      simpa [heq] using le_mcaThreshold
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar hne hi
  · intro h j
    rcases h j with ⟨hne, hsat, hmax⟩
    refine ⟨hne, ?_⟩
    exact (mcaThreshold_unique
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar hne (τ j) hsat hmax).symm

/-- If radius one already satisfies the MCA budget, then the faithful MCA lattice threshold is
the top lattice point.  This is the positive endpoint counterpart to the radius-one
obstruction lemmas: when the top point is good, maximality forces it to be the threshold. -/
theorem mcaThreshold_eq_top_of_epsMCA_one_le
    (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hone : epsMCA (F := F) (A := F) C 1 ≤ (ε_star : ENNReal)) :
    let top : Fin (Fintype.card ι + 1) := ⟨Fintype.card ι, Nat.lt_succ_self _⟩
    let hne : mcaThresholdExists C ε_star := ⟨top, by
      unfold mcaSatisfies
      have h1 : mcaLatticePoint (Fintype.card ι) top = 1 := by
        unfold mcaLatticePoint
        exact div_self (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')
      rw [h1]
      exact hone⟩
    mcaThreshold C ε_star hne = top := by
  classical
  let top : Fin (Fintype.card ι + 1) := ⟨Fintype.card ι, Nat.lt_succ_self _⟩
  have h1 : mcaLatticePoint (Fintype.card ι) top = 1 := by
    unfold mcaLatticePoint
    exact div_self (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')
  let hne : mcaThresholdExists C ε_star := ⟨top, by
    unfold mcaSatisfies
    rw [h1]
    exact hone⟩
  have hsat : mcaSatisfies C ε_star top := by
    unfold mcaSatisfies
    rw [h1]
    exact hone
  have hmax : ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C ε_star i → i ≤ top := by
    intro i _hi
    rw [Fin.le_iff_val_le_val]
    exact Nat.lt_succ_iff.mp i.isLt
  exact (mcaThreshold_unique C ε_star hne top hsat hmax).symm

/-- The full/top linear code makes the faithful MCA lattice threshold exist for every target
threshold.  This is the lattice endpoint form of `epsMCA_top_eq_zero`. -/
theorem mcaThresholdExists_topCode (ε_star : ℝ≥0) :
    mcaThresholdExists (((⊤ : LinearCode ι F) : Set (ι → F))) ε_star := by
  let top : Fin (Fintype.card ι + 1) := ⟨Fintype.card ι, Nat.lt_succ_self _⟩
  refine ⟨top, ?_⟩
  unfold mcaSatisfies
  rw [epsMCA_top_eq_zero]
  exact zero_le _

/-- The faithful MCA lattice threshold of the full/top linear code is the top lattice index. -/
theorem mcaThreshold_topCode_eq_top (ε_star : ℝ≥0) :
    mcaThreshold (((⊤ : LinearCode ι F) : Set (ι → F))) ε_star
        (mcaThresholdExists_topCode (ι := ι) (F := F) ε_star) =
      ⟨Fintype.card ι, Nat.lt_succ_self _⟩ := by
  let top : Fin (Fintype.card ι + 1) := ⟨Fintype.card ι, Nat.lt_succ_self _⟩
  change mcaThreshold (((⊤ : LinearCode ι F) : Set (ι → F))) ε_star
        (mcaThresholdExists_topCode (ι := ι) (F := F) ε_star) = top
  have hsat : mcaSatisfies (((⊤ : LinearCode ι F) : Set (ι → F))) ε_star top := by
    unfold mcaSatisfies
    rw [epsMCA_top_eq_zero]
    exact zero_le _
  have hmax : ∀ i : Fin (Fintype.card ι + 1),
      mcaSatisfies (((⊤ : LinearCode ι F) : Set (ι → F))) ε_star i → i ≤ top := by
    intro i _hi
    rw [Fin.le_iff_val_le_val]
    exact Nat.lt_succ_iff.mp i.isLt
  exact (mcaThreshold_unique (((⊤ : LinearCode ι F) : Set (ι → F))) ε_star
    (mcaThresholdExists_topCode (ι := ι) (F := F) ε_star) top hsat hmax).symm

/-- Endpoint upper bounds resolve the faithful MCA lattice prize with threshold `1` at every
prize rate. -/
theorem mcaPrizeLatticeResolved_top_of_radiusOne_bounds
    (domain : ι ↪ F)
    (hbound : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) 1
        ≤ (epsStar : ENNReal)) :
    mcaPrizeLatticeResolved domain
      (fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩) := by
  intro j
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let top : Fin (Fintype.card ι + 1) := ⟨Fintype.card ι, Nat.lt_succ_self _⟩
  let hne : mcaThresholdExists C epsStar := ⟨top, by
    unfold mcaSatisfies
    simpa [C, top] using hbound j⟩
  refine ⟨hne, ?_⟩
  simpa [C, top, hne] using
    mcaThreshold_eq_top_of_epsMCA_one_le (C := C) (ε_star := epsStar) (hbound j)

/-- The radius-one counting upper bound gives exact top faithful MCA thresholds whenever
`C(n,k_j+1)/q ≤ epsStar` at every prize rate. -/
theorem mcaPrizeLatticeResolved_top_of_choose_bounds
    (domain : ι ↪ F)
    (hbound : ∀ j : Fin 4,
      (Nat.choose (Fintype.card ι)
          (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ENNReal)
        / (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal)) :
    mcaPrizeLatticeResolved domain
      (fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩) := by
  apply mcaPrizeLatticeResolved_top_of_radiusOne_bounds
  intro j
  exact le_trans
    (epsMCA_one_le_choose_div domain
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
    (hbound j)

/-- Existentially resolving the faithful MCA lattice prize is equivalent to threshold
nonemptiness at all four prize rates.  Once every rate has at least one satisfying lattice point,
the finite threshold function itself supplies the four proposed indices. -/
theorem exists_mcaPrizeLatticeResolved_iff (domain : ι ↪ F) :
    (∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ) ↔
      ∀ j : Fin 4,
        mcaThresholdExists
          (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))
          epsStar := by
  constructor
  · rintro ⟨τ, hτ⟩ j
    exact (hτ j).choose
  · intro h
    refine ⟨fun j =>
      mcaThreshold
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
          Set (ι → F))
        epsStar (h j), ?_⟩
    intro j
    exact ⟨h j, rfl⟩

/-- Per-rate lower MCA witnesses resolve the faithful MCA lattice prize existentially.  This is
the four-rate aggregation form used by downstream Johnson/GS/CA upper-bound pipelines. -/
theorem exists_mcaPrizeLatticeResolved_of_lowerWitnesses
    (domain : ι ↪ F)
    (w : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ :=
  (exists_mcaPrizeLatticeResolved_iff domain).mpr fun j =>
    mcaThresholdExists_of_MCALowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar (w j)

/-- Pointwise prize-rate consequences of the ignored-source MCA conjecture resolve the faithful
MCA lattice prize existentially.  The conjecture remains an explicit hypothesis, and all numeric
side conditions are supplied separately for each prize rate. -/
theorem exists_mcaPrizeLatticeResolved_of_ignoredSource_mcaConjecture (h : mcaConjecture) :
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
        ∃ τ : Fin 4 → Fin (Fintype.card ιC + 1), mcaPrizeLatticeResolved domain τ := by
  obtain ⟨c₁, c₂, c₃, hExists⟩ :=
    mcaThresholdExists_prize_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain δ hk hδ hδ1 hbound
  exact (exists_mcaPrizeLatticeResolved_iff domain).mpr fun j =>
    hExists (domain := domain) (j := j) (δ := δ j)
      (hk j) (hδ j) (hδ1 j) (hbound j)

#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_of_ignoredSource_mcaConjecture

/-- Per-rate lower and upper MCA witnesses bracket all four faithful MCA prize thresholds. -/
theorem mcaPrizeLattice_bracketed_of_witnesses
    (domain : ι ↪ F)
    (wlo : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      let hne := mcaThresholdExists_of_MCALowerWitness C epsStar (wlo j)
      latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one ≤
          mcaThreshold C epsStar hne ∧
        mcaThreshold C epsStar hne <
          latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := fun j =>
  mcaThresholdLattice_bracketed_of_witnesses
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    epsStar (wlo j) (whi j) (hδhi j)

/-- Per-rate lower MCA witnesses and per-rate second-moment endpoint certificates bracket all
four faithful MCA prize thresholds below the top lattice point.

This is the four-rate faithful-lattice counterpart of
`not_mcaPrize_of_second_moment`: instead of merely refuting the collapsed formal predicate,
it records that radius `1` is already above the MCA budget, so any existing faithful
threshold lies strictly below the top lattice point. -/
theorem mcaPrizeLattice_lt_one_of_lowerWitnesses_and_secondMoment
    (domain : ι ↪ F)
    (wlo : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hk : ∀ j : Fin 4,
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1 ≤ Fintype.card ι)
    (M' : Fin 4 → ℕ)
    (hM : ∀ j : Fin 4,
      M' j ≤ Nat.choose (Fintype.card ι)
        (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1))
    (hle : ∀ j : Fin 4, M' j * M' j ≤ M' j * Fintype.card F)
    (hnum : ∀ j : Fin 4,
      Fintype.card F * Fintype.card F <
        2 ^ (128 : ℕ) *
          (M' j * Fintype.card F - M' j * M' j)) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      let hne := mcaThresholdExists_of_MCALowerWitness C epsStar (wlo j)
      latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one ≤
          mcaThreshold C epsStar hne ∧
        mcaThreshold C epsStar hne <
          latticeIndexOf (ι := ι) (1 : ℝ≥0) le_rfl := fun j =>
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let hne := mcaThresholdExists_of_MCALowerWitness C epsStar (wlo j)
  ⟨MCALowerWitness_le_mcaThreshold C epsStar hne (wlo j),
    mcaThreshold_lt_one_of_secondMoment domain
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (M' j) hne
      (hk j) (hM j) (hle j) (hnum j)⟩

/-- Adjacent per-rate MCA witnesses resolve the faithful MCA lattice prize with the lower
witness indices as the four exact thresholds. -/
theorem mcaPrizeLatticeResolved_of_adjacent_witnesses
    (domain : ι ↪ F)
    (wlo : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one) := by
  intro j
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  refine ⟨mcaThresholdExists_of_MCALowerWitness C epsStar (wlo j), ?_⟩
  exact mcaThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    C epsStar (wlo j) (whi j) (hδhi j) (hadj j)

/-- Packaged four-rate frontier for an exact faithful MCA lattice-prize resolution.

The fields are the reusable input surface of #70: a chosen lower witness, upper witness,
upper-radius lattice proof, and adjacent-index proof for each prize rate.  Proving or selecting
those witnesses is still the numeric/content work; this structure only names the assembled
frontier consumed by `mcaPrizeLatticeResolved_of_adjacent_witnesses`. -/
structure MCAPrizeAdjacentWitnessFrontier (domain : ι ↪ F) where
  lower : ∀ j : Fin 4,
    GrandChallenges.MCALowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar
  upper : ∀ j : Fin 4,
    GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar
  upper_le_one : ∀ j : Fin 4, (upper j).δ ≤ 1
  adjacent : ∀ j : Fin 4,
    (latticeIndexOf (ι := ι) (upper j).δ (upper_le_one j)).val =
      (latticeIndexOf (ι := ι) (lower j).δ (lower j).le_one).val + 1

/-- Reassemble the faithful four-rate MCA lattice-prize resolution from the packaged
adjacent-witness frontier. -/
theorem mcaPrizeLatticeResolved_of_adjacent_frontier
    (domain : ι ↪ F)
    (frontier : MCAPrizeAdjacentWitnessFrontier (F := F) domain) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (frontier.lower j).δ (frontier.lower j).le_one) :=
  mcaPrizeLatticeResolved_of_adjacent_witnesses domain
    frontier.lower frontier.upper frontier.upper_le_one frontier.adjacent

#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_of_adjacent_witnesses
#print axioms ProximityGap.GrandChallengesLattice.MCAPrizeAdjacentWitnessFrontier
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_of_adjacent_frontier

/-- Exact values for the canonical `Finset ℕ` MCA threshold resolve the four-rate faithful
MCA prize predicate in the `Fin (n+1)` lattice representation. -/
theorem mcaPrizeLatticeResolved_of_canonical_mcaLatticeThreshold_eq
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (hne : ∀ r : Fin 4,
      (GrandChallenges.mcaLatticeSet
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar).Nonempty)
    (heq : ∀ r : Fin 4,
      GrandChallenges.mcaLatticeThreshold
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar (hne r) = (τ r).val) :
    mcaPrizeLatticeResolved domain τ := by
  intro r
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
  have hne' : mcaThresholdExists C epsStar :=
    (mcaSatSet_nonempty_iff C epsStar).mp
      ((mcaSatSet_nonempty_iff_mcaLatticeSet_nonempty C epsStar).mpr (hne r))
  refine ⟨hne', ?_⟩
  apply Fin.ext
  rw [mcaThreshold_val_eq_mcaLatticeThreshold C epsStar hne' (hne r), heq r]

/-- A proposed solution of the list-decoding prize lattice problem at interleaving `m`: for
every prize rate, the faithful list-decoding lattice threshold is the supplied index `τ j`. -/
def listPrizeLatticeResolved (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1)) : Prop :=
  ∀ j : Fin 4,
    ∃ hne : listThresholdExists
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar,
      listThreshold
          (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))
          m epsStar hne = τ j

/-- The faithful list-prize resolution predicate is exactly the per-rate statement that the
proposed lattice index satisfies the list-size bound and is maximal among satisfying lattice
points. -/
theorem listPrizeLatticeResolved_iff (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1)) :
    listPrizeLatticeResolved domain m τ ↔
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : listThresholdExists C m epsStar,
          listSatisfies C m epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), listSatisfies C m epsStar i → i ≤ τ j := by
  constructor
  · intro h j
    rcases h j with ⟨hne, heq⟩
    refine ⟨hne, ?_, ?_⟩
    · simpa [heq] using listThreshold_spec
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar hne
    · intro i hi
      simpa [heq] using le_listThreshold
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar hne hi
  · intro h j
    rcases h j with ⟨hne, hsat, hmax⟩
    refine ⟨hne, ?_⟩
    exact (listThreshold_unique
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      m epsStar hne (τ j) hsat hmax).symm

/-- Existentially resolving the faithful list-decoding lattice prize is equivalent to threshold
nonemptiness at all four prize rates for the chosen interleaving `m`. -/
theorem exists_listPrizeLatticeResolved_iff (domain : ι ↪ F) (m : ℕ) :
    (∃ τ : Fin 4 → Fin (Fintype.card ι + 1), listPrizeLatticeResolved domain m τ) ↔
      ∀ j : Fin 4,
        listThresholdExists
          (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))
          m epsStar := by
  constructor
  · rintro ⟨τ, hτ⟩ j
    exact (hτ j).choose
  · intro h
    refine ⟨fun j =>
      listThreshold
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
          Set (ι → F))
        m epsStar (h j), ?_⟩
    intro j
    exact ⟨h j, rfl⟩

/-- Per-rate lower list-decoding witnesses resolve the faithful list lattice prize
existentially for the chosen interleaving `m`. -/
theorem exists_listPrizeLatticeResolved_of_lowerWitnesses
    (domain : ι ↪ F) (m : ℕ)
    (w : ∀ j : Fin 4,
      GrandChallenges.ListLowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), listPrizeLatticeResolved domain m τ :=
  (exists_listPrizeLatticeResolved_iff domain m).mpr fun j =>
    listThresholdExists_of_ListLowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      m epsStar (w j)

/-- Per-rate lower and upper list-decoding witnesses bracket all four faithful list prize
thresholds for the chosen interleaving `m`. -/
theorem listPrizeLattice_bracketed_of_witnesses
    (domain : ι ↪ F) (m : ℕ)
    (wlo : ∀ j : Fin 4,
      GrandChallenges.ListLowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar)
    (whi : ∀ j : Fin 4,
      GrandChallenges.ListUpperWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      let hne := listThresholdExists_of_ListLowerWitness C m epsStar (wlo j)
      latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one ≤
          listThreshold C m epsStar hne ∧
        listThreshold C m epsStar hne <
          latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := fun j =>
  listThresholdLattice_bracketed_of_witnesses
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    m epsStar (wlo j) (whi j) (hδhi j)

/-- Adjacent per-rate list-decoding witnesses resolve the faithful list lattice prize with the
lower witness indices as the four exact thresholds. -/
theorem listPrizeLatticeResolved_of_adjacent_witnesses
    (domain : ι ↪ F) (m : ℕ)
    (wlo : ∀ j : Fin 4,
      GrandChallenges.ListLowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar)
    (whi : ∀ j : Fin 4,
      GrandChallenges.ListUpperWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one).val + 1) :
    listPrizeLatticeResolved domain m
      (fun j => latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one) := by
  intro j
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  refine ⟨listThresholdExists_of_ListLowerWitness C m epsStar (wlo j), ?_⟩
  exact listThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    C m epsStar (wlo j) (whi j) (hδhi j) (hadj j)

/-- Exact values for the canonical `Finset ℕ` list threshold resolve the four-rate faithful
list-decoding prize predicate in the `Fin (n+1)` lattice representation.

This is pure representation glue: downstream files such as
`GrandChallengeLDThresholdElias.lean` prove exact values for
`GrandChallenges.listLatticeThreshold`, while the prize-facing predicate here is stated using
`listThreshold`. -/
theorem listPrizeLatticeResolved_of_canonical_listLatticeThreshold_eq
    (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (hne : ∀ r : Fin 4,
      (GrandChallenges.listLatticeSet
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar).Nonempty)
    (heq : ∀ r : Fin 4,
      GrandChallenges.listLatticeThreshold
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar (hne r) = (τ r).val) :
    listPrizeLatticeResolved domain m τ := by
  classical
  intro r
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
  have hne' : listThresholdExists C m epsStar :=
    (listSatSet_nonempty_iff C m epsStar).mp
      ((listSatSet_nonempty_iff_listLatticeSet_nonempty C m epsStar).mpr (hne r))
  refine ⟨hne', ?_⟩
  apply Fin.ext
  rw [listThreshold_val_eq_listLatticeThreshold C m epsStar hne' (hne r), heq r]

/-- **Ordinary Reed-Solomon capacity cap at the four ABF26 prize rates.**

This is the exact base-code list-size theorem needed by the faithful list-decoding prize:
for each prize rate, the ordinary smooth-domain Reed-Solomon code has maximised list size
at most `ℓ r` at the proposed predecessor lattice radius `(τ r).val / n`.

The rest of the Lambda/Elias machinery below is fully formalized; proving this predicate is
the remaining ordinary-RS capacity-side mathematical payload. -/
def OrdinaryRSCapacityAtPrizeRates
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ) : Prop :=
  ∀ r : Fin 4,
    Lambda
      (ReedSolomon.code domain
        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (((((τ r).val : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤
        (ℓ r : ℕ∞)

/-- Pointwise finite-list form of `OrdinaryRSCapacityAtPrizeRates`.

This is the native finite combinatorial target: for every received word, the finite list of
ordinary Reed-Solomon codewords at the proposed predecessor radius has cardinality at most
`ℓ r`. -/
def OrdinaryRSCapacityPointwiseAtPrizeRates
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ) : Prop :=
  ∀ r : Fin 4, ∀ f : ι → F,
    (closeCodewordsRelFinset
      (ReedSolomon.code domain
        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      f (((((τ r).val : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)).card ≤
        ℓ r

/-- Pointwise close-list bounds supply the maximised `Λ` cap needed by the LD prize. -/
theorem ordinaryRSCapacityAtPrizeRates_of_pointwise
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hPointwise : OrdinaryRSCapacityPointwiseAtPrizeRates domain τ ℓ) :
    OrdinaryRSCapacityAtPrizeRates domain τ ℓ := by
  intro r
  exact Lambda_le_natCast_of_forall_closeFinset_card_le
    (C := (ReedSolomon.code domain
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
    (δ := (((((τ r).val : ℕ) : ℝ≥0) /
      (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ))
    (ℓ := ℓ r) (hPointwise r)

/-- A maximised `Λ` cap gives the equivalent pointwise finite close-list bound. -/
theorem ordinaryRSCapacityPointwiseAtPrizeRates_of_capacity
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hCapacity : OrdinaryRSCapacityAtPrizeRates domain τ ℓ) :
    OrdinaryRSCapacityPointwiseAtPrizeRates domain τ ℓ := by
  intro r f
  let C : Set (ι → F) := ReedSolomon.code domain
    ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
  let δ : ℝ := (((((τ r).val : ℕ) : ℝ≥0) /
    (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
  have hpoint_le_lambda :
      ((closeCodewordsRel C f δ).ncard : ℕ∞) ≤ Lambda C δ := by
    unfold Lambda
    exact le_iSup
      (fun y : ι → F => ((closeCodewordsRel C y δ).ncard : ℕ∞)) f
  have hcard_enat :
      ((closeCodewordsRelFinset C f δ).card : ℕ∞) ≤ (ℓ r : ℕ∞) := by
    rw [card_closeCodewordsRelFinset_eq_ncard]
    exact le_trans hpoint_le_lambda (by simpa [C, δ] using hCapacity r)
  exact_mod_cast hcard_enat

/-- The prize-rate ordinary-RS `Λ` cap and the pointwise finite-list cap are equivalent. -/
theorem ordinaryRSCapacityAtPrizeRates_iff_pointwise
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ) :
    OrdinaryRSCapacityAtPrizeRates domain τ ℓ ↔
      OrdinaryRSCapacityPointwiseAtPrizeRates domain τ ℓ := by
  constructor
  · exact ordinaryRSCapacityPointwiseAtPrizeRates_of_capacity domain τ ℓ
  · exact ordinaryRSCapacityAtPrizeRates_of_pointwise domain τ ℓ

#print axioms ordinaryRSCapacityAtPrizeRates_iff_pointwise

/-- Any lower bound on one prize-rate `Λ` value that exceeds the proposed ordinary-RS cap
refutes `OrdinaryRSCapacityAtPrizeRates`.

This packages the obstruction side of the LD residual: Elias/GHSZ/ST20-style lower bounds can
be plugged into `hgt` to rule out an over-aggressive proposed predecessor lattice radius/list
size pair. -/
theorem not_ordinaryRSCapacityAtPrizeRates_of_Lambda_gt
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ) (r : Fin 4)
    (hgt :
      (ℓ r : ℕ∞) <
        Lambda
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          (((((τ r).val : ℕ) : ℝ≥0) /
            (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)) :
    ¬ OrdinaryRSCapacityAtPrizeRates domain τ ℓ := by
  intro hCapacity
  exact (not_le_of_gt hgt) (hCapacity r)

/-- Pointwise finite-list version of
`not_ordinaryRSCapacityAtPrizeRates_of_Lambda_gt`. -/
theorem not_ordinaryRSCapacityPointwiseAtPrizeRates_of_Lambda_gt
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ) (r : Fin 4)
    (hgt :
      (ℓ r : ℕ∞) <
        Lambda
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          (((((τ r).val : ℕ) : ℝ≥0) /
            (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)) :
    ¬ OrdinaryRSCapacityPointwiseAtPrizeRates domain τ ℓ := by
  intro hPointwise
  exact not_ordinaryRSCapacityAtPrizeRates_of_Lambda_gt domain τ ℓ r hgt
    (ordinaryRSCapacityAtPrizeRates_of_pointwise domain τ ℓ hPointwise)

/-- `ENNReal` comparison form of `not_ordinaryRSCapacityAtPrizeRates_of_Lambda_gt`.

Many analytic lower bounds, including Elias volume, are stated after coercing `Λ` to
`ENNReal`.  If that coerced value already exceeds the proposed finite cap, the capacity
predicate is impossible. -/
theorem not_ordinaryRSCapacityAtPrizeRates_of_Lambda_toENNReal_gt
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ) (r : Fin 4)
    (hgt :
      (ℓ r : ENNReal) <
        (Lambda
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          (((((τ r).val : ℕ) : ℝ≥0) /
            (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal)) :
    ¬ OrdinaryRSCapacityAtPrizeRates domain τ ℓ := by
  intro hCapacity
  exact (not_le_of_gt hgt) (by exact_mod_cast hCapacity r)

/-- Elias-volume obstruction to a proposed ordinary-RS prize-rate capacity cap.

At a prize rate `r`, if the Elias volume lower bound at the proposed lattice radius
`(τ r).val / n` is already larger than `ℓ r`, then
`OrdinaryRSCapacityAtPrizeRates domain τ ℓ` is false.  The hypotheses `hτ0` and `hτn`
put the radius in the open interval required by the Elias theorem. -/
theorem not_ordinaryRSCapacityAtPrizeRates_of_elias_volume_gt
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ) (r : Fin 4)
    (hτ0 : 0 < (τ r).val)
    (hτn : (τ r).val < Fintype.card ι)
    (hvol :
      (ℓ r : ENNReal) <
        ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((((τ r).val : ℕ) : ℝ≥0) /
                (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) -
                  Module.finrank F
                    (ReedSolomon.code domain
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ :
                        Submodule F (ι → F))))) :
    ¬ OrdinaryRSCapacityAtPrizeRates domain τ ℓ := by
  classical
  let C : Submodule F (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
  let δ : ℝ := (((((τ r).val : ℕ) : ℝ≥0) /
    (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
  have hδpos : (0 : ℝ) < δ := by
    dsimp [δ]
    push_cast
    positivity
  have hδlt : δ < 1 := by
    dsimp [δ]
    push_cast
    rw [div_lt_one (by positivity)]
    exact_mod_cast hτn
  have helias := CodingTheory.linear_lambda_ge_elias_volume_eli57 C δ hδpos hδlt
  have hgt_lambda :
      (ℓ r : ENNReal) <
        (Lambda
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          (((((τ r).val : ℕ) : ℝ≥0) /
            (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal) := by
    calc (ℓ r : ENNReal)
        < ENNReal.ofReal
            ((CodingTheory.hammingBallVolume (Fintype.card F)
                (((((τ r).val : ℕ) : ℝ≥0) /
                  (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
                (Fintype.card ι) : ℝ)
              / (Fintype.card F : ℝ) ^
                  ((Fintype.card ι : ℝ) -
                    Module.finrank F
                      (ReedSolomon.code domain
                        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ :
                          Submodule F (ι → F)))) := hvol
      _ ≤ (Lambda (C : Set (ι → F)) δ : ENNReal) := helias
      _ =
          (Lambda
            (ReedSolomon.code domain
              ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
            (((((τ r).val : ℕ) : ℝ≥0) /
              (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal) := by
        rfl
  exact not_ordinaryRSCapacityAtPrizeRates_of_Lambda_toENNReal_gt domain τ ℓ r hgt_lambda

/-- Per-rate adjacent base-code `Λ` caps and Elias certificates resolve the faithful
four-rate list-decoding lattice prize directly.

This is the capacity-residual analogue of
`listPrizeLatticeResolved_of_johnson_sq_and_elias_next`: for each prize rate, it assumes the
ordinary base Reed-Solomon list-size cap `Λ(RS_k, τ r / n) ≤ ℓ r`, the interleaving budget
inequality, and an Elias-volume failure certificate at `(τ r).val + 1`. -/
theorem listPrizeLatticeResolved_of_Lambda_le_and_elias_next
    (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hm : m ≠ 0)
    (hnext : ∀ r : Fin 4, (τ r).val + 1 < Fintype.card ι)
    (hLambda : ∀ r : Fin 4,
      Lambda
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (((((τ r).val : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤
          (ℓ r : ℕ∞))
    (hpow : ∀ r : Fin 4,
      ((ℓ r : ENNReal)) ^ m ≤
        (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hvol_next : ∀ r : Fin 4,
      (epsStar : ENNReal) * (Fintype.card F : ENNReal) <
        ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((((τ r).val + 1 : ℕ) : ℝ≥0) /
                    (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) -
                  Module.finrank F
                    (ReedSolomon.code domain
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊))))
    (hne : ∀ r : Fin 4,
      (GrandChallenges.listLatticeSet
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar).Nonempty) :
    listPrizeLatticeResolved domain m τ := by
  refine listPrizeLatticeResolved_of_canonical_listLatticeThreshold_eq
    domain m τ hne ?_
  intro r
  exact ProximityGap.listLatticeThreshold_eq_of_Lambda_le_and_elias_next
    (C := ReedSolomon.code domain
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
    (m := m) (j := (τ r).val) (ℓ := ℓ r)
    hm (hnext r) (hLambda r) (hpow r) (hvol_next r) (hne r)

/-- The mathematical residual for the capacity of the ordinary Reed-Solomon code at the four prize rates. -/
theorem Lambda_reedSolomon_prizeRate_capacity_residual
    {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
      [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hdeg_pos : ∀ r : Fin 4,
      0 < ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
    (hdeg_le : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ ≤ Fintype.card ι)
    (hpred_le : ∀ r : Fin 4, (τ r).val ≤ Fintype.card ι)
    (hCapacity : OrdinaryRSCapacityAtPrizeRates domain τ ℓ) :
    ∀ r : Fin 4,
      Lambda
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (((((τ r).val : ℝ≥0) /
              (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)) ≤
          (ℓ r : ℕ∞) := by
  intro r
  exact hCapacity r

#print axioms Lambda_reedSolomon_prizeRate_capacity_residual

theorem listPrizeLatticeResolved_of_ordinaryRSCapacityAtPrizeRates_and_elias_next
    (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hm : m ≠ 0)
    (hnext : ∀ r : Fin 4, (τ r).val + 1 < Fintype.card ι)
    (hCapacity : OrdinaryRSCapacityAtPrizeRates domain τ ℓ)
    (hpow : ∀ r : Fin 4,
      ((ℓ r : ENNReal)) ^ m ≤
        (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hvol_next : ∀ r : Fin 4,
      (epsStar : ENNReal) * (Fintype.card F : ENNReal) <
        ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((((τ r).val + 1 : ℕ) : ℝ≥0) /
                    (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) -
                  Module.finrank F
                    (ReedSolomon.code domain
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊))))
    (hne : ∀ r : Fin 4,
      (GrandChallenges.listLatticeSet
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar).Nonempty) :
    listPrizeLatticeResolved domain m τ :=
  listPrizeLatticeResolved_of_Lambda_le_and_elias_next
    domain m τ ℓ hm hnext hCapacity hpow hvol_next hne

/-- **Packaged four-rate Lambda/Elias exact frontier for the faithful LD prize.**

For every prize rate, this stores the current post-RIM exact closing surface from
`ListLatticeThresholdLambdaEliasFrontier`: a base-code list-size cap at the proposed
threshold index, the interleaving budget, and the adjacent Elias-volume failure certificate.
The nonemptiness field is the representation bridge needed to state the prize-facing
`listPrizeLatticeResolved` predicate. -/
structure ListPrizeLambdaEliasFrontier (domain : ι ↪ F) (m : ℕ) where
  τ : Fin 4 → Fin (Fintype.card ι + 1)
  ℓ : Fin 4 → ℕ
  frontier : ∀ r : Fin 4,
    ListLatticeThresholdLambdaEliasFrontier
      (ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
      m (τ r).val (ℓ r) epsStar
  hne : ∀ r : Fin 4,
    (GrandChallenges.listLatticeSet
      (ReedSolomon.code domain
        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      m epsStar).Nonempty

/-- A packaged four-rate Lambda/Elias frontier resolves the faithful list-decoding lattice
prize at its proposed threshold indices. -/
theorem listPrizeLatticeResolved_of_lambda_elias_frontier
    (domain : ι ↪ F) (m : ℕ)
    (frontier : ListPrizeLambdaEliasFrontier domain m) :
    listPrizeLatticeResolved domain m frontier.τ := by
  refine listPrizeLatticeResolved_of_canonical_listLatticeThreshold_eq
    domain m frontier.τ frontier.hne ?_
  intro r
  exact ProximityGap.listLatticeThreshold_eq_of_lambda_elias_frontier
    (C := ReedSolomon.code domain
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
    (m := m) (j := (frontier.τ r).val) (ℓ := frontier.ℓ r)
    (frontier.frontier r) (frontier.hne r)

/-- Per-rate adjacent Johnson-square/Elias certificates resolve the faithful four-rate
list-decoding lattice prize directly.

This packages the canonical `Finset ℕ` exact-threshold theorem from
`GrandChallengeLDThresholdElias.lean` through the prize-facing `Fin (n+1)` representation:
for each prize rate, a squared Johnson certificate at `τ r` and an Elias-volume failure
certificate at `(τ r).val + 1` determine the exact threshold. -/
theorem listPrizeLatticeResolved_of_johnson_sq_and_elias_next
    (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hm : m ≠ 0)
    (hnext : ∀ r : Fin 4, (τ r).val + 1 < Fintype.card ι)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    Code.minDist
                      (ReedSolomon.code domain
                        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ :
                          Set (ι → F)) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpow : ∀ r : Fin 4,
      ((ℓ r : ENNReal)) ^ m ≤
        (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hvol_next : ∀ r : Fin 4,
      (epsStar : ENNReal) * (Fintype.card F : ENNReal) <
        ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((((τ r).val + 1 : ℕ) : ℝ≥0) /
                    (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) -
                  Module.finrank F
                    (ReedSolomon.code domain
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊))))
    (hne : ∀ r : Fin 4,
      (GrandChallenges.listLatticeSet
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar).Nonempty) :
    listPrizeLatticeResolved domain m τ := by
  refine listPrizeLatticeResolved_of_canonical_listLatticeThreshold_eq
    domain m τ hne ?_
  intro r
  exact ProximityGap.listLatticeThreshold_eq_of_johnson_sq_and_elias_next
    (C := ReedSolomon.code domain
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
    (m := m) (j := (τ r).val) (ℓ := ℓ r)
    hm (hnext r) hq1 (hP r) (hsq r) (hpow r) (hvol_next r) (hne r)

/-- Per-rate adjacent Johnson-square/Elias certificates with the Reed-Solomon distance and
rank already specialized to the prize degree.

This is the numerics-facing ABF26 LD closing criterion: after supplying the standard
Reed-Solomon facts `minDist = n - k + 1` and `finrank = k`, the two remaining analytic
certificates are exactly the squared Johnson inequality and the Elias-volume inequality in
terms of the concrete prize degree `k = ⌊rate·n⌋`. -/
theorem listPrizeLatticeResolved_of_johnson_sq_rsDistance_and_elias_next
    (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hm : m ≠ 0)
    (hnext : ∀ r : Fin 4, (τ r).val + 1 < Fintype.card ι)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hminDist : ∀ r : Fin 4,
      Code.minDist
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) =
        Fintype.card ι - ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1)
    (hrank : ∀ r : Fin 4,
      Module.finrank F
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊) =
        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    (Fintype.card ι -
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpow : ∀ r : Fin 4,
      ((ℓ r : ENNReal)) ^ m ≤
        (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hvol_next : ∀ r : Fin 4,
      (epsStar : ENNReal) * (Fintype.card F : ENNReal) <
        ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((((τ r).val + 1 : ℕ) : ℝ≥0) /
                    (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) -
                  ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)))
    (hne : ∀ r : Fin 4,
      (GrandChallenges.listLatticeSet
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar).Nonempty) :
    listPrizeLatticeResolved domain m τ := by
  refine listPrizeLatticeResolved_of_johnson_sq_and_elias_next
    domain m τ ℓ hm hnext hq1 hP ?_ hpow ?_ hne
  · intro r
    simpa [hminDist r] using hsq r
  · intro r
    simpa [hrank r] using hvol_next r

/-- Numerics-facing ABF26 LD closing criterion with the standard Reed-Solomon invariants
discharged from the degree side conditions.

For each prize rate, it is enough to prove the concrete degree is positive and at most the
block length.  The wrapper supplies `Code.minDist RS = n - k + 1` via
`ReedSolomon.minDist_eq'` and `Module.finrank RS = k` via
`ReedSolomon.dim_eq_deg_of_le'`, leaving only the Johnson/Elias arithmetic certificates. -/
theorem listPrizeLatticeResolved_of_johnson_sq_rsDegreeLe_and_elias_next
    (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hm : m ≠ 0)
    (hdeg_pos : ∀ r : Fin 4,
      0 < ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
    (hdeg_le : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ ≤ Fintype.card ι)
    (hnext : ∀ r : Fin 4, (τ r).val + 1 < Fintype.card ι)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    (Fintype.card ι -
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpow : ∀ r : Fin 4,
      ((ℓ r : ENNReal)) ^ m ≤
        (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hvol_next : ∀ r : Fin 4,
      (epsStar : ENNReal) * (Fintype.card F : ENNReal) <
        ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((((τ r).val + 1 : ℕ) : ℝ≥0) /
                    (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) -
                  ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)))
    (hne : ∀ r : Fin 4,
      (GrandChallenges.listLatticeSet
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar).Nonempty) :
    listPrizeLatticeResolved domain m τ := by
  refine listPrizeLatticeResolved_of_johnson_sq_rsDistance_and_elias_next
    domain m τ ℓ hm hnext hq1 hP ?_ ?_ hsq hpow hvol_next hne
  · intro r
    haveI : NeZero ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ :=
      ⟨(hdeg_pos r).ne'⟩
    exact ReedSolomon.minDist_eq' (α := domain) (hdeg_le r)
  · intro r
    simpa [LinearCode.dim] using
      ReedSolomon.dim_eq_deg_of_le'
        (α := domain)
        (n := ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
        (hdeg_le r)

/-! ## Concrete four-rate MCA prize brackets from named numeric certificates

The combinators above (`mcaPrizeLattice_bracketed_of_witnesses`,
`mcaPrizeLatticeResolved_of_adjacent_witnesses`) take *abstract* per-rate witness families.
The two theorems below are the MCA-side analogue of
`listPrizeLatticeResolved_of_johnson_sq_and_elias_next`: they assemble the four-rate prize
bracket directly from the named BCHKS25 Johnson-range lower certificate and the CS25
complete-CA-breakdown upper certificate, with the exact per-rate side conditions isolated as
hypotheses indexed by the prize rate `j : Fin 4` (each at degree
`k_j := ⌊prizeRates j · n⌋`). This closes the asymmetry flagged in issue #57: the LD side
had a concrete per-rate certificate assembler, the MCA side only had the abstract combinators.
-/

/-- **Four-rate faithful MCA lattice bracket from Johnson(BCHKS25) ⊕ CA-breakdown(CS25).**
For every ABF26 prize rate `j`, the BCHKS25 Johnson-range MCA lower bound at radius `δ_lo j`
and the CS25 complete-CA-breakdown upper bound at radius `δ_hi j` bracket the faithful MCA
lattice threshold of the rate-`j` Reed-Solomon code between the lattice indices `⌊δ_lo j·n⌋`
and `⌊δ_hi j·n⌋`. This is the concrete per-rate instantiation requested in issue #57: the
remaining content is exactly the per-rate Johnson/CS25 numeric inequalities. -/
theorem mcaPrizeLattice_bracketed_ofJohnsonBCHKS25_and_RSBreakdownCS25
    (domain : ι ↪ F)
    (η δ_lo δ_hi : Fin 4 → ℝ≥0)
    (hη : ∀ j : Fin 4, 0 < η j)
    (hδ_johnson : ∀ j : Fin 4,
        (δ_lo j : ℝ) <
          1 - (((⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / Fintype.card ι
              + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) - (η j : ℝ))
    (hδlo_le_one : ∀ j : Fin 4, δ_lo j ≤ 1)
    (hBCHKS25 : ∀ j : Fin 4,
      CodingTheory.rs_epsMCA_johnson_range_bchks25 domain
        ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (η j) (δ_lo j) (hη j) (hδ_johnson j))
    (hle : ∀ j : Fin 4,
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η j)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo j * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (epsStar : ENNReal))
    (hδhi : ∀ j : Fin 4, δ_hi j ≤ 1)
    (hq_ge : ∀ _ : Fin 4, 10 ≤ Fintype.card F)
    (hδ_cs_lo : ∀ j : Fin 4,
        1 - CodingTheory.qEntropy (Fintype.card F) (δ_hi j : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((CodingTheory.qEntropy (Fintype.card F) (δ_hi j : ℝ) - (δ_hi j : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / Fintype.card ι)
    (hδ_cs_hi : ∀ j : Fin 4,
        (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / Fintype.card ι
          ≤ 1 - (δ_hi j : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hCS25 : ∀ j : Fin 4,
      CodingTheory.rs_epsCA_breakdown_cs25 domain
        ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (δ_hi j)
        (hq_ge j) (hδ_cs_lo j) (hδ_cs_hi j))
    (hε : ∀ _ : Fin 4, (epsStar : ENNReal) < 1) :
    ∀ j : Fin 4,
      let hne := mcaThresholdExists_ofJohnsonBCHKS25 domain
        ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (η j) (δ_lo j) epsStar
        (hη j) (hδ_johnson j) (hδlo_le_one j) (hBCHKS25 j) (hle j)
      latticeIndexOf (ι := ι) (δ_lo j) (hδlo_le_one j) ≤
          mcaThreshold (ReedSolomon.code domain
            ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) epsStar hne ∧
        mcaThreshold (ReedSolomon.code domain
            ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) epsStar hne <
          latticeIndexOf (ι := ι) (δ_hi j) (hδhi j) := fun j =>
  mcaThresholdLattice_bracketed_ofJohnsonBCHKS25_and_RSBreakdownCS25
    domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (η j) (δ_lo j) (δ_hi j) epsStar
    (hη j) (hδ_johnson j) (hδlo_le_one j) (hBCHKS25 j) (hle j)
    (hδhi j) (hq_ge j) (hδ_cs_lo j) (hδ_cs_hi j) (hCS25 j) (hε j)

/-- **Four-rate faithful MCA prize resolution from adjacent Johnson(BCHKS25)/CS25
certificates.** If at every prize rate the CS25 upper lattice index `⌊δ_hi j·n⌋` is exactly
one above the BCHKS25 lower lattice index `⌊δ_lo j·n⌋`, the bracket pins the faithful MCA
lattice threshold to the lower index at each rate, *resolving* the four-rate faithful MCA
prize predicate `mcaPrizeLatticeResolved`. This is the MCA counterpart of
`listPrizeLatticeResolved_of_johnson_sq_and_elias_next`. -/
theorem mcaPrizeLatticeResolved_ofJohnsonBCHKS25_and_RSBreakdownCS25_adjacent
    (domain : ι ↪ F)
    (η δ_lo δ_hi : Fin 4 → ℝ≥0)
    (hη : ∀ j : Fin 4, 0 < η j)
    (hδ_johnson : ∀ j : Fin 4,
        (δ_lo j : ℝ) <
          1 - (((⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / Fintype.card ι
              + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) - (η j : ℝ))
    (hδlo_le_one : ∀ j : Fin 4, δ_lo j ≤ 1)
    (hBCHKS25 : ∀ j : Fin 4,
      CodingTheory.rs_epsMCA_johnson_range_bchks25 domain
        ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (η j) (δ_lo j) (hη j) (hδ_johnson j))
    (hle : ∀ j : Fin 4,
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η j)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo j * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (epsStar : ENNReal))
    (hδhi : ∀ j : Fin 4, δ_hi j ≤ 1)
    (hq_ge : ∀ _ : Fin 4, 10 ≤ Fintype.card F)
    (hδ_cs_lo : ∀ j : Fin 4,
        1 - CodingTheory.qEntropy (Fintype.card F) (δ_hi j : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((CodingTheory.qEntropy (Fintype.card F) (δ_hi j : ℝ) - (δ_hi j : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / Fintype.card ι)
    (hδ_cs_hi : ∀ j : Fin 4,
        (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ) / Fintype.card ι
          ≤ 1 - (δ_hi j : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hCS25 : ∀ j : Fin 4,
      CodingTheory.rs_epsCA_breakdown_cs25 domain
        ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (δ_hi j)
        (hq_ge j) (hδ_cs_lo j) (hδ_cs_hi j))
    (hε : ∀ _ : Fin 4, (epsStar : ENNReal) < 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (δ_hi j) (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ_lo j) (hδlo_le_one j)).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (δ_lo j) (hδlo_le_one j)) :=
  mcaPrizeLatticeResolved_of_adjacent_witnesses domain
    (fun j => GrandChallenges.MCALowerWitness.ofJohnsonBCHKS25 domain
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (η j) (δ_lo j) epsStar
      (hη j) (hδ_johnson j) (hδlo_le_one j) (hBCHKS25 j) (hle j))
    (fun j => GrandChallenges.MCAUpperWitness.ofRSBreakdownCS25 domain
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (δ_hi j) epsStar
      (hq_ge j) (hδ_cs_lo j) (hδ_cs_hi j) (hCS25 j) (hε j))
    (fun j => hδhi j)
    (fun j => hadj j)

end GrandChallengesLattice

end ProximityGap

#print axioms
  ProximityGap.GrandChallengesLattice.listPrizeLatticeResolved_of_ordinaryRSCapacityAtPrizeRates_and_elias_next
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_topCode
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_topCode_eq_top
