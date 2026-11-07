/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Research.ProximityPrize.MCAGSWitness
import Research.ProximityPrize.LatticeSpec

/-!
# Faithful MCA prize specifications from GS mass frontiers

`MCAGSWitness.lean` packages the remaining Guruswami-Sudan obligations as explicit faithful
mass and pivot/list-size frontiers, and turns each such frontier into a `MCALowerWitness`.
This module routes the **mass** frontiers through the faithful four-rate lattice prize API and
the satisfy/maximality specification layer.

The former `..._of_GSPivotFrontier(s)...` copies of every theorem here were removed (audit
CW-B21-04): each was its `GSMass` twin composed with
`MCAGS.GSPivotLowerWitnessFrontier.toGSMassLowerWitnessFrontier`, and the uniform pivot frontier
was moreover uninstantiable (its covering field demands `u 1 x ≠ 0` for every stack, which fails at
`u 1 = 0`). A caller holding pivot frontiers `fr j` should pass
`fun j => (fr j).toGSMassLowerWitnessFrontier _ _ _` to the `GSMass` theorem.

For explicit adjacent upper witnesses the canonical theorems are
`mcaPrizeLatticeResolved_of_GSMassFrontiers_and_adjacent_upperWitnesses` and their
`_with_spec` / `mcaPrizeLatticeSpec_` projections. Earlier `...GS{Mass,Pivot}AdjacentFrontier`
copies with identical binders and conclusions, and the adjacent `..._brackets_...` wrappers, were
removed: with `τ j := latticeIndexOf (δ j)` their lower bracket is `le_rfl` and their strict upper
bracket is the hypothesis `hadj`, so they carried no content beyond the `_with_spec` theorems.
-/

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators NNReal ENNReal

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace GrandChallengesLattice

open GrandChallenges

section GSThresholdSpec

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A faithful GS mass frontier supplies existence of the faithful MCA lattice threshold. -/
theorem mcaThresholdExists_of_GSMassFrontier
    (C : LinearCode ι F) (δ ε_star : ℝ≥0) (hδ_le_one : δ ≤ 1)
    (frontier : MCAGS.GSMassLowerWitnessFrontier (F := F) C δ ε_star) :
    mcaThresholdExists (C : Set (ι → F)) ε_star :=
  mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) ε_star
    (MCAGS.MCALowerWitness.ofGSMassFrontier C δ ε_star hδ_le_one frontier)

/-- A faithful GS mass frontier supplies the selected threshold's satisfy fact. -/
theorem mcaThreshold_spec_of_GSMassFrontier
    (C : LinearCode ι F) (δ ε_star : ℝ≥0) (hδ_le_one : δ ≤ 1)
    (frontier : MCAGS.GSMassLowerWitnessFrontier (F := F) C δ ε_star) :
    let hne := mcaThresholdExists_of_GSMassFrontier C δ ε_star hδ_le_one frontier
    mcaSatisfies (C : Set (ι → F)) ε_star
      (mcaThreshold (C : Set (ι → F)) ε_star hne) :=
  mcaThreshold_spec (C : Set (ι → F)) ε_star
    (mcaThresholdExists_of_GSMassFrontier C δ ε_star hδ_le_one frontier)

/-- A faithful GS mass frontier lower-bounds the selected faithful MCA lattice threshold. -/
theorem latticeIndexOf_le_mcaThreshold_of_GSMassFrontier
    (C : LinearCode ι F) (δ ε_star : ℝ≥0) (hδ_le_one : δ ≤ 1)
    (frontier : MCAGS.GSMassLowerWitnessFrontier (F := F) C δ ε_star) :
    let hne := mcaThresholdExists_of_GSMassFrontier C δ ε_star hδ_le_one frontier
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold (C : Set (ι → F)) ε_star hne :=
  MCALowerWitness_le_mcaThreshold (C : Set (ι → F)) ε_star
    (mcaThresholdExists_of_GSMassFrontier C δ ε_star hδ_le_one frontier)
    (MCAGS.MCALowerWitness.ofGSMassFrontier C δ ε_star hδ_le_one frontier)

/-- Per-rate faithful GS mass frontiers resolve the faithful MCA lattice prize existentially. -/
theorem exists_mcaPrizeLatticeResolved_of_GSMassFrontiers
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ :=
  exists_mcaPrizeLatticeResolved_of_lowerWitnesses domain fun j =>
    MCAGS.MCALowerWitness.ofGSMassFrontier
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
      (δ j) epsStar (hδ_le_one j) (frontier j)

/-- Per-rate faithful GS mass frontiers resolve the faithful MCA prize and expose the
satisfy/maximality specification for the selected lattice thresholds. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_of_GSMassFrontiers
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses domain fun j =>
    MCAGS.MCALowerWitness.ofGSMassFrontier
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
      (δ j) epsStar (hδ_le_one j) (frontier j)

/-- Per-rate faithful GS mass frontiers expose the selected-threshold specification and lower
lattice brackets for the faithful MCA prize lattice. -/
theorem exists_mcaPrizeLatticeSpec_and_lower_brackets_of_GSMassFrontiers
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      (∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j) ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_mcaPrizeLatticeSpec_and_lower_brackets_of_lowerWitnesses domain δ hδ_le_one
    (fun j =>
      MCAGS.MCALowerWitness.ofGSMassFrontier
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar (hδ_le_one j) (frontier j))
    (fun _ => rfl)

/-- Per-rate faithful GS mass frontiers resolve the faithful MCA prize and expose the selected
threshold specification together with lower lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_GSMassFrontiers
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar) :
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
  exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_lowerWitnesses
    domain δ hδ_le_one
    (fun j =>
      MCAGS.MCALowerWitness.ofGSMassFrontier
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar (hδ_le_one j) (frontier j))
    (fun _ => rfl)

/-- Per-rate faithful GS mass frontiers resolve the faithful MCA prize and expose lower lattice
brackets for the selected thresholds. -/
theorem exists_mcaPrizeLatticeResolved_with_lower_brackets_of_GSMassFrontiers
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_lower_brackets_of_lowerWitnesses
    domain δ hδ_le_one
    (fun j =>
      MCAGS.MCALowerWitness.ofGSMassFrontier
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar (hδ_le_one j) (frontier j))
    (fun _ => rfl)

/-- Per-rate faithful GS mass frontiers and explicit upper witnesses expose the selected-threshold
specification and two-sided lattice brackets for the faithful MCA prize lattice. -/
theorem exists_mcaPrizeLatticeSpec_and_brackets_of_GSMassFrontiers
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar)
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
  exists_mcaPrizeLatticeSpec_and_brackets_of_lowerWitnesses domain δ hδ_le_one
    (fun j =>
      MCAGS.MCALowerWitness.ofGSMassFrontier
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar (hδ_le_one j) (frontier j))
    (fun _ => rfl) whi hδhi

/-- Per-rate faithful GS mass frontiers and explicit upper witnesses resolve the faithful MCA prize
and expose the selected-threshold specification together with two-sided lattice brackets. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_GSMassFrontiers
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar)
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
  exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_lowerWitnesses
    domain δ hδ_le_one
    (fun j =>
      MCAGS.MCALowerWitness.ofGSMassFrontier
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar (hδ_le_one j) (frontier j))
    (fun _ => rfl) whi hδhi

/-- Per-rate faithful GS mass frontiers and explicit upper witnesses resolve the faithful MCA prize
and expose only the two-sided lattice brackets for the selected thresholds. -/
theorem exists_mcaPrizeLatticeResolved_with_brackets_of_GSMassFrontiers
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar)
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
          ∀ j : Fin 4, τ j < latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
  exists_mcaPrizeLatticeResolved_with_brackets_of_lowerWitnesses
    domain δ hδ_le_one
    (fun j =>
      MCAGS.MCALowerWitness.ofGSMassFrontier
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar (hδ_le_one j) (frontier j))
    (fun _ => rfl) whi hδhi

/-- Faithful GS mass lower frontiers and explicit upper witnesses bracket all four faithful MCA
prize thresholds. -/
def mcaPrizeLattice_bracketed_of_GSMassFrontiers_and_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :=
  mcaPrizeLattice_bracketed_of_witnesses domain
    (fun j =>
      MCAGS.MCALowerWitness.ofGSMassFrontier
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar (hδ_le_one j) (frontier j))
    whi hδhi

/-- Faithful GS mass frontiers and adjacent explicit upper witnesses resolve the four-rate MCA
prize lattice at the lower-frontier lattice indices. -/
theorem mcaPrizeLatticeResolved_of_GSMassFrontiers_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar)
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
  refine mcaPrizeLatticeResolved_of_adjacent_witnesses domain
    (fun j =>
      MCAGS.MCALowerWitness.ofGSMassFrontier
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar (hδ_le_one j) (frontier j))
    whi hδhi ?_
  intro j
  exact hadj j

/-- Adjacent GS mass frontiers resolve the four-rate MCA prize at the lower-frontier lattice
indices and expose the satisfy/maximality specification for those concrete thresholds. -/
theorem mcaPrizeLatticeResolved_with_spec_of_GSMassFrontiers_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar)
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
    mcaPrizeLatticeResolved_of_GSMassFrontiers_and_adjacent_upperWitnesses
      domain δ hδ_le_one frontier whi hδhi hadj
  exact ⟨hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

/-- Package faithful GS mass frontiers and explicit adjacent upper witnesses into the generic
four-rate adjacent-witness frontier. -/
noncomputable def mcaPrizeAdjacentWitnessFrontier_of_GSMassFrontiers_and_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar)
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
    MCAGS.MCALowerWitness.ofGSMassFrontier
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
      (δ j) epsStar (hδ_le_one j) (frontier j)
  upper := whi
  upper_le_one := hδhi
  adjacent := by
    intro j
    exact hadj j

/-- Project the exact threshold specification from adjacent GS mass frontiers. -/
theorem mcaPrizeLatticeSpec_of_GSMassFrontiers_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar)
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
  (mcaPrizeLatticeResolved_with_spec_of_GSMassFrontiers_and_adjacent_upperWitnesses
    domain δ hδ_le_one frontier whi hδhi hadj).2

end GSThresholdSpec

set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_of_GSMassFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_of_GSMassFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_of_GSMassFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_of_GSMassFrontiers
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_GSMassFrontiers
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_lower_brackets_of_GSMassFrontiers
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_GSMassFrontiers
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_lower_brackets_of_GSMassFrontiers
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeSpec_and_brackets_of_GSMassFrontiers
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_GSMassFrontiers
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_brackets_of_GSMassFrontiers
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLattice_bracketed_of_GSMassFrontiers_and_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_of_GSMassFrontiers_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_GSMassFrontiers_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeAdjacentWitnessFrontier_of_GSMassFrontiers_and_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeSpec_of_GSMassFrontiers_and_adjacent_upperWitnesses

end GrandChallengesLattice

end ProximityGap
