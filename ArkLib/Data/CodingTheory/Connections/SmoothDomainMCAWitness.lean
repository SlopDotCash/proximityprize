/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA
import ArkLib.Data.CodingTheory.ProximityGap.Lattice2

/-!
# List-size → MCA witnesses: wiring the smooth-domain derandomization route

The "up" direction of the Grand LD Challenge (the CONJ-A/CONJ-3 RIM program,
`research/proximity-prize/conja-qanalog`) aims at AGL24/GZ-style list-size bounds for
plain RS over smooth domains `μ_{2^t}`. ABF26 Theorem 5.1 [GCXK25 Thm 3] converts any
such list-size bound into an `ε_mca` bound at the Johnson lift `1 - √(1-δ+η)` of the
list-decoding radius — a second, Guruswami–Sudan-free route to the Johnson-range floor
of the **Grand MCA Challenge** on smooth domains.

This file is pure plumbing (sorry-free): it composes the honest in-tree reduction
`linear_listSize_to_epsMCA_gcxk25_of_bad_count` (whose only hypothesis beyond the
list-size bound is GCXK25's per-stack bad-`γ` count, the genuine external content) with
the Grand-Challenge witness layer:

* `MCALowerWitness.ofListSizeGCXK25` — a list-size bound + the GCXK25 per-stack count +
  a numeric threshold check yield a verified `MCALowerWitness` at the Johnson lift.
* `mcaThresholdExists_ofListSizeGCXK25` / `le_mcaThreshold_ofListSizeGCXK25` — the same
  data makes the faithful MCA lattice threshold exist and bounds it from below.

The √-loss in the radius is intrinsic to the black-box list-size→MCA implication
(ABF26 §5 discusses counterexamples); the lossless route is line-decoding (T4.21).

## References

- [ABF26] §5, Theorem 5.1; §1 (Grand MCA Challenge).
- [GCXK25] Theorem 3.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal ProbabilityTheory
open ListDecodable CodingTheory GrandChallenges GrandChallengesLattice

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The Johnson lift `1 - √(1-δ+η)` of a list-decoding radius, as a `ℝ≥0` radius. -/
noncomputable def johnsonLift (δ η : ℝ) : ℝ≥0 :=
  (1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal

/-- The Johnson lift is a legal radius: `johnsonLift δ η ≤ 1` whenever `1 - δ + η ≥ 0`
(in particular whenever `δ < 1` and `0 < η`). -/
theorem johnsonLift_le_one {δ η : ℝ} (hδ_lt : δ < 1) (hη_pos : 0 < η) :
    johnsonLift δ η ≤ 1 := by
  unfold johnsonLift
  rw [Real.toNNReal_le_one]
  have hbase : (0 : ℝ) ≤ 1 - δ + η := by linarith
  have hroot : (0 : ℝ) ≤ (1 - δ + η) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg hbase _
  linarith

/-- **List-size ⟹ MCA lower witness (GCXK25 route).** A list-size bound `Λ(C, δ) ≤ L`
(e.g. from the derandomized AGL24/GZ program on a smooth domain), the GCXK25 per-stack
bad-`γ` count, and a numeric check that the resulting bound clears `ε*` produce a verified
`MCALowerWitness` at the Johnson lift of `δ`: every Grand-MCA resolution has
`δ* ≥ 1 - √(1-δ+η)`. -/
noncomputable def GrandChallenges.MCALowerWitness.ofListSizeGCXK25
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hBadCount :
        ∀ u : Code.WordStack F (Fin 2) ι,
          ((ProximityGap.mcaBad (F := F) ((C : Set (ι → F)))
              ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) (u 0) (u 1)).card : ℝ) ≤
            (L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η)
    (hle : ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
      (ε_star : ENNReal)) :
    MCALowerWitness ((C : Set (ι → F))) ε_star :=
  MCALowerWitness.ofLe (johnsonLift_le_one hδ_lt hη_pos)
    (le_trans
      (linear_listSize_to_epsMCA_gcxk25_of_bad_count C L δ η
        hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hBadCount)
      hle)

/-- The same data makes the faithful MCA lattice threshold exist. -/
theorem mcaThresholdExists_ofListSizeGCXK25
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hBadCount :
        ∀ u : Code.WordStack F (Fin 2) ι,
          ((ProximityGap.mcaBad (F := F) ((C : Set (ι → F)))
              ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) (u 0) (u 1)).card : ℝ) ≤
            (L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η)
    (hle : ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
      (ε_star : ENNReal)) :
    mcaThresholdExists ((C : Set (ι → F))) ε_star :=
  mcaThresholdExists_of_MCALowerWitness _ _
    (GrandChallenges.MCALowerWitness.ofListSizeGCXK25 C L δ η ε_star
      hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hBadCount hle)

/-- …and bounds it from below by the lattice index of the Johnson lift. -/
theorem le_mcaThreshold_ofListSizeGCXK25
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ) (ε_star : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hBadCount :
        ∀ u : Code.WordStack F (Fin 2) ι,
          ((ProximityGap.mcaBad (F := F) ((C : Set (ι → F)))
              ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) (u 0) (u 1)).card : ℝ) ≤
            (L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η)
    (hle : ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) ≤
      (ε_star : ENNReal))
    (hne : mcaThresholdExists ((C : Set (ι → F))) ε_star) :
    latticeIndexOf (ι := ι) (johnsonLift δ η) (johnsonLift_le_one hδ_lt hη_pos) ≤
      mcaThreshold ((C : Set (ι → F))) ε_star hne :=
  MCALowerWitness_le_mcaThreshold _ _ hne
    (GrandChallenges.MCALowerWitness.ofListSizeGCXK25 C L δ η ε_star
      hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hBadCount hle)

end ProximityGap
