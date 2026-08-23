/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.JohnsonBound.ReedSolomonJohnsonLambda
import ArkLib.Data.CodingTheory.Connections.SmoothDomainMCAWitness

/-!
# The conditional Reed–Solomon MCA δ* floor (#371 / #389)

This packages the δ* prize **floor** for Reed–Solomon codes into the exact shape the prize asks
for: `δ* ≥ (a Johnson-lift radius)` **conditional on one named object with a numeric budget**.

The smooth-domain MCA floor path (`ProximityGap.le_mcaThreshold_ofListSizeGCXK25`) needs two
inputs:
* a list-size bound `hΛ : Λ(C, δ) ≤ L` — **discharged in-tree** here for RS via
  `ArkLib.JohnsonBound.rs_johnson_lambda_nat_le` (the MDS Johnson list size,
  `L = ⌈1/(2 η_J ρ)⌉₊`, constant in `n`);
* the GCXK25 first-moment per-stack bad-scalar count `hBadCount` — the **single remaining named
  residual** (equivalently the carrier-`L²` second-moment cover, the active swarm route-2 target).

`rs_le_mcaThreshold_of_badCount` is therefore the RS conditional Johnson-lift δ* floor with
`hBadCount` (+ the numeric budget `hle`) as the sole hypotheses beyond positivity/range: the
list-size half is no longer assumed.
-/

open scoped NNReal
open CodingTheory ListDecodable ProximityGap ProximityGap.GrandChallengesLattice

namespace ArkLib.ProximityGapFloor

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Conditional RS Johnson-lift δ* floor.** For the Reed–Solomon code `ReedSolomon.code α k`
of rate `ρ = k / n`, list radius `δ = 1 − √ρ − η_J`, and MCA lift slack `η`, the MCA threshold
`δ*(RS, ε*)` is at least the lattice index of the Johnson lift `1 − √(1 − δ + η)` — **conditional
only** on the GCXK25 first-moment per-stack bad-scalar count `hBadCount` and the numeric budget
`hle`. The list-size hypothesis is discharged in-tree by `rs_johnson_lambda_nat_le`
(`L = ⌈1/(2 η_J ρ)⌉₊`), so `hBadCount` is the prize's single "named object". -/
theorem rs_le_mcaThreshold_of_badCount
    {k : ℕ} [NeZero k] {α : ι ↪ F}
    (η_J η : ℝ) (ε_star : ℝ≥0)
    (hk : k ≤ Fintype.card ι)
    (hη_J_pos : 0 < η_J)
    (hδ_pos : 0 < 1 - Real.sqrt ((k : ℝ) / Fintype.card ι) - η_J)
    (hδ_lt : 1 - Real.sqrt ((k : ℝ) / Fintype.card ι) - η_J < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1)
    (hη_le_δ : η ≤ 1 - Real.sqrt ((k : ℝ) / Fintype.card ι) - η_J)
    (hBadCount :
        ∀ u : Code.WordStack F (Fin 2) ι,
          ((mcaBad (F := F) ((ReedSolomon.code α k : Set (ι → F)))
              ((1 - (1 - (1 - Real.sqrt ((k : ℝ) / Fintype.card ι) - η_J) + η) ^ ((1 : ℝ) / 2)).toNNReal)
              (u 0) (u 1)).card : ℝ) ≤
            ((⌈1 / (2 * η_J * ((k : ℝ) / Fintype.card ι))⌉₊ : ℕ) : ℝ) ^ 2
                * (1 - Real.sqrt ((k : ℝ) / Fintype.card ι) - η_J) * Fintype.card ι + 1 / η)
    (hle : ENNReal.ofReal
        ((((⌈1 / (2 * η_J * ((k : ℝ) / Fintype.card ι))⌉₊ : ℕ) : ℝ) ^ 2
              * (1 - Real.sqrt ((k : ℝ) / Fintype.card ι) - η_J) * Fintype.card ι + 1 / η)
          / Fintype.card F) ≤ (ε_star : ENNReal))
    (hne : mcaThresholdExists ((ReedSolomon.code α k : Set (ι → F))) ε_star) :
    latticeIndexOf (ι := ι)
        (johnsonLift (1 - Real.sqrt ((k : ℝ) / Fintype.card ι) - η_J) η)
        (johnsonLift_le_one hδ_lt hη_pos) ≤
      mcaThreshold ((ReedSolomon.code α k : Set (ι → F))) ε_star hne :=
  le_mcaThreshold_ofListSizeGCXK25 (ReedSolomon.code α k)
    ⌈1 / (2 * η_J * ((k : ℝ) / Fintype.card ι))⌉₊
    (1 - Real.sqrt ((k : ℝ) / Fintype.card ι) - η_J) η ε_star
    hδ_pos hδ_lt hη_pos hη_lt hη_le_δ
    (ArkLib.JohnsonBound.rs_johnson_lambda_nat_le η_J hη_J_pos hk)
    hBadCount hle hne

end ArkLib.ProximityGapFloor
