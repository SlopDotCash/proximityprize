/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BandExactness

/-!
# The unconditional `δ*` floor from the exact staircase

The exact staircase (`epsMCA_band_exact`) says `ε_mca(RS, j/n) = (j+1)/q` on every
in-hypothesis band. Reading it in the good direction: whenever `j + 1 ≤ ε*·q`, the lattice
radius `j/n` is a **good** radius, so the bracket engine gives

  **`mcaDeltaStar(RS, ε*) ≥ j/n` — unconditionally.**

At production parameters (`ε*·q ≈ 2^{128} ≫ n`) the binding constraint is the staircase
hypothesis `3j < n − (k−1)`: the floor reaches `δ* ≥ ⌊(n−k)/3⌋/n ≈ (1−ρ)/3`. Within this
repository's *proven* (non-interface) surface this is, to date, the deepest unconditional
`δ*` lower bound at production parameters: the Johnson-side floors (BCGM25/Hab25/BCHKS25)
remain external interface surfaces (`JohnsonDischargeStatement` et al.), while every
ingredient here — the band collapse, the spike bound, the bracket engine — is in-tree and
axiom-clean.

Honest position: this does **not** beat Johnson (`1 − √ρ > (1−ρ)/3` for all `ρ < 1`); it
is the best *fully machine-checked* floor pending the Johnson discharge.

## References
* Issue #357; `BandExactness.lean`, `MCAThresholdLedger.lean`.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.BandCollapse

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code Finset GrandChallengesLattice
open ProximityGap.MCAThresholdLedger

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **The unconditional staircase floor.** For any band `j` inside the staircase hypothesis
(`3j < n − (k−1)`, plus the spike size conditions) whose exact value clears the target
(`(j+1)/q ≤ ε*`), the lattice radius `j/n` is good, so
`mcaDeltaStar(RS, ε*) ≥ j/n`. Every ingredient is in-tree and axiom-clean: at production
parameters this reaches `δ* ≳ (1−ρ)/3` with no external interfaces. -/
theorem le_mcaDeltaStar_of_band (domain : ι ↪ F) {k : ℕ}
    (j : Fin (Fintype.card ι + 1))
    (hjn : j.val < Fintype.card ι)
    (ht_n : j.val + 1 + k ≤ Fintype.card ι)
    (ht_q : j.val + 1 ≤ Fintype.card F)
    (hd : 3 * j.val < Fintype.card ι - (k - 1))
    (εstar : ℝ≥0∞)
    (hε : (↑(j.val + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    mcaLatticePoint (Fintype.card ι) j
      ≤ mcaDeltaStar (F := F) (A := F)
          (ReedSolomon.code domain k : Set (ι → F)) εstar := by
  refine le_mcaDeltaStar_of_good (F := F) (A := F)
    (ReedSolomon.code domain k : Set (ι → F)) εstar
    (mcaLatticePoint_le_one _ _) ?_
  rw [epsMCA_band_exact domain j hjn ht_n ht_q hd]
  exact hε

/-! ## Source audit -/

#print axioms le_mcaDeltaStar_of_band

end ProximityGap.BandCollapse
