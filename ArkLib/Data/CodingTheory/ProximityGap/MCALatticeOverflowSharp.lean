/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Lattice

/-!
# MCA lattice sharpening and conditional pinning (#232, MCA Grand Challenge)

The MCA analog of `listLatticeThreshold_lt_of_overflow` / `…_eq_of_mem_of_overflow_succ`, on the
discrete faithful MCA threshold `mcaLatticeThreshold C ε* = max {j | ε_mca(C, j/n) ≤ ε*}`:

* `mcaLatticeThreshold_lt_of_overflow` — an MCA overflow `ε_mca(C, j/n) > ε*` forces
  `mcaLatticeThreshold C ε* < j` (monotonicity `epsMCA_mono` + `Finset.max'_lt_iff`).
* `mcaLatticeThreshold_eq_of_mem_of_overflow_succ` — membership at `j` (the open MCA lower bound)
  plus an overflow at `j+1` pins `mcaLatticeThreshold C ε* = j`.

So the discrete MCA threshold is *determined* the moment one proves `ε_mca(C, j/n) ≤ ε*` at the
critical index — exactly mirroring the list-decoding reduction. The MCA lower side currently reaches
only the unique-decoding radius (`rs_mcaLowerWitness_udr`); pushing it to Johnson is the BCIKS20
bivariate line-decoding argument, and to capacity is the open prize. Axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap

open scoped NNReal ENNReal

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **MCA overflow pushes the lattice threshold below `j`.** If `ε_mca(C, j/n)` exceeds the budget
`ε*`, then `mcaLatticeThreshold C ε* < j`. -/
theorem mcaLatticeThreshold_lt_of_overflow (C : Set (ι → F)) {j : ℕ} {ε_star : ℝ≥0}
    (hover : (ε_star : ENNReal)
        < epsMCA (F := F) (A := F) C ((j : ℝ≥0) / (Fintype.card ι : ℝ≥0)))
    (hne : (GrandChallenges.mcaLatticeSet C ε_star).Nonempty) :
    GrandChallenges.mcaLatticeThreshold C ε_star hne < j := by
  classical
  rw [GrandChallenges.mcaLatticeThreshold, Finset.max'_lt_iff]
  intro t ht
  rw [GrandChallenges.mcaLatticeSet, Finset.mem_filter, Finset.mem_range] at ht
  obtain ⟨htn, htle⟩ := ht
  by_contra hjt
  push_neg at hjt
  have hjt' : (j : ℝ≥0) ≤ (t : ℝ≥0) := by exact_mod_cast hjt
  have hrad : ((j : ℝ≥0) / (Fintype.card ι : ℝ≥0)) ≤ ((t : ℝ≥0) / (Fintype.card ι : ℝ≥0)) := by
    gcongr
  have hmono := epsMCA_mono (F := F) (A := F) C hrad
  exact absurd (le_trans hmono htle) (not_le.mpr hover)

/-- **Conditional exact pinning (MCA).** Membership at `j` (the open MCA lower bound) plus an MCA
overflow at `j+1` (an upper bound) pins the discrete MCA threshold exactly at `j`. -/
theorem mcaLatticeThreshold_eq_of_mem_of_overflow_succ (C : Set (ι → F)) {j : ℕ} {ε_star : ℝ≥0}
    (hmem : j ∈ GrandChallenges.mcaLatticeSet C ε_star)
    (hover : (ε_star : ENNReal)
        < epsMCA (F := F) (A := F) C (((j + 1 : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0)))
    (hne : (GrandChallenges.mcaLatticeSet C ε_star).Nonempty) :
    GrandChallenges.mcaLatticeThreshold C ε_star hne = j := by
  have hlo : j ≤ GrandChallenges.mcaLatticeThreshold C ε_star hne := by
    rw [GrandChallenges.mcaLatticeThreshold]
    exact Finset.le_max' _ _ hmem
  have hhi : GrandChallenges.mcaLatticeThreshold C ε_star hne < j + 1 :=
    mcaLatticeThreshold_lt_of_overflow C hover hne
  omega

#print axioms mcaLatticeThreshold_lt_of_overflow
#print axioms mcaLatticeThreshold_eq_of_mem_of_overflow_succ

end ProximityGap
