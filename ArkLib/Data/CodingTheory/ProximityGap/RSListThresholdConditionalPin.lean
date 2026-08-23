/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RSListThresholdOverflowSharpGen

/-!
# Conditional exact pinning of the list-decoding threshold (#232)

The whole open content of the Grand List-Decoding Challenge is now isolated to a *single* missing
ingredient. This file proves that one list-decodability fact at the critical index — the open
matching lower bound — plus the **already-proven** overflow one step above, pins the threshold
exactly:

  `listLatticeThreshold_eq_of_mem_of_overflow_succ` — if index `j` is in the faithful lattice
  (`Λ(C^⋈m, j/n) ≤ ε*·|F|`, the open lower bound) and the base code overflows at `j+1`
  (`Λ(C, (j+1)/n) > ε*·|F|`, supplied by `rs_lambda_gt_of_capExp_overflow`), then
  `listLatticeThreshold C m ε* = j`.

So the genuine threshold is *determined* the moment one proves list-decodability at the critical
index `j = ⌊δ_LD·n⌋`: the lower bound `j ∈ lattice` is exactly the unsolved $1M breakthrough, and it
would immediately fix `δ*` (the upper side `threshold < j+1` is already done via
`listLatticeThreshold_lt_of_overflow`). This file makes that reduction machine-checked, correctly
delineating the open core (cf. #169: no fake-completion).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open ListDecodable

/-- **Conditional exact pinning.** If `j` is in the list-decoding lattice (the open lower bound) and
the base code overflows the budget at `j+1` (the proven upper bound), then the genuine threshold is
exactly `j`. The only missing ingredient is membership at the critical index — the prize. -/
theorem listLatticeThreshold_eq_of_mem_of_overflow_succ
    {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C : Set (ι → F)) {m j : ℕ} [NeZero m] {ε_star : ℝ≥0}
    (hmem : j ∈ GrandChallenges.listLatticeSet C m ε_star)
    (hover : (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        < (Lambda C ((((j + 1 : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal))
    (hne : (GrandChallenges.listLatticeSet C m ε_star).Nonempty) :
    GrandChallenges.listLatticeThreshold C m ε_star hne = j := by
  have hlo : j ≤ GrandChallenges.listLatticeThreshold C m ε_star hne := by
    rw [GrandChallenges.listLatticeThreshold]
    exact Finset.le_max' _ _ hmem
  have hhi : GrandChallenges.listLatticeThreshold C m ε_star hne < j + 1 :=
    listLatticeThreshold_lt_of_overflow C (m := m) (j := j + 1) hover hne
  omega

#print axioms listLatticeThreshold_eq_of_mem_of_overflow_succ

end ProximityGap
