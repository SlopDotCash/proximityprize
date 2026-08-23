/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.RandomLinearCodeEquidistribution

/-!
# GLMRSW22 dependent (parallel) message-pair joint probability (second-moment summand)

The pairwise joint probability (`RandomLinearCodePairwiseProb`) covers *linearly independent*
message pairs. The remaining second-moment summands come from *parallel* pairs `m' = c • m`
(`c ∈ F`). For a fixed nonzero `m`, since `(c • m) ᵥ* G = c • (m ᵥ* G)` (`smul_vecMul`) and
`m ᵥ* G` is uniform, the joint event collapses to a single-codeword event:

  `Pr_G[m ᵥ* G ∈ S ∧ (c • m) ᵥ* G ∈ S] = |{ v ∈ S : c • v ∈ S }| / qⁿ`.

This is the exact parallel-pair contribution the GLMRSW22 second moment sums over `c ∈ F⋆`
(issue #79), completing the per-pair second-moment summands alongside the independent-pair term.

## Main result (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `parallel_joint_mem_prob` — the parallel-pair joint hit probability.
-/

namespace ArkLib.RandomLinearCode

open scoped Matrix ENNReal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Parallel-pair second-moment summand.** For a fixed nonzero message `m` and scalar `c`, the
random codewords `m ᵥ* G` and `(c • m) ᵥ* G` land jointly in `S` with probability
`|{v ∈ S : c • v ∈ S}| / qⁿ` — because the second codeword is `c • (m ᵥ* G)`, collapsing the joint
event to a single-codeword membership in `{v | v ∈ S ∧ c • v ∈ S}`. -/
theorem parallel_joint_mem_prob {m : Fin k → F} (hm : m ≠ 0) (c : F) (S : Finset (ι → F)) :
    (PMF.uniformOfFintype (Matrix (Fin k) ι F)).toOuterMeasure
        {G : Matrix (Fin k) ι F | m ᵥ* G ∈ S ∧ (c • m) ᵥ* G ∈ S}
      = (Fintype.card {v : ι → F | v ∈ S ∧ c • v ∈ S} : ℝ≥0∞) / Fintype.card (ι → F) := by
  classical
  have hev : {G : Matrix (Fin k) ι F | m ᵥ* G ∈ S ∧ (c • m) ᵥ* G ∈ S}
      = (fun G : Matrix (Fin k) ι F => m ᵥ* G) ⁻¹' {v : ι → F | v ∈ S ∧ c • v ∈ S} := by
    ext G
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Matrix.smul_vecMul]
  rw [hev, ← PMF.toOuterMeasure_map_apply]
  exact vecMul_uniform_mem_prob hm {v : ι → F | v ∈ S ∧ c • v ∈ S}

end ArkLib.RandomLinearCode

-- Axiom audit.
#print axioms ArkLib.RandomLinearCode.parallel_joint_mem_prob
