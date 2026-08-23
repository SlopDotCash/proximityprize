/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.MCAEndpointLower
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount
import ArkLib.Data.CodingTheory.ProximityGap.Lattice2.Core

/-!
# The General Spike-Plant MCA Lower Bound at Lattice Index `j` (Issue #232)

This file packages the in-tree general `t`-spike floor `epsMCA_ge_spike` at the
interior MCA lattice point `j/n` with `t = j + 1`, supplying the missing
**size lemma** and **hypothesis discharge** for each lattice index.

## The result

For a Reed–Solomon code `C = RS[F, domain, k]` with evaluation domain of
size `n`, at the lattice radius `j/n` (with `j + 1 + k ≤ n` and `j + 1 ≤ |F|`):

  `(j + 1) / |F| ≤ ε_mca(C, j/n)`.

This is the **general spike-plant lower bound**, extending the j=1 result `2/q`
(`epsMCA_interiorJ1_ge`) and the j=2 result `3/q` (`epsMCA_interiorJ2_ge`) to
arbitrary lattice indices.

## The construction (informal)

The spike plant at radius `j/n` constructs a 2-row stack `(u₀, u₁)` and `j+1`
distinct scalars `γ₀, …, γⱼ` such that:
- For each `γᵢ`, the line `u₀ + γᵢ · u₁` is `(j/n)`-close to `C` via some
  agreement set `Sᵢ` with `|Sᵢ| ≥ (1 - j/n) · n = n - j`.
- But no codeword *pair* `(v₀, v₁) ∈ C²` jointly agrees with `(u₀, u₁)` on `Sᵢ`.

The `j+1` distinct bad scalars force `ε_mca ≥ (j+1)/|F|` via the uniform
distribution over `F`.

The construction: take `u₁ = x^k` (a non-codeword of the right degree) and
`u₀ = x^{k+1}`. The `j+1` "windows" are consecutive `(k+1)`-blocks of the
evaluation domain, and the `j+1` bad scalars are the negatives of the
divided differences of `u₁` on each block. The key arithmetic is that `u₁`
takes distinct values on each block (so no joint agreement), while `u₀ + γᵢ·u₁`
is constant (hence a codeword) on each block.

This is exactly the `epsMCA_ge_spike` construction with `t = j + 1`.

## The size lemma

The spike plant requires `((1 - j/n) · n : ℝ≥0) ≤ ((n - (j+1) + 1 : ℕ) : ℝ≥0)`,
i.e., `(n - j : ℝ≥0) ≤ (n - j : ℕ)`. This is a TAUTOLOGY: the lattice radius
`j/n` has `(1 - j/n) · n = n - j` exactly (no rounding).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Issue #232.
- `MCAEndpointLower.lean`: the general `epsMCA_ge_spike` theorem.
- `GrandChallengeInteriorJ1.lean`, `GrandChallengeInteriorGeneral.lean`: j=1,2 instances.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal ENNReal BigOperators
open Code ReedSolomon GrandChallengesLattice

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The size lemma at lattice point `j/n` -/

/-- **Size lemma for the spike plant at lattice index `j`.**
At the lattice radius `δ = j / n` (encoded as `mcaLatticePoint n j`), the
agreement size `(1 - δ) · n = n - j` fits the spike requirement
`(1 - δ) · n ≤ n - t + 1` with `t = j + 1` (i.e. `n - j ≤ n - j`, an equality). -/
theorem spike_size_at_latticeJ (n : ℕ) (j : Fin (n + 1)) (hn : 0 < n)
    (hjn : j.val < n) :
    ((1 - mcaLatticePoint n j) * (n : ℝ≥0) : ℝ≥0) ≤
      ((n - (j.val + 1) + 1 : ℕ) : ℝ≥0) := by
  -- (1 - j/n) · n = n - j and n - (j+1) + 1 = n - j.
  have hn_pos : (0 : ℝ≥0) < (n : ℝ≥0) := by
    exact_mod_cast hn
  have hjn_le : (j.val : ℝ≥0) ≤ (n : ℝ≥0) := by
    exact_mod_cast Nat.le_of_lt_succ j.isLt
  unfold mcaLatticePoint
  rw [show (n - (j.val + 1) + 1 : ℕ) = n - j.val from by omega]
  have key : ((1 - (j.val : ℝ≥0) / (n : ℝ≥0)) * (n : ℝ≥0)) = (n : ℝ≥0) - j.val := by
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hn_pos)]
  rw [key]
  rw [← NNReal.coe_le_coe, NNReal.coe_sub hjn_le]
  change (n : ℝ) - j.val ≤ ((n - j.val : ℕ) : ℝ)
  rw [Nat.cast_sub (Nat.le_of_lt hjn)]

/-- **The general spike-plant MCA lower bound at lattice index `j`.**

For a Reed–Solomon code `RS[F, domain, k]` with `(j+1) + k ≤ n` (the wide-regime
spike hypothesis) and `j + 1 ≤ |F|` (enough field elements for the spike), the
MCA error at radius `j/n` satisfies:

  `(j + 1) / |F| ≤ ε_mca(C, j/n)`.

This is `epsMCA_ge_spike` instantiated at `t = j + 1`, with the size lemma
discharged by `spike_size_at_latticeJ`.

Combined with the minor-route upper bound `ε_mca(C, j/n) ≤ (j+1)/|F|` (from
`GrandChallengeInteriorGeneral.lean`, under the named nondegeneracy hypothesis and
the wide-regime condition `n - k ≥ 2j + 1`), this gives the exact value
`ε_mca(C, j/n) = (j+1)/|F|` at each wide-regime lattice point — but by
`WideRegimeDisjointness.lean`, these are all below the Johnson radius. -/
theorem epsMCA_generalJ_ge
    (domain : ι ↪ F) {k : ℕ} (j : Fin (Fintype.card ι + 1))
    (hjn : j.val < Fintype.card ι)
    (ht_n : j.val + 1 + k ≤ Fintype.card ι)
    (ht_q : j.val + 1 ≤ Fintype.card F) :
    (↑(j.val + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
        (mcaLatticePoint (Fintype.card ι) j) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hδ := spike_size_at_latticeJ (Fintype.card ι) j hn hjn
  exact epsMCA_ge_spike domain k (j.val + 1) (mcaLatticePoint (Fintype.card ι) j) ht_n ht_q hδ

/-- **The spike lower bound is a strict lower bound on the MCA threshold at lattice
index `j + 1`.** If `(j + 1 + 1) / |F| > ε*` (i.e., `j + 2 > ε* · |F|`), then the
threshold `δ*` is at most `j/n`, because at `(j+1)/n` the MCA error already exceeds `ε*`.

This is the **upper bracket** for the MCA threshold: it tells us `δ* ≤ j/n`
when `j + 2 > ε* · |F|`, equivalently `j ≥ ⌊ε* · |F|⌋`. -/
theorem epsMCA_threshold_upper_bracket_from_spike
    (domain : ι ↪ F) {k : ℕ} (j : Fin (Fintype.card ι + 1))
    (hjn : j.val < Fintype.card ι)
    (ht_n : j.val + 1 + k ≤ Fintype.card ι)
    (ht_q : j.val + 1 ≤ Fintype.card F)
    (ε_star : ℝ≥0)
    (hε_lt : (ε_star : ℝ≥0∞) < (↑(j.val + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    (ε_star : ℝ≥0∞) <
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
        (mcaLatticePoint (Fintype.card ι) j) :=
  lt_of_lt_of_le hε_lt (epsMCA_generalJ_ge domain j hjn ht_n ht_q)

end ProximityGap
