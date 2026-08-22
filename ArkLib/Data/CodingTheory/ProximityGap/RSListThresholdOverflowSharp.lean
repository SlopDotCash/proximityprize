/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.InterleavedFinOneEq
import ArkLib.Data.CodingTheory.ProximityGap.Lattice

/-!
# Base-code overflow sharpens the list-decoding threshold past capacity (#232)

`listLatticeThreshold_le_capacity` bounds the genuine threshold by the capacity index `n − k` via a
construction that only exists *at or above* capacity. Using the unary-interleaving equality
`Lambda_interleaved_fin_one_eq` (`Λ(C^⋈Fin 1, δ) = Λ(C, δ)`), a *base-code* list-size lower bound
(overflow) at any radius `j/n` propagates into the faithful lattice and pushes the threshold strictly
below `j`:

  `listLatticeThreshold_lt_of_overflow_fin_one` — if `Λ(C, j/n) > ε*·|F|`, then (for `m = 1`)
  `listLatticeThreshold C 1 ε* < j`.

Composed with the capacity-exponent overflow `rs_lambda_gt_of_capExp_overflow` (`Λ(RS, δ) > ε*·|F|`
whenever `H_q(⌊δn⌋/n) > 1 − ρ`), this tightens the upper bound on `δ*` from the capacity radius
`1 − ρ` down to the **list-decoding capacity** `δ_LD = H_q⁻¹(1 − ρ) < 1 − ρ` — i.e. into the open
Johnson→capacity gap *from above*. Since `δ_LD` is the conjectured value of `δ*`, the remaining open
question is exactly the matching lower bound `δ* ≥ δ_LD` (the prize).

The proof: every lattice member `t` has `Λ(C^⋈Fin 1, t/n) ≤ ε*·|F|`, hence (equality + `Lambda_mono`)
`Λ(C, j/n) ≤ Λ(C, t/n) ≤ ε*·|F|` whenever `j ≤ t`, contradicting the overflow; so all members are
`< j` and `max' < j`. Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open ListDecodable

/-- **Base-code overflow pushes the threshold below `j`.** For single-column interleaving (`m = 1`),
if the base Reed–Solomon-style list `Λ(C, j/n)` already exceeds the budget `ε*·|F|`, then the
faithful list-decoding lattice threshold is strictly below `j`. -/
theorem listLatticeThreshold_lt_of_overflow_fin_one
    {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C : Set (ι → F)) {j : ℕ} {ε_star : ℝ≥0}
    (hover : (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        < (Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal))
    (hne : (GrandChallenges.listLatticeSet C 1 ε_star).Nonempty) :
    GrandChallenges.listLatticeThreshold C 1 ε_star hne < j := by
  classical
  rw [GrandChallenges.listLatticeThreshold, Finset.max'_lt_iff]
  intro t ht
  rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range] at ht
  obtain ⟨htn, htle⟩ := ht
  by_contra hjt
  push_neg at hjt
  have hjt' : (j : ℝ≥0) ≤ (t : ℝ≥0) := by exact_mod_cast hjt
  -- radius monotonicity `j/n ≤ t/n`
  have hrad : (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
      ≤ (((t : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) := by
    have h1 : ((j : ℝ≥0) / (Fintype.card ι : ℝ≥0)) ≤ ((t : ℝ≥0) / (Fintype.card ι : ℝ≥0)) := by
      gcongr
    exact_mod_cast h1
  have hLmono : Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
      ≤ Lambda C (((t : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) := Lambda_mono hrad
  -- the lattice's `C ^⋈ Fin 1` is defeq to `interleavedCodeSet (Fin 1) C`, so the unary equality
  -- applies and turns the interleaved cap into the base cap
  have heq2 : Lambda (C ^⋈ (Fin 1)) (((t : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
      = Lambda C (((t : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) :=
    InterleavedCode.ListSize.Lambda_interleaved_fin_one_eq C _
  have hstep : Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
      ≤ Lambda (C ^⋈ (Fin 1)) (((t : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) := by
    rw [heq2]; exact hLmono
  have hle : (Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal)
      ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal) :=
    le_trans (by exact_mod_cast hstep) htle
  exact absurd hle (not_le.mpr hover)

#print axioms listLatticeThreshold_lt_of_overflow_fin_one

end ProximityGap
