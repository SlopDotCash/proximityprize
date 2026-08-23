/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.InterleavedLambdaGe
import ArkLib.Data.CodingTheory.ProximityGap.Lattice

/-!
# Base-code overflow sharpens the threshold past capacity, at every arity (#232)

General-`m` form of `listLatticeThreshold_lt_of_overflow_fin_one`: the interleaving lower bound
`Lambda_interleaved_ge` (`Λ C δ ≤ Λ(C^⋈Fin m, δ)`) suffices — no equality needed — to push a
base-code overflow through the faithful lattice at any arity `m ≠ 0`:

  `listLatticeThreshold_lt_of_overflow` — if `Λ(C, j/n) > ε*·|F|`, then
  `listLatticeThreshold C m ε* < j`.

Every lattice member `t` has `Λ(C^⋈Fin m, t/n) ≤ ε*·|F|`; if `j ≤ t` then
`Λ(C, j/n) ≤ Λ(C, t/n) ≤ Λ(C^⋈Fin m, t/n) ≤ ε*·|F|` (monotonicity + interleaving lower bound),
contradicting the overflow. So all members are `< j` and `max' < j`.

Composed with the capacity-exponent overflow `rs_lambda_gt_of_capExp_overflow`, this caps `δ*` at the
list-decoding capacity `δ_LD = H_q⁻¹(1 − ρ) < 1 − ρ` for **every** column count `m`, not just `m = 1`.
Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open ListDecodable

/-- **Base-code overflow pushes the threshold below `j`, at every arity.** If `Λ(C, j/n)` already
exceeds the budget `ε*·|F|`, then for any `m ≠ 0` the faithful list-decoding lattice threshold is
strictly below `j`. -/
theorem listLatticeThreshold_lt_of_overflow
    {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C : Set (ι → F)) {m j : ℕ} [NeZero m] {ε_star : ℝ≥0}
    (hover : (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        < (Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal))
    (hne : (GrandChallenges.listLatticeSet C m ε_star).Nonempty) :
    GrandChallenges.listLatticeThreshold C m ε_star hne < j := by
  classical
  rw [GrandChallenges.listLatticeThreshold, Finset.max'_lt_iff]
  intro t ht
  rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range] at ht
  obtain ⟨htn, htle⟩ := ht
  rw [Code.interleavedCode_eq_interleavedCodeSet] at htle
  by_contra hjt
  push_neg at hjt
  have hjt' : (j : ℝ≥0) ≤ (t : ℝ≥0) := by exact_mod_cast hjt
  have hrad : (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
      ≤ (((t : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) := by
    have h1 : ((j : ℝ≥0) / (Fintype.card ι : ℝ≥0)) ≤ ((t : ℝ≥0) / (Fintype.card ι : ℝ≥0)) := by
      gcongr
    exact_mod_cast h1
  have hLmono : Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
      ≤ Lambda C (((t : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) := Lambda_mono hrad
  have hge := InterleavedCode.ListSize.Lambda_interleaved_ge (C := C) (m := m)
    (((t : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
  have hle : (Lambda C (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal)
      ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal) :=
    le_trans (by exact_mod_cast (le_trans hLmono hge)) htle
  exact absurd hle (not_le.mpr hover)

#print axioms listLatticeThreshold_lt_of_overflow

end ProximityGap
