/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon
import ProximityPrize.Extensions.Data.CodingTheory.ListDecodability
import ArkLib.Data.Probability.Notation

/-!
# Issue #14 scratch: Batched FRI Joint Proximity

This file isolates the mathematical kernels of the Batched FRI joint proximity bound.
The core mathematical property states that if a random linear combination of functions
is close to a Reed-Solomon code, then, except with probability at most an explicit error `ε`,
the original functions are jointly close to the same code: some codeword tuple agrees with them
outside a common set of at most `δ n` coordinates (column/interleaved distance
`jointColumnDist`, not the number of differing rows). `BatchedFRIJointProximityKernel` is an
unproved `def : Prop` whose `ε` is a parameter.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap
namespace Issue14

open NNReal Code
open scoped ProbabilityTheory BigOperators ENNReal

/-- **Random Linear Combination (RLC).**
Computes the RLC of a list of functions given a list of random coefficients. -/
def randomLinearCombination {ι F : Type} {m : ℕ} [Field F] [Fintype F] [Fintype ι]
    (funcs : Fin m → (ι → F)) (alphas : Fin m → F) : ι → F :=
  fun x => ∑ i : Fin m, alphas i * funcs i x

/-- **Joint (column) Hamming distance** between two stacks of `m` functions: the number of
coordinates `x : ι` at which *some* row differs. This is the Hamming distance of the transposed
stacks `x ↦ (i ↦ funcs i x)` over the alphabet `Fin m → F`, i.e. the interleaved-code distance
used by `InterleavedCode.jointProximityNat` (not the number of differing rows). -/
def jointColumnDist {ι F : Type} [Fintype ι] [DecidableEq F] {m : ℕ}
    (funcs c_funcs : Fin m → (ι → F)) : ℕ :=
  hammingDist (fun x : ι => fun i : Fin m => funcs i x) (fun x : ι => fun i : Fin m => c_funcs i x)

/-- `jointColumnDist` counts the coordinates at which some row differs. -/
theorem jointColumnDist_eq_card {ι F : Type} [Fintype ι] [DecidableEq F] {m : ℕ}
    (funcs c_funcs : Fin m → (ι → F)) :
    jointColumnDist funcs c_funcs
      = (Finset.univ.filter (fun x : ι => ∃ i, funcs i x ≠ c_funcs i x)).card := by
  classical
  unfold jointColumnDist hammingDist
  congr 1
  ext x
  simp [funext_iff]

/-- **Joint Proximity Bound (The Extractable Math), with an explicit error parameter `ε`.**
For every stack `funcs`, the probability over uniform `alphas : Fin m → F` that the random linear
combination `∑ αᵢ fᵢ` is `δ`-close to `RS[⌊ρ n⌋]` while the `fᵢ` are **not jointly** `δ`-close is at
most `ε`. Joint closeness is measured in **columns**: there are codewords `cᵢ` such that the set
of coordinates where some `fᵢ` differs from `cᵢ` has size `≤ δ n` (`jointColumnDist`).

(An earlier version compared the *row* Hamming distance `hammingDist funcs c_funcs` — the number
of rows that differ anywhere — with `δ n`; whenever `m ≤ δ n` that is satisfied by `cᵢ = 0`, so
the kernel was vacuous. It also fixed `ε = 1/|F|`, which is not the known bound.)

The value of `ε` is a hypothesis of the intended batched-FRI theorem, not something claimed here:
correlated-agreement results (BCIKS20) give an `ε` of order `n/|F|` in the unique-decoding regime
`δ < (1−ρ)/2`, and a larger `ε` depending on `n`, `ρ`, `δ` (and the gap to the Johnson radius) in
the list-decoding regime. No instance of this `Prop` is proved in tree; it is an open residual. -/
def BatchedFRIJointProximityKernel
    {ι F : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (ρ δ : ℝ≥0) (m : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ (funcs : Fin m → (ι → F)),
    Pr_{ let alphas ←$ᵖ (Fin m → F) }[
      (∃ c ∈ (ReedSolomon.code (domain := domain) ⌊ρ * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)),
        hammingDist (randomLinearCombination funcs alphas) c ≤ δ * Fintype.card ι) ∧
      ¬ (∃ c_funcs : Fin m → (ι → F),
          (∀ i, c_funcs i ∈
            (ReedSolomon.code (domain := domain) ⌊ρ * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) ∧
          ((jointColumnDist funcs c_funcs : ℝ≥0) ≤ δ * Fintype.card ι))
    ] ≤ ε

end Issue14
end ProximityGap
