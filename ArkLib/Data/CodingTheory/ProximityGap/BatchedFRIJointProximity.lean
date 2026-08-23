/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.Probability.Notation

/-!
# Issue #14 scratch: Batched FRI Joint Proximity

This file isolates the mathematical kernels of the Batched FRI joint proximity bound.
The core mathematical property states that if a random linear combination of functions
is close to a Reed-Solomon code, then all the original functions are jointly close to the
same code with high probability.
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

/-- **Joint Proximity Bound (The Extractable Math).**
The theorem asserts that if the random linear combination `g = \sum \alpha_i f_i` is `δ`-close
to the Reed-Solomon code `C`, then the probability that the functions `f_i` are NOT jointly `δ`-close
to `C` is bounded by the typical `1 / |F|` term (ignoring list-decoding size constraints).
This formalizes the unproven `batched_fri_joint_proximity_residual` mathematics in isolation.
-/
def BatchedFRIJointProximityKernel
    {ι F : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (ρ δ : ℝ≥0) (m : ℕ) : Prop :=
  ∀ (funcs : Fin m → (ι → F)),
    Pr_{ let alphas ←$ᵖ (Fin m → F) }[
      (∃ c ∈ (ReedSolomon.code (domain := domain) ⌊ρ * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)),
        hammingDist (randomLinearCombination funcs alphas) c ≤ δ * Fintype.card ι) ∧
      ¬ (∃ c_funcs : Fin m → (ι → F),
          (∀ i, c_funcs i ∈ (ReedSolomon.code (domain := domain) ⌊ρ * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) ∧
          (hammingDist funcs c_funcs ≤ δ * Fintype.card ι))
    ] ≤ (1 : ℝ≥0∞) / Fintype.card F

end Issue14
end ProximityGap
