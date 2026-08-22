/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungPoolSpan

/-!
# The top-cancellation law (#371, rung): high-degree direction rows

For rows whose direction interpolant outdegrees the witness budget, the
identity's top coefficient pins the scalar: `coeff_d(R₀) + γ·lead(R₁) = 0` at
`d = deg R₁` since every other term lives below.  At most ONE bad scalar —
the general-stack stratum of `SubCeilingInteriorCeiling` with
`deg R₁ > deg g + |S|` is closed by `top_cancellation_unique`.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **Top cancellation**: when both defect data sit strictly below
`deg R₁`, the scalar is pinned by the leading coefficient — two bad scalars
coincide. -/
theorem top_cancellation_unique {dom : Fin n ↪ F} {R₀ R₁ : F[X]}
    {γ₁ γ₂ : F} {P₁ P₂ g₁ g₂ : F[X]} {S₁ S₂ : Finset (Fin n)}
    (hd₁ : (g₁ * vanishingPoly dom S₁).natDegree < R₁.natDegree)
    (hd₂ : (g₂ * vanishingPoly dom S₂).natDegree < R₁.natDegree)
    (hP₁ : P₁.natDegree < R₁.natDegree) (hP₂ : P₂.natDegree < R₁.natDegree)
    (hR₀ : R₀.natDegree < R₁.natDegree)
    (hid₁ : R₀ + C γ₁ * R₁ - P₁ = g₁ * vanishingPoly dom S₁)
    (hid₂ : R₀ + C γ₂ * R₁ - P₂ = g₂ * vanishingPoly dom S₂) :
    γ₁ = γ₂ := by
  have hR₁ne : R₁ ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hR₀
    omega
  have hc₁ := congrArg (fun q : F[X] => q.coeff R₁.natDegree) hid₁
  have hc₂ := congrArg (fun q : F[X] => q.coeff R₁.natDegree) hid₂
  simp only [coeff_sub, coeff_add, coeff_C_mul] at hc₁ hc₂
  rw [coeff_eq_zero_of_natDegree_lt hP₁,
    coeff_eq_zero_of_natDegree_lt hd₁,
    coeff_eq_zero_of_natDegree_lt hR₀] at hc₁
  rw [coeff_eq_zero_of_natDegree_lt hP₂,
    coeff_eq_zero_of_natDegree_lt hd₂,
    coeff_eq_zero_of_natDegree_lt hR₀] at hc₂
  have hlead : R₁.coeff R₁.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hR₁ne
  have h₁ : γ₁ * R₁.coeff R₁.natDegree = 0 := by linear_combination hc₁
  have h₂ : γ₂ * R₁.coeff R₁.natDegree = 0 := by linear_combination hc₂
  have e₁ : γ₁ = 0 := by
    rcases mul_eq_zero.mp h₁ with h | h
    · exact h
    · exact absurd h hlead
  have e₂ : γ₂ = 0 := by
    rcases mul_eq_zero.mp h₂ with h | h
    · exact h
    · exact absurd h hlead
  rw [e₁, e₂]

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.top_cancellation_unique
