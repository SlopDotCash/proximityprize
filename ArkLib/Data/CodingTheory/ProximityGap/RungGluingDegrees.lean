/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungGluing

/-!
# Gluing degree collapse (#371, rung): all class products share their top

From `gluing_eq_above_k` (the products of any two classes share every
coefficient from `k` up), when one product has degree ≥ `k` ALL of them
do, with the SAME degree and the SAME leading coefficient
(`gluing_equal_natDegree`, `gluing_equal_leadingCoeff`).  Consequently
`aⱼ + deg hⱼ` is one number `D` across all classes of a stack: agreement
sets and factor degrees trade off exactly — the first quantitative tooth
of the 3-class collapse (bigger `A` ⟹ smaller `h` ⟹ fewer h-roots and a
thinner reservoir correction, uniformly across classes).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section GluingDegrees

variable {dom : Fin n ↪ F} {R₁ q₁ q₂ h₁ h₂ : F[X]}

/-- **Equal degrees**: when the cross difference is low-degree and one
product reaches degree `k`, both products have the same `natDegree`. -/
theorem gluing_equal_natDegree {k : ℕ} {A₁ A₂ : Finset (Fin n)}
    (hq : (q₂ - q₁).natDegree < k)
    (hfac₁ : R₁ - q₁ = vanishingPoly dom A₁ * h₁)
    (hfac₂ : R₁ - q₂ = vanishingPoly dom A₂ * h₂)
    (hD : k ≤ (vanishingPoly dom A₁ * h₁).natDegree) :
    (vanishingPoly dom A₁ * h₁).natDegree
      = (vanishingPoly dom A₂ * h₂).natDegree := by
  have hcoe := gluing_eq_above_k hq hfac₁ hfac₂
  set P₁ := vanishingPoly dom A₁ * h₁
  set P₂ := vanishingPoly dom A₂ * h₂
  have hne₁ : P₁ ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hD
    omega
  -- P₂'s coefficient at deg P₁ equals P₁'s leading coefficient ≠ 0
  have hlead : P₂.coeff P₁.natDegree ≠ 0 := by
    rw [← hcoe P₁.natDegree hD]
    exact leadingCoeff_ne_zero.mpr hne₁
  have hle₁ : P₁.natDegree ≤ P₂.natDegree := le_natDegree_of_ne_zero hlead
  -- conversely every P₂-coefficient above deg P₁ vanishes
  have hle₂ : P₂.natDegree ≤ P₁.natDegree := by
    by_contra hgt
    push_neg at hgt
    have hcz : P₂.coeff P₂.natDegree = 0 := by
      rw [← hcoe P₂.natDegree (by omega)]
      exact coeff_eq_zero_of_natDegree_lt hgt
    have hne₂ : P₂ ≠ 0 := by
      intro h0
      rw [h0, natDegree_zero] at hgt
      omega
    exact (leadingCoeff_ne_zero.mpr hne₂) hcz
  omega

/-- **Equal leading coefficients** (same hypotheses). -/
theorem gluing_equal_leadingCoeff {k : ℕ} {A₁ A₂ : Finset (Fin n)}
    (hq : (q₂ - q₁).natDegree < k)
    (hfac₁ : R₁ - q₁ = vanishingPoly dom A₁ * h₁)
    (hfac₂ : R₁ - q₂ = vanishingPoly dom A₂ * h₂)
    (hD : k ≤ (vanishingPoly dom A₁ * h₁).natDegree) :
    (vanishingPoly dom A₁ * h₁).leadingCoeff
      = (vanishingPoly dom A₂ * h₂).leadingCoeff := by
  have hdeg := gluing_equal_natDegree hq hfac₁ hfac₂ hD
  have hcoe := gluing_eq_above_k hq hfac₁ hfac₂
  rw [leadingCoeff, leadingCoeff, ← hdeg]
  exact hcoe _ hD

end GluingDegrees

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.gluing_equal_natDegree
#print axioms ProximityGap.WBPencil.gluing_equal_leadingCoeff
