/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungGluingDegrees

/-!
# The class factor family (#371, rung): all factor products are
low-degree-congruent

The structural input that makes the class-packing count tractable — and is
strictly stronger than Fisher on the agreement sets (which the KB
insufficiency note shows leaves the count at ~280, not ≤ 30).  Through the
direction row every two classes are coupled: by `class_gluing_equation`
the factor products differ by the LOW-DEGREE cross difference,

  `Φᵢ − Φⱼ = qⱼ − qᵢ`,  `deg(qⱼ − qᵢ) < k`,

so (`class_factors_share_coeff_above`) all `Φⱼ` share every coefficient
from `k` upward: fixing one class's factor product `Φ₁`, the whole family
lives in the affine space `Φ₁ + {deg < k}` — a `k`-dimensional slice
(here `k = 3`), NOT the full Fisher family of low-degree agreement sets.
This is the coupling that forbids many large classes from coexisting.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section ClassFamily

variable {dom : Fin n ↪ F} {R₁ q₁ q₂ h₁ h₂ : F[X]}

/-- **The factor-difference law**: two classes' factor products differ by
the negated cross difference `q₂ − q₁` — a single direction-row identity. -/
theorem class_factor_difference {A₁ A₂ : Finset (Fin n)}
    (hfac₁ : R₁ - q₁ = vanishingPoly dom A₁ * h₁)
    (hfac₂ : R₁ - q₂ = vanishingPoly dom A₂ * h₂) :
    vanishingPoly dom A₁ * h₁ - vanishingPoly dom A₂ * h₂ = q₂ - q₁ :=
  class_gluing_equation hfac₁ hfac₂

/-- **Affine-family membership**: when the cross difference is degree
`< k`, the two factor products agree in every coefficient `≥ k`; the family
of class factor products lies in one `Φ₁ + {deg < k}` coset. -/
theorem class_factors_share_coeff_above {k : ℕ} {A₁ A₂ : Finset (Fin n)}
    (hq : (q₂ - q₁).natDegree < k)
    (hfac₁ : R₁ - q₁ = vanishingPoly dom A₁ * h₁)
    (hfac₂ : R₁ - q₂ = vanishingPoly dom A₂ * h₂) :
    ∀ t, k ≤ t → (vanishingPoly dom A₁ * h₁).coeff t
      = (vanishingPoly dom A₂ * h₂).coeff t :=
  gluing_eq_above_k hq hfac₁ hfac₂

/-- **The family is small**: the class factor products, shifted by `Φ₁`, all
have degree `< k`; equivalently `Φⱼ − Φ₁` lies in the degree-`< k` space. -/
theorem class_factor_shift_low_degree {k : ℕ} {A₁ A₂ : Finset (Fin n)}
    (hq : (q₂ - q₁).natDegree < k)
    (hfac₁ : R₁ - q₁ = vanishingPoly dom A₁ * h₁)
    (hfac₂ : R₁ - q₂ = vanishingPoly dom A₂ * h₂) :
    (vanishingPoly dom A₂ * h₂ - vanishingPoly dom A₁ * h₁).natDegree < k := by
  have hdiff : vanishingPoly dom A₂ * h₂ - vanishingPoly dom A₁ * h₁
      = q₁ - q₂ := by
    have := class_factor_difference hfac₁ hfac₂
    linear_combination -this
  rw [hdiff]
  have : (q₁ - q₂).natDegree = (q₂ - q₁).natDegree := by
    rw [← natDegree_neg (q₁ - q₂)]
    congr 1
    ring
  omega

end ClassFamily

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.class_factor_difference
#print axioms ProximityGap.WBPencil.class_factors_share_coeff_above
#print axioms ProximityGap.WBPencil.class_factor_shift_low_degree
