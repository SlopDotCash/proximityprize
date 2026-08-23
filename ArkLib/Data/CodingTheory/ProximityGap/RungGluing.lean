/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungCollisionDichotomy

/-!
# The gluing equation (#371, rung): coupling law 2, the certain core

Two frame classes of one stack are glued through the direction row:
subtracting the factorizations `R₁ − qⱼ = m_{Aⱼ}·hⱼ` gives the EXACT
deg-`< k` equation

  `m_{A₁}·h₁ − m_{A₂}·h₂ = q₂ − q₁`

(`class_gluing_equation`).  Consequences formalized here:
* `gluing_cross_values` — on `A₂` the product `m_{A₁}·h₁` takes the
  values of the degree-`< k` polynomial `q₂ − q₁` (and vice versa): each
  class's factor is pinned to low-degree data on the other class's
  agreement set — the probes' multi-block kernel collapse is the
  numerical shadow of this pinning;
* `gluing_eq_above_k` — the two products agree in every coefficient from
  `k` upward; in particular equal degrees and leading coefficients when
  `deg > k − 1` (`natDegree`/`leadingCoeff` corollary shape, coefficient
  form, no casework).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section Gluing

variable {dom : Fin n ↪ F} {R₁ q₁ q₂ h₁ h₂ : F[X]}

/-- **The gluing equation**: two class factorizations of the same
direction row subtract to the low-degree cross difference. -/
theorem class_gluing_equation {A₁ A₂ : Finset (Fin n)}
    (hfac₁ : R₁ - q₁ = vanishingPoly dom A₁ * h₁)
    (hfac₂ : R₁ - q₂ = vanishingPoly dom A₂ * h₂) :
    vanishingPoly dom A₁ * h₁ - vanishingPoly dom A₂ * h₂ = q₂ - q₁ := by
  linear_combination hfac₂ - hfac₁

/-- **Cross-value pinning**: on the other class's agreement set, each
factor product evaluates to the low-degree cross difference. -/
theorem gluing_cross_values {A₁ A₂ : Finset (Fin n)}
    (hfac₁ : R₁ - q₁ = vanishingPoly dom A₁ * h₁)
    (hfac₂ : R₁ - q₂ = vanishingPoly dom A₂ * h₂) :
    ∀ i ∈ A₂, (vanishingPoly dom A₁ * h₁).eval (dom i)
      = (q₂ - q₁).eval (dom i) := by
  intro i hi
  have hglue := class_gluing_equation hfac₁ hfac₂
  have hev := congrArg (Polynomial.eval (dom i)) hglue
  simp only [eval_sub, eval_mul] at hev ⊢
  rw [vanishingPoly_eval_eq_zero dom hi, zero_mul, sub_zero] at hev
  exact hev

/-- **Coefficient agreement above the budget**: the two factor products
share every coefficient from `k` upward whenever the cross difference has
degree `< k` — the gluing freezes both products' high parts together. -/
theorem gluing_eq_above_k {k : ℕ} {A₁ A₂ : Finset (Fin n)}
    (hq : (q₂ - q₁).natDegree < k)
    (hfac₁ : R₁ - q₁ = vanishingPoly dom A₁ * h₁)
    (hfac₂ : R₁ - q₂ = vanishingPoly dom A₂ * h₂) :
    ∀ t, k ≤ t → (vanishingPoly dom A₁ * h₁).coeff t
      = (vanishingPoly dom A₂ * h₂).coeff t := by
  intro t ht
  have hglue := class_gluing_equation hfac₁ hfac₂
  have hc := congrArg (fun p : F[X] => p.coeff t) hglue
  dsimp only at hc
  have hz : (q₂ - q₁).coeff t = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hq ht)
  rw [hz, coeff_sub] at hc
  exact sub_eq_zero.mp hc

end Gluing

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.class_gluing_equation
#print axioms ProximityGap.WBPencil.gluing_cross_values
#print axioms ProximityGap.WBPencil.gluing_eq_above_k
