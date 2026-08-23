/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungClassPartition

/-!
# Off-point pinning (#371, rung): the per-class candidate map

The first of the three coupling laws required for the class-coexistence
count (the bookkeeping-insufficiency note in the KB).  Within a frame
class `(A, h, r)` with `A` maximal, the factor `Φ = m_A·h` does not vanish
at any domain point off `A`, so every member's scalar is PINNED at every
point of its off-part:

* `class_offpoint_phi_ne_zero` — `Φ(x) ≠ 0` off a maximal `A`;
* `class_member_gamma_pinned` — `γ·Φ(x) = −(R₀−r)(x)` at every off-point;
* `class_offpart_ratio_constant` — multi-point off-parts force the
  cross-multiplied ratio constancy (a stack constraint, division-free);
* `cross_class_collision_pencil` — equal scalars realized in two classes
  at points `x, y` put both points on the zero set of the rank-2 pencil
  `Ψ = (R₀−r₁)·(R₁−q₂) − (R₀−r₂)·(R₁−q₁)` — the collision locus of the
  two candidate maps (expanding: `R₀·Δq − R₁·Δr + (r₁q₂ − r₂q₁)`).

Probe match: the pencil's rotating cross-points and the 2-block's
`γ_x = −f(x)` table are exactly images of these candidate maps.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section OffPointPinning

variable {dom : Fin n ↪ F} {R₀ R₁ q r h : F[X]}

/-- Off a maximal agreement set the class factor does not vanish. -/
theorem class_offpoint_phi_ne_zero {A : Finset (Fin n)}
    (hA : ∀ i, i ∈ A ↔ R₁.eval (dom i) = q.eval (dom i))
    (hfac : R₁ - q = vanishingPoly dom A * h)
    {i : Fin n} (hiA : i ∉ A) :
    (vanishingPoly dom A * h).eval (dom i) ≠ 0 := by
  intro h0
  rw [eval_mul] at h0
  rcases mul_eq_zero.mp h0 with hm | hh
  · exact hiA ((vanishingPoly_eval_eq_zero_iff dom).mp hm)
  · exact maximal_agreement_offA_no_root hA hfac i hiA hh

/-- **The pinning law**: a class member's scalar satisfies
`γ·Φ(x) = −(R₀−r)(x)` at every point of its off-part. -/
theorem class_member_gamma_pinned {γ : F} {g : F[X]}
    {A S : Finset (Fin n)}
    (hid : (R₀ - r) + C γ * (vanishingPoly dom A * h)
      = g * vanishingPoly dom S)
    {i : Fin n} (hiS : i ∈ S) :
    γ * (vanishingPoly dom A * h).eval (dom i)
      = -((R₀ - r).eval (dom i)) := by
  have hev := congrArg (Polynomial.eval (dom i)) hid
  rw [eval_mul, vanishingPoly_eval_eq_zero dom hiS, mul_zero] at hev
  simp only [eval_add, eval_mul, eval_C] at hev ⊢
  linear_combination hev

/-- **Ratio constancy**: a member whose off-part contains two points
imposes the division-free cross-ratio constraint on the stack. -/
theorem class_offpart_ratio_constant {γ : F} {g : F[X]}
    {A S : Finset (Fin n)}
    (hid : (R₀ - r) + C γ * (vanishingPoly dom A * h)
      = g * vanishingPoly dom S)
    {i j : Fin n} (hiS : i ∈ S) (hjS : j ∈ S)
    (hA : ∀ i, i ∈ A ↔ R₁.eval (dom i) = q.eval (dom i))
    (hfac : R₁ - q = vanishingPoly dom A * h)
    (hiA : i ∉ A) :
    (R₀ - r).eval (dom i) * (vanishingPoly dom A * h).eval (dom j)
      = (R₀ - r).eval (dom j) * (vanishingPoly dom A * h).eval (dom i) := by
  have hpi := class_member_gamma_pinned hid hiS
  have hpj := class_member_gamma_pinned hid hjS
  have hne := class_offpoint_phi_ne_zero hA hfac hiA
  -- γ = −(R₀−r)(xᵢ)/Φ(xᵢ); substitute into the j-equation
  have hγ : γ = -((R₀ - r).eval (dom i)) *
      ((vanishingPoly dom A * h).eval (dom i))⁻¹ := by
    field_simp
    linear_combination hpi
  rw [hγ] at hpj
  field_simp at hpj
  linear_combination -hpj

/-- **The cross-class collision pencil**: if scalars of two classes
coincide (`γ` realized in both), then at every off-point of each witness
the rank-2 pencil `Ψ = (R₀−r₁)·(R₁−q₂) − (R₀−r₂)·(R₁−q₁)` vanishes. -/
theorem cross_class_collision_pencil {γ : F} {g₁ g₂ h₁ h₂ r₁ r₂ q₁ q₂ : F[X]}
    {A₁ A₂ S₁ S₂ : Finset (Fin n)}
    (hA₁ : ∀ i, i ∈ A₁ ↔ R₁.eval (dom i) = q₁.eval (dom i))
    (hA₂ : ∀ i, i ∈ A₂ ↔ R₁.eval (dom i) = q₂.eval (dom i))
    (hfac₁ : R₁ - q₁ = vanishingPoly dom A₁ * h₁)
    (hfac₂ : R₁ - q₂ = vanishingPoly dom A₂ * h₂)
    (hid₁ : (R₀ - r₁) + C γ * (vanishingPoly dom A₁ * h₁)
      = g₁ * vanishingPoly dom S₁)
    (hid₂ : (R₀ - r₂) + C γ * (vanishingPoly dom A₂ * h₂)
      = g₂ * vanishingPoly dom S₂)
    {i : Fin n} (hiS : i ∈ S₁ ∩ S₂) :
    ((R₀ - r₁) * (R₁ - q₂) - (R₀ - r₂) * (R₁ - q₁)).eval (dom i) = 0 := by
  rw [Finset.mem_inter] at hiS
  have hp₁ := class_member_gamma_pinned hid₁ hiS.1
  have hp₂ := class_member_gamma_pinned hid₂ hiS.2
  rw [← hfac₁] at hp₁
  rw [← hfac₂] at hp₂
  simp only [eval_sub, eval_mul]
  have e₁ : γ * (R₁.eval (dom i) - q₁.eval (dom i))
      = -(R₀.eval (dom i) - r₁.eval (dom i)) := by
    have := hp₁
    simp only [eval_sub] at this
    linear_combination this
  have e₂ : γ * (R₁.eval (dom i) - q₂.eval (dom i))
      = -(R₀.eval (dom i) - r₂.eval (dom i)) := by
    have := hp₂
    simp only [eval_sub] at this
    linear_combination this
  linear_combination (R₁.eval (dom i) - q₂.eval (dom i)) * e₁
    - (R₁.eval (dom i) - q₁.eval (dom i)) * e₂

end OffPointPinning

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.class_offpoint_phi_ne_zero
#print axioms ProximityGap.WBPencil.class_member_gamma_pinned
#print axioms ProximityGap.WBPencil.class_offpart_ratio_constant
#print axioms ProximityGap.WBPencil.cross_class_collision_pencil
