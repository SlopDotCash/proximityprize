/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungGluingDegrees

/-!
# The cross-restriction law (#371, rung): candidate maps are low-degree
on other classes' frames

The formal version of the probes' `f = −Δr/Δq` cross function (the 2-block
record's 12 cross scalars are its image).  A class-1 member whose off-part
touches a point where class 2's agreement AND frame both hold has its
scalar pinned by the LOW-DEGREE data alone:

  `γ·(q₂−q₁)(x) = −(r₂−r₁)(x)`

(`cross_restriction_pinned`).  Two consequences land here:
* `cross_restriction_root` — such a point lies on the deg `< k` pencil
  member `(r₂−r₁) + γ·(q₂−q₁)`;
* `cross_restriction_card_le` — for a FIXED scalar, the set of such
  points is at most `k−1` unless the pencil member vanishes identically
  (the level-set cap: each cross-γ is served by ≤ `k−1` frame points —
  at the rung, ≤ 2).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section CrossRestriction

variable {dom : Fin n ↪ F} {R₀ R₁ q₁ q₂ r₁ r₂ h₁ h₂ : F[X]}

/-- **Cross-restriction pinning**: at a point of class 2's agreement set
where class 2's frame also holds, a class-1 member's pinning relation
reduces to the low-degree data `γ·Δq(x) = −Δr(x)`. -/
theorem cross_restriction_pinned {γ : F} {g : F[X]} {A₁ A₂ S : Finset (Fin n)}
    (hfac₁ : R₁ - q₁ = vanishingPoly dom A₁ * h₁)
    (hfac₂ : R₁ - q₂ = vanishingPoly dom A₂ * h₂)
    (hid : (R₀ - r₁) + C γ * (vanishingPoly dom A₁ * h₁)
      = g * vanishingPoly dom S)
    {i : Fin n} (hiS : i ∈ S) (hiA₂ : i ∈ A₂)
    (hfr₂ : R₀.eval (dom i) = r₂.eval (dom i)) :
    γ * (q₂ - q₁).eval (dom i) = -((r₂ - r₁).eval (dom i)) := by
  have hpin := class_member_gamma_pinned hid hiS
  have hcross := gluing_cross_values hfac₁ hfac₂ i hiA₂
  rw [hcross] at hpin
  simp only [eval_sub] at hpin ⊢
  rw [hfr₂] at hpin
  linear_combination hpin

/-- Such a point is a root of the deg-`< k` pencil member
`(r₂−r₁) + C γ·(q₂−q₁)`. -/
theorem cross_restriction_root {γ : F} {g : F[X]} {A₁ A₂ S : Finset (Fin n)}
    (hfac₁ : R₁ - q₁ = vanishingPoly dom A₁ * h₁)
    (hfac₂ : R₁ - q₂ = vanishingPoly dom A₂ * h₂)
    (hid : (R₀ - r₁) + C γ * (vanishingPoly dom A₁ * h₁)
      = g * vanishingPoly dom S)
    {i : Fin n} (hiS : i ∈ S) (hiA₂ : i ∈ A₂)
    (hfr₂ : R₀.eval (dom i) = r₂.eval (dom i)) :
    ((r₂ - r₁) + C γ * (q₂ - q₁)).eval (dom i) = 0 := by
  have h := cross_restriction_pinned hfac₁ hfac₂ hid hiS hiA₂ hfr₂
  simp only [eval_add, eval_mul, eval_C]
  linear_combination h

/-- **The level-set cap**: for a fixed scalar with nondegenerate pencil
member, at most `k−1` frame points of another class can serve it. -/
theorem cross_restriction_card_le {k : ℕ} (hk : 1 ≤ k) {γ : F} {g : F[X]}
    {A₁ A₂ S T : Finset (Fin n)}
    (hdq : (q₂ - q₁).natDegree < k) (hdr : (r₂ - r₁).natDegree < k)
    (hpne : (r₂ - r₁) + C γ * (q₂ - q₁) ≠ 0)
    (hfac₁ : R₁ - q₁ = vanishingPoly dom A₁ * h₁)
    (hfac₂ : R₁ - q₂ = vanishingPoly dom A₂ * h₂)
    (hid : (R₀ - r₁) + C γ * (vanishingPoly dom A₁ * h₁)
      = g * vanishingPoly dom S)
    (hT : ∀ i ∈ T, i ∈ S ∧ i ∈ A₂ ∧ R₀.eval (dom i) = r₂.eval (dom i)) :
    T.card ≤ k - 1 := by
  classical
  have hdvd : vanishingPoly dom T ∣ (r₂ - r₁) + C γ * (q₂ - q₁) :=
    vanishingPoly_dvd_of_eval_zero dom (fun i hi => by
      obtain ⟨h1, h2, h3⟩ := hT i hi
      exact cross_restriction_root hfac₁ hfac₂ hid h1 h2 h3)
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hpne
  rw [vanishingPoly_natDegree] at hdeg
  have hd : ((r₂ - r₁) + C γ * (q₂ - q₁)).natDegree < k :=
    lt_of_le_of_lt (natDegree_add_le _ _)
      (max_lt hdr (lt_of_le_of_lt (natDegree_C_mul_le _ _) hdq))
  omega

end CrossRestriction

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.cross_restriction_pinned
#print axioms ProximityGap.WBPencil.cross_restriction_root
#print axioms ProximityGap.WBPencil.cross_restriction_card_le
