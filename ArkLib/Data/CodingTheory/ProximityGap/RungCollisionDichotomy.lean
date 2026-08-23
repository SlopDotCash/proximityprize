/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungOffPointPinning

/-!
# The collision dichotomy (#371, rung): Ψ ≡ 0 merges the candidate maps

The structural half of the cross-class coupling.  For two frame classes
the collision pencil `Ψ = (R₀−r₁)(R₁−q₂) − (R₀−r₂)(R₁−q₁)` either is
nonzero (and the classes' scalar collisions are root-confined) or vanishes
IDENTICALLY — and then the stack is **rationally coupled**:

  `R₀ − r₁ = u₁·w`, `R₀ − r₂ = u₂·w`, where `R₁ − qⱼ = G·uⱼ` with
  `G = gcd` and `u₁ ⊥ u₂`

(`psi_zero_rational_coupling`).  Both classes' candidate maps collapse to
the single rational map `−w/G` (`psi_zero_candidate_maps_merge`,
division-free form) — exactly the Welch–Berlekamp pair shape handled by
the below-UDR window programme (`WindowChainStructure`,
`cored_gamma_unique`): the two arcs of the campaign meet at this seam.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [DecidableEq F]

section CollisionDichotomy

/-- **Rational coupling from a vanishing collision pencil**: if
`(R₀−r₁)(R₁−q₂) = (R₀−r₂)(R₁−q₁)` with `R₁ ≠ q₁`, then writing
`R₁−qⱼ = G·uⱼ` for the gcd `G`, there is a single `w` with
`R₀ − rⱼ = uⱼ·w` for both `j`. -/
theorem psi_zero_rational_coupling {R₀ R₁ r₁ r₂ q₁ q₂ : F[X]}
    (hne : R₁ - q₁ ≠ 0)
    (hΨ : (R₀ - r₁) * (R₁ - q₂) = (R₀ - r₂) * (R₁ - q₁)) :
    ∃ (G u₁ u₂ w : F[X]),
      R₁ - q₁ = G * u₁ ∧ R₁ - q₂ = G * u₂ ∧ IsCoprime u₁ u₂ ∧
      R₀ - r₁ = u₁ * w ∧ R₀ - r₂ = u₂ * w := by
  classical
  set G := GCDMonoid.gcd (R₁ - q₁) (R₁ - q₂) with hGdef
  have hGne : G ≠ 0 := by
    intro h0
    rw [hGdef] at h0
    exact hne (((_root_.gcd_eq_zero_iff _ _).mp h0).1)
  obtain ⟨u₁, hu₁⟩ : ∃ u, R₁ - q₁ = G * u := gcd_dvd_left (R₁ - q₁) (R₁ - q₂)
  obtain ⟨u₂, hu₂⟩ : ∃ u, R₁ - q₂ = G * u := gcd_dvd_right (R₁ - q₁) (R₁ - q₂)
  have hcop : IsCoprime u₁ u₂ := by
    have hGne' : GCDMonoid.gcd (R₁ - q₁) (R₁ - q₂) ≠ 0 := by
      rw [← hGdef]; exact hGne
    have h := isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
      (p := R₁ - q₁) (q := R₁ - q₂) hGne'
    have e₁ : (R₁ - q₁) / G = u₁ := by
      rw [hu₁]
      exact mul_div_cancel_left₀ u₁ hGne
    have e₂ : (R₁ - q₂) / G = u₂ := by
      rw [hu₂]
      exact mul_div_cancel_left₀ u₂ hGne
    rwa [← hGdef, e₁, e₂] at h
  -- substitute into Ψ ≡ 0 and cancel G
  have hkey : (R₀ - r₁) * u₂ = (R₀ - r₂) * u₁ := by
    have h2 : ((R₀ - r₁) * u₂) * G = ((R₀ - r₂) * u₁) * G := by
      calc ((R₀ - r₁) * u₂) * G = (R₀ - r₁) * (G * u₂) := by ring
        _ = (R₀ - r₁) * (R₁ - q₂) := by rw [← hu₂]
        _ = (R₀ - r₂) * (R₁ - q₁) := hΨ
        _ = (R₀ - r₂) * (G * u₁) := by rw [← hu₁]
        _ = ((R₀ - r₂) * u₁) * G := by ring
    exact mul_right_cancel₀ hGne h2
  -- u₁ ∣ (R₀ − r₁)·u₂ and u₁ ⊥ u₂ ⟹ u₁ ∣ R₀ − r₁
  have hdvd : u₁ ∣ R₀ - r₁ := by
    have h3 : u₁ ∣ (R₀ - r₁) * u₂ := ⟨R₀ - r₂, by linear_combination hkey⟩
    exact (hcop.symm).symm.dvd_of_dvd_mul_right h3
  obtain ⟨w, hw⟩ := hdvd
  refine ⟨G, u₁, u₂, w, hu₁, hu₂, hcop, hw, ?_⟩
  -- (R₀−r₂)·u₁ = (R₀−r₁)·u₂ = u₁·w·u₂ ⟹ R₀−r₂ = u₂·w (cancel u₁)
  have hu₁ne : u₁ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hu₁
    exact hne hu₁
  have h4 : (R₀ - r₂) * u₁ = (u₂ * w) * u₁ := by
    calc (R₀ - r₂) * u₁ = (R₀ - r₁) * u₂ := hkey.symm
      _ = (u₁ * w) * u₂ := by rw [hw]
      _ = (u₂ * w) * u₁ := by ring
  exact mul_right_cancel₀ hu₁ne h4

/-- **Candidate-map merge** (division-free): under the rational coupling,
both classes' pinning relations reduce to the SAME relation
`γ·G(x) = −w(x)` at any point where `u_j(x) ≠ 0` — one low-degree
candidate map serves both classes. -/
theorem psi_zero_candidate_maps_merge {G u w : F[X]} {γ x : F}
    (hu : u.eval x ≠ 0)
    (hpin : γ * (G * u).eval x = -((u * w).eval x)) :
    γ * G.eval x = -(w.eval x) := by
  rw [eval_mul] at hpin
  rw [eval_mul] at hpin
  have h := mul_right_cancel₀ hu (by linear_combination hpin :
    (γ * G.eval x) * u.eval x = (-(w.eval x)) * u.eval x)
  exact h

end CollisionDichotomy

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.psi_zero_rational_coupling
#print axioms ProximityGap.WBPencil.psi_zero_candidate_maps_merge
