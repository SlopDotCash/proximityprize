/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungCrossRestriction
import ArkLib.Data.CodingTheory.ProximityGap.WindowParametricCapstone

/-!
# The solo bound (#371, rung): the Fisher leg of the summation

Scalars whose witnesses pairwise share at most `s < m` points form a
family bounded by the `(s+1)`-subset Fisher inequality: the witness map
is automatically injective on such a family (equal witnesses would share
`≥ m > s` points), so

  `#Γ_solo · C(m, s+1) ≤ C(n, s+1)`

(`solo_scalars_card_le`).  At the rung instance (`n = 16, m = 7, s = 2`):
`#solo ≤ C(16,3)/C(7,3) = 16` — the solo leg of the census summation,
now fully landed (the case-tree probe shows the record-22 stack has
ZERO solos; this leg binds only solo-heavy configurations).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section SoloBound

/-- **The solo Fisher bound**: a scalar family with witnesses of size
`≥ m` pairwise sharing `≤ s < m` points satisfies
`#Γ · C(m, s+1) ≤ C(n, s+1)`. -/
theorem solo_scalars_card_le {Γ : Finset F} {s m : ℕ} (hsm : s < m)
    (S : F → Finset (Fin n))
    (hcard : ∀ γ ∈ Γ, m ≤ (S γ).card)
    (hpair : ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ → (S γ₁ ∩ S γ₂).card ≤ s) :
    Γ.card * Nat.choose m (s + 1) ≤ Nat.choose n (s + 1) := by
  classical
  have hinj : Set.InjOn S Γ := by
    intro γ₁ h₁ γ₂ h₂ heq
    by_contra hne
    have hcap := hpair γ₁ h₁ γ₂ h₂ hne
    rw [heq, Finset.inter_self] at hcap
    have := hcard γ₂ h₂
    omega
  have himg : (Γ.image S).card = Γ.card := Finset.card_image_of_injOn hinj
  rw [← himg]
  refine pairwise_inter_le_subsets_card_le hsm ?_ ?_
  · intro T hT
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hT
    exact hcard γ hγ
  · intro T₁ hT₁ T₂ hT₂ hne
    obtain ⟨γ₁, hγ₁, rfl⟩ := Finset.mem_image.mp hT₁
    obtain ⟨γ₂, hγ₂, rfl⟩ := Finset.mem_image.mp hT₂
    exact hpair γ₁ hγ₁ γ₂ hγ₂ (fun h => hne (by rw [h]))

end SoloBound

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.solo_scalars_card_le
