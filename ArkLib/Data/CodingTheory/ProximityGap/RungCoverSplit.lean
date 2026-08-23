/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungPackingResidual

/-!
# The cover split (#371, rung): the solo / paired Finset decomposition

The first concrete step of the cover construction inside `ClassPackingBound`.
Given any per-scalar witness assignment `S : F → Finset (Fin n)` and an
overlap threshold `t`, the bad set splits as

  `Γ = soloPart ∪ pairedPart`,  disjoint,

where `soloPart` = scalars whose witness shares `< t` points with every
*other* scalar's witness, and `pairedPart` = the rest (each has a
`≥ t`-overlap partner, so `paired_scalars_share_class` assigns it a frame
class).  This file proves the decomposition is a genuine cover
(`bad_eq_solo_union_paired`) and that the solo part is a pairwise-`< t`
family (`soloPart_pairwise_lt` — the exact hypothesis of
`solo_scalars_card_le`).  The paired part is then handed to the
class-indexing step; combined they build the `ClassPackingBound` cover.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [DecidableEq F]
variable {n : ℕ}

section CoverSplit

variable (Γ : Finset F) (S : F → Finset (Fin n)) (t : ℕ)

open Classical in
/-- The solo part: scalars sharing `< t` witness points with every other
member of `Γ`. -/
noncomputable def soloPart : Finset F :=
  Γ.filter (fun γ => ∀ γ' ∈ Γ, γ' ≠ γ → (S γ ∩ S γ').card < t)

open Classical in
/-- The paired part: the complement (has a `≥ t`-overlap partner). -/
noncomputable def pairedPart : Finset F :=
  Γ.filter (fun γ => ∃ γ' ∈ Γ, γ' ≠ γ ∧ t ≤ (S γ ∩ S γ').card)

/-- **The decomposition is a cover**: every bad scalar is solo or paired. -/
theorem bad_eq_solo_union_paired :
    Γ = soloPart Γ S t ∪ pairedPart Γ S t := by
  classical
  ext γ
  simp only [soloPart, pairedPart, Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hγ
    by_cases h : ∀ γ' ∈ Γ, γ' ≠ γ → (S γ ∩ S γ').card < t
    · exact Or.inl ⟨hγ, h⟩
    · push_neg at h
      obtain ⟨γ', hγ', hne, hge⟩ := h
      exact Or.inr ⟨hγ, γ', hγ', hne, hge⟩
  · rintro (⟨hγ, _⟩ | ⟨hγ, _⟩) <;> exact hγ

/-- The solo part is contained in the bad set. -/
theorem soloPart_subset : soloPart Γ S t ⊆ Γ := Finset.filter_subset _ _

/-- The paired part is contained in the bad set. -/
theorem pairedPart_subset : pairedPart Γ S t ⊆ Γ := Finset.filter_subset _ _

/-- **The solo part is a pairwise-`< t` family** — the hypothesis form of
`solo_scalars_card_le`.  Distinct solo scalars share `< t` witness points. -/
theorem soloPart_pairwise_lt :
    ∀ γ₁ ∈ soloPart Γ S t, ∀ γ₂ ∈ soloPart Γ S t, γ₁ ≠ γ₂ →
      (S γ₁ ∩ S γ₂).card < t := by
  classical
  intro γ₁ h₁ γ₂ h₂ hne
  rw [soloPart, Finset.mem_filter] at h₁ h₂
  exact h₁.2 γ₂ h₂.1 (Ne.symm hne)

end CoverSplit

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.bad_eq_solo_union_paired
#print axioms ProximityGap.WBPencil.soloPart_pairwise_lt
