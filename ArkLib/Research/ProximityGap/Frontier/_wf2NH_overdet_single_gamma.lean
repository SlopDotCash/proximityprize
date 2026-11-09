/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# wf-NH (#407): the per-witness over-determination dichotomy — structural root of δ* p-independence

The lane-NH decoupling claim is: at the binding (over-determined) radius the far-line incidence
`I(u₀,u₁) = #{γ : u₀ + γ·u₁ explainable}` is a **union of single γ's** (each witness contributes
≤ 1 γ unless the direction is degenerate), hence a *discrete combinatorial count* over witness
configurations — NOT a character sum.  This file isolates the elementary linear-algebra fact that
makes "each witness ≤ 1 γ" exact, with **no character theory and no field-size dependence**:

> For a submodule `W` of a vector space and vectors `a b`, the affine line `{γ : a + γ•b ∈ W}`
> is **either** all of `F` (iff `b ∈ W`) **or** a subsingleton (≤ 1 point).

In the incidence application `W = RS[R,k]|_R` and `b = u₁|_R`: a *far* direction (`b ∉ W`, the
over-determined regime where `dim W = |R| − k ≥ 0` forces `b ∉ W` for a far stack) gives **at most
one** γ per witness, so `I` is a finite union of forced points — the p-independent combinatorial
object.  The "all of F" branch is the heavy/near-coset degeneracy excluded by the far condition.

This is axiom-clean and field-size-free: the dichotomy holds verbatim over `F_p` for every `p`,
which is exactly why the per-witness contribution carries no p-dependence (the p-dependence in the
*under-determined* regime comes from the *value* of the forced γ varying with p when there are
≤ k+1 points — not from this dichotomy, which is uniform).
-/

namespace ProximityGap.Frontier.wf2NH

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-- The affine line `γ ↦ a + γ•b` hits the submodule `W` for **at most one** γ, *unless*
`b ∈ W` (in which case it hits for either all γ or no γ).  Concretely: if two distinct scalars
`γ₁ ≠ γ₂` both place the line in `W`, then `b ∈ W`. -/
theorem mem_of_two_hits {W : Submodule F V} {a b : V} {γ₁ γ₂ : F}
    (h₁ : a + γ₁ • b ∈ W) (h₂ : a + γ₂ • b ∈ W) (hne : γ₁ ≠ γ₂) : b ∈ W := by
  have hdiff : (γ₁ - γ₂) • b ∈ W := by
    have : (a + γ₁ • b) - (a + γ₂ • b) ∈ W := W.sub_mem h₁ h₂
    simpa [sub_smul, add_sub_add_left_eq_sub] using this
  have hunit : (γ₁ - γ₂) ≠ 0 := sub_ne_zero.mpr hne
  have := W.smul_mem (γ₁ - γ₂)⁻¹ hdiff
  rwa [smul_smul, inv_mul_cancel₀ hunit, one_smul] at this

/-- **The over-determination dichotomy.**  For the far/over-determined regime (`b ∉ W`), the
γ-incidence set of a single witness is a **subsingleton**: at most one scalar γ places the affine
line `a + γ•b` inside `W`.  This is the per-witness "≤ 1 γ" that turns the binding incidence into a
finite union of forced points (a combinatorial count), uniformly in the field. -/
theorem incidence_subsingleton_of_not_mem {W : Submodule F V} {a b : V} (hb : b ∉ W) :
    {γ : F | a + γ • b ∈ W}.Subsingleton := by
  intro γ₁ h₁ γ₂ h₂
  by_contra hne
  exact hb (mem_of_two_hits h₁ h₂ hne)

/-- **The full trichotomy.**  The γ-incidence set of one witness is exactly one of:
(i) `b ∈ W` ⇒ it is all of `F` (every γ) when `a ∈ W`, else ∅; (ii) `b ∉ W` ⇒ a subsingleton.
The combinatorial (p-independent) object is the union of the case-(ii) singletons. -/
theorem incidence_trichotomy {W : Submodule F V} (a b : V) :
    (b ∈ W ∧ a ∈ W ∧ {γ : F | a + γ • b ∈ W} = Set.univ) ∨
    (b ∈ W ∧ a ∉ W ∧ {γ : F | a + γ • b ∈ W} = ∅) ∨
    (b ∉ W ∧ {γ : F | a + γ • b ∈ W}.Subsingleton) := by
  by_cases hb : b ∈ W
  · by_cases ha : a ∈ W
    · refine Or.inl ⟨hb, ha, ?_⟩
      ext γ; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact W.add_mem ha (W.smul_mem γ hb)
    · refine Or.inr (Or.inl ⟨hb, ha, ?_⟩)
      ext γ; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hmem
      exact ha (by
        have := W.sub_mem hmem (W.smul_mem γ hb)
        simpa using this)
  · exact Or.inr (Or.inr ⟨hb, incidence_subsingleton_of_not_mem hb⟩)

end ProximityGap.Frontier.wf2NH

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — no sorryAx)
#print axioms ProximityGap.Frontier.wf2NH.mem_of_two_hits
#print axioms ProximityGap.Frontier.wf2NH.incidence_subsingleton_of_not_mem
#print axioms ProximityGap.Frontier.wf2NH.incidence_trichotomy
