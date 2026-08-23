/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Abel

/-!
# The proximity-gap line dichotomy (UDR MCA bound ingredient, #232)

A core ingredient of the unique-decoding-regime proximity gap / MCA upper bound: if two *distinct*
points of an affine line `{u₀ + γ·u₁}` are close to the code, then `u₁` (and symmetrically `u₀`) is
itself close to the code. This is the "either ≤ 1 close point, or the whole line is close"
dichotomy.

* `u1_close_of_two_line_points` — two distinct close line points (codewords `w₁, w₂` on `S₁, S₂`)
  ⇒ `u₁` agrees with `(γ₁−γ₂)⁻¹·(w₁−w₂) ∈ C` on the overlap `S₁ ∩ S₂`.
* `card_inter_ge` — `|S₁| + |S₂| ≤ n + |S₁ ∩ S₂|`, so two size-`≥(1-δ)n` witness sets overlap on
  `≥ (1-2δ)n` coordinates.

Combined with `CodingTheory.badGamma_affine_card_le` (the bad-scalar counting engine) and the
minimum-distance codeword-uniqueness step, these assemble into `ε_mca ≤ O(δn)/|F|` below the
unique-decoding radius (ABF26 Table-1 row 2). All results are hole-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
- [BCIKS20] Proximity gaps for Reed–Solomon codes.
-/

namespace ProximityGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]
variable {A : Type*} [AddCommGroup A] [Module F A]

/-- **Proximity-gap dichotomy (half).** If two *distinct* points of the affine line `{u₀ + γ·u₁}`
are close to `C` — witnessed by codewords `w₁, w₂` agreeing with the line on `S₁, S₂` — then `u₁`
agrees with the codeword `(γ₁−γ₂)⁻¹·(w₁−w₂) ∈ C` on the overlap `S₁ ∩ S₂`. -/
theorem u1_close_of_two_line_points (C : Submodule F (ι → A)) (u₀ u₁ : ι → A)
    {γ₁ γ₂ : F} (hne : γ₁ ≠ γ₂) {S₁ S₂ : Finset ι} {w₁ w₂ : ι → A}
    (hw₁ : w₁ ∈ C) (h₁ : ∀ i ∈ S₁, w₁ i = u₀ i + γ₁ • u₁ i)
    (hw₂ : w₂ ∈ C) (h₂ : ∀ i ∈ S₂, w₂ i = u₀ i + γ₂ • u₁ i) :
    ∃ c ∈ C, ∀ i ∈ S₁ ∩ S₂, c i = u₁ i := by
  have hd : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
  refine ⟨(γ₁ - γ₂)⁻¹ • (w₁ - w₂), C.smul_mem _ (C.sub_mem hw₁ hw₂), ?_⟩
  intro i hi
  rw [Finset.mem_inter] at hi
  have hwi : (w₁ - w₂) i = (γ₁ - γ₂) • u₁ i := by
    have e₁ := h₁ i hi.1
    have e₂ := h₂ i hi.2
    simp only [Pi.sub_apply, e₁, e₂, sub_smul]; abel
  simp only [Pi.smul_apply, hwi, inv_smul_smul₀ hd]

/-- The overlap of two witness sets is large: `|S₁| + |S₂| ≤ n + |S₁ ∩ S₂|`. -/
theorem card_inter_ge (S₁ S₂ : Finset ι) :
    S₁.card + S₂.card ≤ Fintype.card ι + (S₁ ∩ S₂).card := by
  have hun : (S₁ ∪ S₂).card ≤ Fintype.card ι := by simpa using Finset.card_le_univ (S₁ ∪ S₂)
  have hui : (S₁ ∪ S₂).card + (S₁ ∩ S₂).card = S₁.card + S₂.card :=
    Finset.card_union_add_card_inter S₁ S₂
  omega

#print axioms u1_close_of_two_line_points
#print axioms card_inter_ge

end ProximityGap
