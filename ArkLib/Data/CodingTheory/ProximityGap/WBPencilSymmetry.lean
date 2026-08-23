/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# The γ-inversion symmetry of the MCA event (#371, WB-2 component)

For linear codes, the bad event is symmetric under swapping the stack rows and
inverting the scalar: `u₀ + γ·u₁ = γ·(u₁ + γ⁻¹·u₀)`, scaling by the unit `γ`
preserves explainability (the code is closed under scalars), the witness set is
unchanged, and the joint clause is row-symmetric.  Consequence (WB-2): the pencil
bound applies through EITHER row — the below-UDR supremum reduces to stacks where
both rows are WB-near, i.e. **doubly rational pairs**, the family the known
ceiling constructions inhabit.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.WBPencil

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

private theorem mcaEvent_swap_inv_aux (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} {γ : F} (hγ : γ ≠ 0)
    (h : mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ) :
    mcaEvent (F := F) (C : Set (ι → A)) δ u₁ u₀ γ⁻¹ := by
  obtain ⟨S, hsz, ⟨w, hw, hag⟩, hno⟩ := h
  refine ⟨S, hsz, ⟨γ⁻¹ • w, C.smul_mem γ⁻¹ hw, fun i hi => ?_⟩, fun hjoint => ?_⟩
  · have := hag i hi
    calc (γ⁻¹ • w) i = γ⁻¹ • w i := rfl
      _ = γ⁻¹ • (u₀ i + γ • u₁ i) := by rw [this]
      _ = u₁ i + γ⁻¹ • u₀ i := by
          rw [smul_add, smul_smul, inv_mul_cancel₀ hγ, one_smul, add_comm]
  · obtain ⟨v₀, h₀, v₁, h₁, hagj⟩ := hjoint
    exact hno ⟨v₁, h₁, v₀, h₀, fun i hi => ⟨(hagj i hi).2, (hagj i hi).1⟩⟩

/-- **The γ-inversion symmetry**: for linear codes,
`mcaEvent(u₀, u₁, γ) ⟺ mcaEvent(u₁, u₀, γ⁻¹)` at every nonzero scalar. -/
theorem mcaEvent_swap_inv (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} {γ : F} (hγ : γ ≠ 0) :
    mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₁ u₀ γ⁻¹ := by
  constructor
  · exact mcaEvent_swap_inv_aux C δ hγ
  · intro h
    have := mcaEvent_swap_inv_aux C δ (inv_ne_zero hγ) h
    rwa [inv_inv] at this

open Classical in
/-- The bad-set counting form: the bad scalars of the swapped stack are the
inverses of the bad scalars (away from `0`), so the counts differ by at most one. -/
theorem badScalars_card_swap_le (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (u₀ u₁ : ι → A) :
    (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ)).card
      ≤ (Finset.univ.filter (fun γ : F =>
          mcaEvent (F := F) (C : Set (ι → A)) δ u₁ u₀ γ)).card + 1 := by
  set S₀ := Finset.univ.filter (fun γ : F =>
    mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ) with hS₀
  set S₁ := Finset.univ.filter (fun γ : F =>
    mcaEvent (F := F) (C : Set (ι → A)) δ u₁ u₀ γ) with hS₁
  have hsub : S₀.erase 0 ⊆ S₁.image (fun γ => γ⁻¹) := by
    intro γ hγ
    have hγ0 : γ ≠ 0 := Finset.ne_of_mem_erase hγ
    have hbad := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hγ)).2
    refine Finset.mem_image.mpr ⟨γ⁻¹, ?_, inv_inv γ⟩
    rw [hS₁, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (mcaEvent_swap_inv C δ hγ0).mp hbad⟩
  calc S₀.card ≤ (insert (0 : F) (S₀.erase 0)).card := Finset.card_le_card (by
        intro γ hγ
        by_cases h0 : γ = 0
        · subst h0
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h0, hγ⟩))
    _ ≤ (S₀.erase 0).card + 1 := Finset.card_insert_le _ _
    _ ≤ (S₁.image (fun γ => γ⁻¹)).card + 1 :=
        Nat.add_le_add_right (Finset.card_le_card hsub) 1
    _ ≤ S₁.card + 1 := Nat.add_le_add_right Finset.card_image_le 1

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.mcaEvent_swap_inv
#print axioms ProximityGap.WBPencil.badScalars_card_swap_le
