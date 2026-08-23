/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# The polynomial-row case: a codeword row kills all nonzero bad scalars (#371, WB-3b)

The degenerate branch of the rational-pair analysis: if **either row of the stack is
itself a codeword**, at most one scalar is MCA-bad — and effortlessly so:

* `u₀ ∈ C`: an explanation `w` of the line on the witness gives the joint pair
  `(u₀, γ⁻¹•(w − u₀))` on the SAME witness — every `γ ≠ 0` is good (`only γ = 0`
  can be bad).
* `u₁ ∈ C` (by the same algebra through the line): the joint pair
  `(w − γ•u₁, u₁)` works at EVERY `γ` — **no scalar is bad at all**.

This closes the polynomial-row branch of the WB classification: together with
WB-3a (genuine rational rows, zero bad below the ladder reach) the below-ladder
rational family carries at most one bad scalar in every branch with at least one
non-genuine row.  No degree hypotheses, no radius hypotheses, any linear code.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.WBPencil

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The codeword-offset kill**: if `u₀ ∈ C`, no nonzero scalar is MCA-bad — the
line explanation hands back a joint explanation. -/
theorem not_mcaEvent_of_fst_mem (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} (h₀ : u₀ ∈ C) {γ : F} (hγ : γ ≠ 0) :
    ¬ mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  rintro ⟨S, hsz, ⟨w, hw, hag⟩, hno⟩
  refine hno ⟨u₀, h₀, γ⁻¹ • (w - u₀), C.smul_mem _ (C.sub_mem hw h₀), fun i hi => ?_⟩
  refine ⟨rfl, ?_⟩
  have h := hag i hi
  calc (γ⁻¹ • (w - u₀)) i = γ⁻¹ • (w i - u₀ i) := rfl
    _ = γ⁻¹ • ((u₀ i + γ • u₁ i) - u₀ i) := by rw [h]
    _ = γ⁻¹ • (γ • u₁ i) := by rw [add_sub_cancel_left]
    _ = u₁ i := by rw [smul_smul, inv_mul_cancel₀ hγ, one_smul]

/-- **The codeword-direction kill**: if `u₁ ∈ C`, NO scalar is MCA-bad at all. -/
theorem not_mcaEvent_of_snd_mem (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} (h₁ : u₁ ∈ C) (γ : F) :
    ¬ mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  rintro ⟨S, hsz, ⟨w, hw, hag⟩, hno⟩
  refine hno ⟨w - γ • u₁, C.sub_mem hw (C.smul_mem γ h₁), u₁, h₁, fun i hi => ?_⟩
  refine ⟨?_, rfl⟩
  have h := hag i hi
  calc (w - γ • u₁) i = w i - γ • u₁ i := rfl
    _ = (u₀ i + γ • u₁ i) - γ • u₁ i := by rw [h]
    _ = u₀ i := by rw [add_sub_cancel_right]

open Classical in
/-- The counting form: a stack with a codeword offset has at most one bad scalar. -/
theorem badScalars_card_le_one_of_fst_mem (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} (h₀ : u₀ ∈ C) :
    (Finset.univ.filter (fun γ : F =>
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ)).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun γ hγ γ' hγ' => ?_
  have hb := (Finset.mem_filter.mp hγ).2
  have hb' := (Finset.mem_filter.mp hγ').2
  by_cases h : γ = 0
  · by_cases h' : γ' = 0
    · rw [h, h']
    · exact absurd hb' (not_mcaEvent_of_fst_mem C δ h₀ h')
  · exact absurd hb (not_mcaEvent_of_fst_mem C δ h₀ h)

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.not_mcaEvent_of_fst_mem
#print axioms ProximityGap.WBPencil.not_mcaEvent_of_snd_mem
#print axioms ProximityGap.WBPencil.badScalars_card_le_one_of_fst_mem
