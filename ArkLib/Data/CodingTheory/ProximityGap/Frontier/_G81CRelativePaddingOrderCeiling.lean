/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# G81C: exact cardinality of the factorial-corrected padding code

G80R refuted the one-word padding code because the two energy endpoints may order their common
padding multiset differently.  The corrected reconstruction data stores an ordered primitive core,
two core-slot embeddings, one ordered common-padding word, and the relative permutation producing
the second endpoint order.

This file proves the exact cardinality of that code and the generic surjective-decoder consumer.
It does not assume that the actual collision sector admits such a decoder: constructing it from
canonical maximal common cancellation remains the precise open combinatorial bridge.  Issue
#466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G81CRelativePaddingOrderCeiling

/-- Corrected reconstruction data, including the relative order of the second padding word. -/
abbrev PaddingCode (C A : Type*) (r s : ℕ) :=
  C × (Fin s ↪ Fin r) × (Fin s ↪ Fin r) ×
    (Fin (r - s) → A) × Equiv.Perm (Fin (r - s))

/-- **Exact corrected-code cardinality.**  The relative-permutation coordinate contributes the
universal ceiling factor `(r-s)!`.  With repeated padding values this coordinate is redundant, so
the exact padding-pair multiplicity can be strictly smaller. -/
theorem card_paddingCode (C A : Type*) [Fintype C] [Fintype A] (r s : ℕ) :
    Fintype.card (PaddingCode C A r s) =
      Fintype.card C * (r.descFactorial s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
  simp only [PaddingCode, Fintype.card_prod, Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_fun, Fintype.card_perm]
  ring

/-- Any collision sector admitting a surjective corrected-padding decoder satisfies the
factorial-corrected G80R envelope.  All remaining mathematical content is exactly decoder
surjectivity. -/
theorem card_le_factorialCorrectedPadding
    (X C A : Type*) [Fintype X] [Fintype C] [Fintype A]
    (r s : ℕ) (decode : PaddingCode C A r s → X)
    (hdecode : Function.Surjective decode) :
    Fintype.card X ≤ Fintype.card C * (r.descFactorial s) ^ 2 *
      (r - s).factorial * (Fintype.card A) ^ (r - s) := by
  rw [← card_paddingCode]
  exact Fintype.card_le_of_surjective decode hdecode

/-- The relative-order coordinate is genuinely used already for two padding slots: the identity
word and its swap are different endpoint orders of the same multiset. -/
theorem exists_swapped_padding_order :
    ∃ left right : Fin 2 → Fin 2, ∃ σ : Equiv.Perm (Fin 2),
      right = left ∘ σ ∧ right ≠ left := by
  let σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  refine ⟨(fun i => i), (fun i => 1 - i), σ, ?_, ?_⟩
  · funext i
    fin_cases i <;> rfl
  · intro h
    have h0 := congrFun h 0
    simp at h0

end ArkLib.ProximityGap.Frontier.G81CRelativePaddingOrderCeiling

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G81CRelativePaddingOrderCeiling.card_paddingCode
#print axioms
  ArkLib.ProximityGap.Frontier.G81CRelativePaddingOrderCeiling.card_le_factorialCorrectedPadding
#print axioms
  ArkLib.ProximityGap.Frontier.G81CRelativePaddingOrderCeiling.exists_swapped_padding_order
