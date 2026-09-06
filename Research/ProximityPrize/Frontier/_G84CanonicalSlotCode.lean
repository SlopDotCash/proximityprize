/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-! Lightweight canonical-slot code substrate for G84/G94. -/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G84CanonicalSlotsDepthFive

/-- An unordered set of `s` core positions in an endpoint of length `r`. -/
abbrev CoreSlots (r s : ℕ) := {t : Finset (Fin r) // t.card = s}

/-- Corrected padding code with canonical increasing core positions. -/
abbrev CanonicalPaddingCode (C A : Type*) (r s : ℕ) :=
  C × CoreSlots r s × CoreSlots r s ×
    (Fin (r - s) → A) × Equiv.Perm (Fin (r - s))

/-- Exact canonical-code cardinality. -/
theorem card_canonicalPaddingCode
    (C A : Type*) [Fintype C] [Fintype A] (r s : ℕ) :
    Fintype.card (CanonicalPaddingCode C A r s) =
      Fintype.card C * (r.choose s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
  simp only [CanonicalPaddingCode, CoreSlots, Fintype.card_prod,
    Fintype.card_finset_len, Fintype.card_fin, Fintype.card_fun, Fintype.card_perm]
  ring

/-- The numeric envelope supplied by the canonical code. -/
def canonicalPadEnvelope (n r K s : ℕ) : ℕ :=
  K * (r.choose s) ^ 2 * (r - s).factorial * n ^ (r - s)

/-- Any surjective canonical decoder gives the sharpened envelope. -/
theorem card_le_canonicalPadEnvelope
    (X C A : Type*) [Fintype X] [Fintype C] [Fintype A]
    (r s : ℕ) (decode : CanonicalPaddingCode C A r s → X)
    (hdecode : Function.Surjective decode) :
    Fintype.card X ≤ Fintype.card C * (r.choose s) ^ 2 *
      (r - s).factorial * (Fintype.card A) ^ (r - s) := by
  rw [← card_canonicalPaddingCode]
  exact Fintype.card_le_of_surjective decode hdecode

end ArkLib.ProximityGap.Frontier.G84CanonicalSlotsDepthFive

#print axioms
  ArkLib.ProximityGap.Frontier.G84CanonicalSlotsDepthFive.card_canonicalPaddingCode
