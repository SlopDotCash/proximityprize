/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# G84S: canonical partition of endpoint slots into core and padding positions

The factorial-corrected decoder stores an embedding of `s` primitive-core slots into `r` endpoint
slots.  This file canonically enumerates the complementary `r-s` padding slots in increasing order
and proves that core plus padding slots form an equivalence with `Fin r`.

This is the tuple-position substrate needed to assemble and recover ordered endpoints from G81C's
coordinates.  The hypothesis `s <= r` is explicit; natural-number subtraction must not silently
accept malformed sector depths.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G84SCorePaddingSlotPartition

open Finset

/-- The endpoint slots occupied by an embedded ordered core. -/
def coreRange {r s : ℕ} (e : Fin s ↪ Fin r) : Finset (Fin r) :=
  Finset.univ.map e

@[simp] theorem card_coreRange {r s : ℕ} (e : Fin s ↪ Fin r) :
    (coreRange e).card = s := by
  simp [coreRange]

/-- Canonical increasing enumeration of all endpoint slots outside the core range. -/
noncomputable def padSlots {r s : ℕ} (hsr : s ≤ r) (e : Fin s ↪ Fin r) :
    Fin (r - s) ↪ Fin r :=
  (((coreRange e)ᶜ).orderEmbOfFin (by simp [Finset.card_compl, coreRange, hsr])).toEmbedding

theorem coreRange_mem {r s : ℕ} (e : Fin s ↪ Fin r) (i : Fin s) :
    e i ∈ coreRange e := by
  exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem padSlots_mem_compl {r s : ℕ} (hsr : s ≤ r) (e : Fin s ↪ Fin r)
    (j : Fin (r - s)) :
    padSlots hsr e j ∈ (coreRange e)ᶜ := by
  exact Finset.orderEmbOfFin_mem _ _ _

/-- Sum-indexed map placing core slots and padding slots into the endpoint. -/
noncomputable def slotMap {r s : ℕ} (hsr : s ≤ r) (e : Fin s ↪ Fin r) :
    Fin s ⊕ Fin (r - s) → Fin r :=
  Sum.elim e (padSlots hsr e)

theorem slotMap_injective {r s : ℕ} (hsr : s ≤ r) (e : Fin s ↪ Fin r) :
    Function.Injective (slotMap hsr e) := by
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl i' =>
          simp only [slotMap, Sum.elim_inl] at hxy
          exact congrArg Sum.inl (e.injective hxy)
      | inr j =>
          exfalso
          have hc : e i ∈ coreRange e := coreRange_mem e i
          have hp : padSlots hsr e j ∈ (coreRange e)ᶜ := padSlots_mem_compl hsr e j
          simp only [slotMap, Sum.elim_inl, Sum.elim_inr] at hxy
          rw [← hxy] at hp
          exact (Finset.mem_compl.mp hp) hc
  | inr j =>
      cases y with
      | inl i =>
          exfalso
          have hc : e i ∈ coreRange e := coreRange_mem e i
          have hp : padSlots hsr e j ∈ (coreRange e)ᶜ := padSlots_mem_compl hsr e j
          simp only [slotMap, Sum.elim_inl, Sum.elim_inr] at hxy
          rw [hxy] at hp
          exact (Finset.mem_compl.mp hp) hc
      | inr j' =>
          simp only [slotMap, Sum.elim_inr] at hxy
          exact congrArg Sum.inr ((padSlots hsr e).injective hxy)

/-- Core and canonical padding slots cover every endpoint slot exactly once. -/
theorem slotMap_bijective {r s : ℕ} (hsr : s ≤ r) (e : Fin s ↪ Fin r) :
    Function.Bijective (slotMap hsr e) := by
  apply (Fintype.bijective_iff_injective_and_card (slotMap hsr e)).mpr
  exact ⟨slotMap_injective hsr e, by simp [Fintype.card_sum, hsr]⟩

/-- The canonical equivalence used by endpoint assembly. -/
noncomputable def slotEquiv {r s : ℕ} (hsr : s ≤ r) (e : Fin s ↪ Fin r) :
    (Fin s ⊕ Fin (r - s)) ≃ Fin r :=
  Equiv.ofBijective (slotMap hsr e) (slotMap_bijective hsr e)

@[simp] theorem slotEquiv_inl {r s : ℕ} (hsr : s ≤ r) (e : Fin s ↪ Fin r)
    (i : Fin s) :
    slotEquiv hsr e (Sum.inl i) = e i := rfl

@[simp] theorem slotEquiv_inr {r s : ℕ} (hsr : s ≤ r) (e : Fin s ↪ Fin r)
    (j : Fin (r - s)) :
    slotEquiv hsr e (Sum.inr j) = padSlots hsr e j := rfl

end ArkLib.ProximityGap.Frontier.G84SCorePaddingSlotPartition

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G84SCorePaddingSlotPartition.slotMap_injective
#print axioms ArkLib.ProximityGap.Frontier.G84SCorePaddingSlotPartition.slotMap_bijective
#print axioms ArkLib.ProximityGap.Frontier.G84SCorePaddingSlotPartition.slotEquiv
