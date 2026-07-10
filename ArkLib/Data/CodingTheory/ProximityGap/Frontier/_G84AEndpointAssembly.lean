/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G84SCorePaddingSlotPartition

/-!
# G84A: assemble and recover ordered endpoints from core/padding slots

Using G84S's canonical slot equivalence, this file defines the endpoint word obtained by placing an
ordered primitive core in its embedded slots and an ordered padding word in the complementary
slots.  Both restrictions recover definitionally, so assembly is injective for a fixed core-slot
embedding.

This is the forward half of the actual factorial-corrected decoder.  The remaining surjectivity
proof must extract the embedding/core/padding data from G83M maximal cancellation and use G81D for
the second padding order.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G84AEndpointAssembly

open ArkLib.ProximityGap.Frontier.G84SCorePaddingSlotPartition

/-- Assemble one ordered endpoint from an ordered core and its complementary padding word. -/
noncomputable def assemble {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (core : Fin s → A) (pad : Fin (r - s) → A) : Fin r → A :=
  Sum.elim core pad ∘ (slotEquiv hsr e).symm

@[simp] theorem assemble_core {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (core : Fin s → A) (pad : Fin (r - s) → A) (i : Fin s) :
    assemble hsr e core pad (e i) = core i := by
  unfold assemble Function.comp_def
  rw [← slotEquiv_inl hsr e i, Equiv.symm_apply_apply]
  rfl

@[simp] theorem assemble_pad {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (core : Fin s → A) (pad : Fin (r - s) → A)
    (j : Fin (r - s)) :
    assemble hsr e core pad (padSlots hsr e j) = pad j := by
  unfold assemble Function.comp_def
  rw [← slotEquiv_inr hsr e j, Equiv.symm_apply_apply]
  rfl

/-- Core and padding words can be recovered uniquely from the assembled endpoint when the slot
embedding is fixed. -/
theorem assemble_injective {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) :
    Function.Injective (fun d : (Fin s → A) × (Fin (r - s) → A) =>
      assemble hsr e d.1 d.2) := by
  rintro ⟨core, pad⟩ ⟨core', pad'⟩ h
  apply Prod.ext
  · funext i
    have hi := congrFun h (e i)
    simpa using hi
  · funext j
    have hj := congrFun h (padSlots hsr e j)
    simpa using hj

end ArkLib.ProximityGap.Frontier.G84AEndpointAssembly

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G84AEndpointAssembly.assemble_core
#print axioms ArkLib.ProximityGap.Frontier.G84AEndpointAssembly.assemble_pad
#print axioms ArkLib.ProximityGap.Frontier.G84AEndpointAssembly.assemble_injective
