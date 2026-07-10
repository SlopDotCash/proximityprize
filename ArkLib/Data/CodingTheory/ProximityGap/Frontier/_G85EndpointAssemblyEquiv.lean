/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G84SCorePaddingSlotPartition

/-!
# G85: endpoint assembly is an equivalence

G84S partitions the slots of an endpoint into an embedded ordered core and the canonically ordered
complementary padding slots.  This file turns that partition into mutually inverse assembly and
decomposition maps.

For every core-slot embedding `e : Fin s ↪ Fin r`, an endpoint word is exactly the same data as a
core word of length `s` and a padding word of length `r-s`.  The result removes the tuple-position
part of the factorial-corrected decoder obligation.  G83M chooses the core and common-padding
multisets; G81D chooses their relative order; this file proves that those ordered pieces reconstruct
each endpoint without loss.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G85EndpointAssemblyEquiv

open G84SCorePaddingSlotPartition

/-- Assemble an endpoint from its ordered core and padding words. -/
noncomputable def assemble {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (core : Fin s → A) (padding : Fin (r - s) → A) : Fin r → A :=
  Sum.elim core padding ∘ (slotEquiv hsr e).symm

/-- Read the core entries of an endpoint at the embedded core slots. -/
def coreAt {A : Type*} {r s : ℕ} (e : Fin s ↪ Fin r) (word : Fin r → A) : Fin s → A :=
  word ∘ e

/-- Read the padding entries in the canonical increasing order of complementary slots. -/
noncomputable def paddingAt {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (word : Fin r → A) : Fin (r - s) → A :=
  word ∘ padSlots hsr e

@[simp] theorem assemble_core {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (core : Fin s → A) (padding : Fin (r - s) → A) (i : Fin s) :
    assemble hsr e core padding (e i) = core i := by
  change Sum.elim core padding ((slotEquiv hsr e).symm (e i)) = core i
  rw [← slotEquiv_inl hsr e i, Equiv.symm_apply_apply]
  rfl

@[simp] theorem assemble_padding {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (core : Fin s → A) (padding : Fin (r - s) → A)
    (j : Fin (r - s)) :
    assemble hsr e core padding (padSlots hsr e j) = padding j := by
  change Sum.elim core padding ((slotEquiv hsr e).symm (padSlots hsr e j)) = padding j
  rw [← slotEquiv_inr hsr e j, Equiv.symm_apply_apply]
  rfl

@[simp] theorem coreAt_assemble {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (core : Fin s → A) (padding : Fin (r - s) → A) :
    coreAt e (assemble hsr e core padding) = core := by
  funext i
  exact assemble_core hsr e core padding i

@[simp] theorem paddingAt_assemble {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (core : Fin s → A) (padding : Fin (r - s) → A) :
    paddingAt hsr e (assemble hsr e core padding) = padding := by
  funext j
  exact assemble_padding hsr e core padding j

/-- Decomposing an endpoint and reassembling it returns the original endpoint. -/
@[simp] theorem assemble_coreAt_paddingAt {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (word : Fin r → A) :
    assemble hsr e (coreAt e word) (paddingAt hsr e word) = word := by
  funext k
  cases h : (slotEquiv hsr e).symm k with
  | inl i =>
      have hk : k = e i := by
        have := congrArg (slotEquiv hsr e) h
        simpa using this
      subst k
      exact assemble_core hsr e (coreAt e word) (paddingAt hsr e word) i
  | inr j =>
      have hk : k = padSlots hsr e j := by
        have := congrArg (slotEquiv hsr e) h
        simpa using this
      subst k
      exact assemble_padding hsr e (coreAt e word) (paddingAt hsr e word) j

/-- Fixed core positions induce an explicit equivalence between `(core,padding)` data and an
ordered endpoint. -/
noncomputable def endpointEquiv {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) : ((Fin s → A) × (Fin (r - s) → A)) ≃ (Fin r → A) where
  toFun x := assemble hsr e x.1 x.2
  invFun word := (coreAt e word, paddingAt hsr e word)
  left_inv x := by ext <;> simp
  right_inv word := assemble_coreAt_paddingAt hsr e word

end ArkLib.ProximityGap.Frontier.G85EndpointAssemblyEquiv

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G85EndpointAssemblyEquiv.assemble_core
#print axioms ArkLib.ProximityGap.Frontier.G85EndpointAssemblyEquiv.assemble_padding
#print axioms ArkLib.ProximityGap.Frontier.G85EndpointAssemblyEquiv.assemble_coreAt_paddingAt
#print axioms ArkLib.ProximityGap.Frontier.G85EndpointAssemblyEquiv.endpointEquiv
