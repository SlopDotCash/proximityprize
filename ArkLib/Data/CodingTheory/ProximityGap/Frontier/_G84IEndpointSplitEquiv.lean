/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G84AEndpointAssembly

/-!
# G84I: endpoint restriction is inverse to core/padding assembly

For a fixed core-slot embedding, restrict an endpoint word to its core slots and G84S's canonical
complementary padding slots.  G84A assembly and these restrictions are exact inverses, giving an
equivalence

`(Fin r -> A) ≃ (Fin s -> A) × (Fin (r-s) -> A)`.

This closes the positional inverse problem.  The remaining decoder theorem only has to choose
embeddings whose restricted core multisets are G83M's residuals; the endpoint reconstruction then
follows automatically.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G84IEndpointSplitEquiv

open ArkLib.ProximityGap.Frontier.G84SCorePaddingSlotPartition
open ArkLib.ProximityGap.Frontier.G84AEndpointAssembly

/-- Restrict an endpoint to its embedded primitive-core slots. -/
def restrictCore {A : Type*} {r s : ℕ} (e : Fin s ↪ Fin r)
    (endpoint : Fin r → A) : Fin s → A := endpoint ∘ e

/-- Restrict an endpoint to the canonical increasing complementary padding slots. -/
noncomputable def restrictPad {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (endpoint : Fin r → A) : Fin (r - s) → A :=
  endpoint ∘ padSlots hsr e

/-- Assembly after restriction recovers every endpoint exactly. -/
theorem assemble_restrict {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (endpoint : Fin r → A) :
    assemble hsr e (restrictCore e endpoint) (restrictPad hsr e endpoint) = endpoint := by
  funext j
  obtain ⟨z, rfl⟩ := (slotEquiv hsr e).surjective j
  cases z with
  | inl i => simp [restrictCore]
  | inr k => simp [restrictPad]

/-- Core/padding restriction after assembly recovers both source words. -/
theorem restrict_assemble {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (core : Fin s → A) (pad : Fin (r - s) → A) :
    (restrictCore e (assemble hsr e core pad),
      restrictPad hsr e (assemble hsr e core pad)) = (core, pad) := by
  apply Prod.ext
  · funext i
    simp [restrictCore]
  · funext j
    simp [restrictPad]

/-- **Exact endpoint split equivalence.** -/
noncomputable def endpointSplitEquiv {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) :
    (Fin r → A) ≃ ((Fin s → A) × (Fin (r - s) → A)) where
  toFun endpoint := (restrictCore e endpoint, restrictPad hsr e endpoint)
  invFun d := assemble hsr e d.1 d.2
  left_inv endpoint := assemble_restrict hsr e endpoint
  right_inv d := by
    rcases d with ⟨core, pad⟩
    exact restrict_assemble hsr e core pad

end ArkLib.ProximityGap.Frontier.G84IEndpointSplitEquiv

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G84IEndpointSplitEquiv.assemble_restrict
#print axioms ArkLib.ProximityGap.Frontier.G84IEndpointSplitEquiv.restrict_assemble
#print axioms ArkLib.ProximityGap.Frontier.G84IEndpointSplitEquiv.endpointSplitEquiv
