/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G84CanonicalSlotsDepthFive
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G87CorrectedPaddingDecoder
import Mathlib.Data.Finset.Sort

/-!
# G94: every core embedding factors through canonical increasing slots

G84 replaces arbitrary core embeddings by an `s`-element subset of endpoint positions.  The key
finite bridge is that an arbitrary occurrence embedding carries no additional positional data:
after taking its range, it is the increasing enumeration of that range composed with one
permutation of the ordered core word.

This file proves that factorization.  It is the transport lemma needed to sharpen G87's genuine
maximal-cancellation decoder to G84's canonical-slot code without quotienting subgroup scale.
Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G94CanonicalCoreSlotFactorization

open ArkLib.ProximityGap.Frontier.G84CanonicalSlotsDepthFive

/-- The unique increasing embedding enumerating a core-slot subset. -/
noncomputable def canonicalEmbedding {r s : ℕ} (slots : CoreSlots r s) : Fin s ↪ Fin r :=
  (slots.1.orderEmbOfFin slots.2).toEmbedding

/-- Canonical enumeration lands exactly in its stored slot subset. -/
theorem canonicalEmbedding_mem {r s : ℕ} (slots : CoreSlots r s) (i : Fin s) :
    canonicalEmbedding slots i ∈ slots.1 := by
  exact Finset.orderEmbOfFin_mem slots.1 slots.2 i

/-- **Canonical factorization.** If an embedding has precisely the stored range, then it is the
increasing range enumeration followed by a unique permutation of `Fin s`. -/
theorem exists_perm_factor_canonical
    {r s : ℕ} (slots : CoreSlots r s) (e : Fin s ↪ Fin r)
    (hrange : ∀ x, x ∈ slots.1 ↔ ∃ i, e i = x) :
    ∃ σ : Equiv.Perm (Fin s),
      e = σ.toEmbedding.trans (canonicalEmbedding slots) := by
  let f : Fin s → Fin s := fun i =>
    (slots.1.orderIsoOfFin slots.2).symm
      ⟨e i, (hrange (e i)).2 ⟨i, rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply e.injective
    have h := congrArg (fun k : Fin s => canonicalEmbedding slots k) hij
    simpa [f, canonicalEmbedding, Finset.orderEmbOfFin,
      Finset.orderIsoOfFin] using h
  let σ : Equiv.Perm (Fin s) := Equiv.ofBijective f
    ⟨hf, (Finite.injective_iff_surjective.mp hf)⟩
  refine ⟨σ, ?_⟩
  apply DFunLike.ext _ _
  intro i
  change e i = canonicalEmbedding slots (f i)
  simp [f, canonicalEmbedding, Finset.orderEmbOfFin]

end ArkLib.ProximityGap.Frontier.G94CanonicalCoreSlotFactorization

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G94CanonicalCoreSlotFactorization.canonicalEmbedding_mem
#print axioms
  ArkLib.ProximityGap.Frontier.G94CanonicalCoreSlotFactorization.exists_perm_factor_canonical
