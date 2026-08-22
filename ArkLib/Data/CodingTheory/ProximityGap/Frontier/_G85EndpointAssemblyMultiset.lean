/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G84AEndpointAssembly

/-!
# G85: endpoint assembly preserves the core-plus-padding multiset

G83M decomposes endpoint multisets, while G84A assembles ordered endpoint words.  This file proves
the missing compatibility law between those views: the multiset of an assembled endpoint is
exactly the sum of the core and padding multisets.

The proof factors through a reusable statement that enumerating a finite function's values is
invariant under reindexing by an equivalence.  This is the cancellation invariant needed by the
inverse factorial-corrected decoder.  It does not itself choose core positions from an arbitrary
endpoint; that extraction remains the next finite bridge.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G85EndpointAssemblyMultiset

open ArkLib.ProximityGap.Frontier.G84SCorePaddingSlotPartition
open ArkLib.ProximityGap.Frontier.G84AEndpointAssembly

/-- The multiset of values of a function on a finite index type, with multiplicity. -/
def valueMultiset {ι A : Type*} [Fintype ι] (f : ι → A) : Multiset A :=
  Multiset.map f Finset.univ.val

/-- Reindexing a finite word by an equivalence does not change its value multiset. -/
theorem valueMultiset_comp_equiv {ι κ A : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → A) :
    valueMultiset (f ∘ e) = valueMultiset f := by
  unfold valueMultiset
  rw [← Multiset.map_map]
  have hu := congrArg Finset.val (Finset.map_univ_equiv e)
  rw [Finset.map_val] at hu
  exact congrArg (Multiset.map f) (by simpa using hu)

/-- A word on a sum type enumerates as the sum of the two component value multisets. -/
theorem valueMultiset_sum {ι κ A : Type*} [Fintype ι] [Fintype κ]
    (left : ι → A) (right : κ → A) :
    valueMultiset (Sum.elim left right) = valueMultiset left + valueMultiset right := by
  unfold valueMultiset
  rw [← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.map_disjSum]
  rfl

/-- **Assembly/multiset compatibility.**  The assembled endpoint contains exactly its ordered
core and ordered padding values, independently of their slot positions. -/
theorem valueMultiset_assemble {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (core : Fin s → A) (pad : Fin (r - s) → A) :
    valueMultiset (assemble hsr e core pad) = valueMultiset core + valueMultiset pad := by
  rw [assemble, valueMultiset_comp_equiv (slotEquiv hsr e).symm]
  exact valueMultiset_sum core pad

/-- Restrict an endpoint word to the selected core slots. -/
def coreAt {A : Type*} {r s : ℕ} (e : Fin s ↪ Fin r) (word : Fin r → A) : Fin s → A :=
  word ∘ e

/-- Restrict an endpoint word to the canonical complementary padding slots. -/
noncomputable def padAt {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (word : Fin r → A) : Fin (r - s) → A :=
  word ∘ padSlots hsr e

/-- **Fixed-embedding inverse.**  Restriction to core and complementary padding slots followed by
assembly recovers the original endpoint exactly. -/
theorem assemble_coreAt_padAt {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (word : Fin r → A) :
    assemble hsr e (coreAt e word) (padAt hsr e word) = word := by
  funext x
  obtain ⟨z, rfl⟩ := (slotEquiv hsr e).surjective x
  cases z with
  | inl i => simp [coreAt]
  | inr j => simp [padAt]

/-- Once the selected core slots have the prescribed core multiset, the complementary restriction
has exactly the prescribed padding multiset.  This is multiset cancellation for the inverse
decoder. -/
theorem valueMultiset_padAt_eq_of_split {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (word : Fin r → A) (coreBag padBag : Multiset A)
    (hsplit : coreBag + padBag = valueMultiset word)
    (hcore : valueMultiset (coreAt e word) = coreBag) :
    valueMultiset (padAt hsr e word) = padBag := by
  have htotal :
      valueMultiset (coreAt e word) + valueMultiset (padAt hsr e word) =
        valueMultiset word := by
    have ha := valueMultiset_assemble hsr e (coreAt e word) (padAt hsr e word)
    rw [assemble_coreAt_padAt] at ha
    exact ha.symm
  apply add_left_cancel (a := coreBag)
  calc
    coreBag + valueMultiset (padAt hsr e word) = valueMultiset word := by
      simpa [hcore] using htotal
    _ = coreBag + padBag := hsplit.symm

end ArkLib.ProximityGap.Frontier.G85EndpointAssemblyMultiset

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G85EndpointAssemblyMultiset.valueMultiset_comp_equiv
#print axioms
  ArkLib.ProximityGap.Frontier.G85EndpointAssemblyMultiset.valueMultiset_sum
#print axioms
  ArkLib.ProximityGap.Frontier.G85EndpointAssemblyMultiset.valueMultiset_assemble
#print axioms
  ArkLib.ProximityGap.Frontier.G85EndpointAssemblyMultiset.assemble_coreAt_padAt
#print axioms
  ArkLib.ProximityGap.Frontier.G85EndpointAssemblyMultiset.valueMultiset_padAt_eq_of_split
