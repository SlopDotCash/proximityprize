/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.BhSidonClosure
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Permutation

/-!
# `B_h`-Sidon ordered-list bridge (#444, §0)

`BhSidonClosure` states the §0 `B_h`-Sidon predicate in the clean multiset form: two
size-`h` multisets over `S` with the same sum must be equal.  Downstream counting often uses
**ordered** `h`-tuples/lists instead.  This file packages the exact bridge: under `IsBhSidon h S`,
two ordered size-`h` lists over `S` with the same sum are permutations of one another.

Probe: `scripts/probes/probe_bhsidon_list_perm.py` checked the corresponding finite cyclic
statement over many proper small sets in `Z/mZ` (`138416` `B_h` sets, `2149946` equal-sum ordered
pairs, zero failures).  This is only a structural bridge, not a CORE analytic input.

**Honesty / scope.** This is universal additive-combinatorics bookkeeping.  It is thickness-
invariant and therefore cannot prove the thin-subgroup CORE bound by itself.  It only supplies the
ordered-representation interface for the already-formalized `B_h`-Sidon predicate.
-/

namespace ArkLib.ProximityGap.BhSidon

variable {G : Type*} [AddCommGroup G]

/-- **Ordered representation uniqueness up to permutation.** If `S` is `B_h`-Sidon, then any two
ordered length-`h` lists over `S` with the same sum have the same underlying multiset, equivalently
they are permutations of each other.

This is the ordered-list interface for the multiset representation uniqueness theorem
`IsBhSidon.rep_unique`: the `B_h` predicate kills all non-permutation equal-sum ordered
collisions, so the ordered representation count is bounded by the number of orderings of a single
multiset (at most `h!`, formalized separately if needed). -/
theorem IsBhSidon.list_perm_of_sum_eq {h : ℕ} {S : Set G} (hS : IsBhSidon h S)
    {l m : List G}
    (hl : l.length = h) (hm : m.length = h)
    (hlS : ∀ y ∈ l, y ∈ S) (hmS : ∀ y ∈ m, y ∈ S)
    (hsum : l.sum = m.sum) : l.Perm m := by
  have hcard_l : Multiset.card (l : Multiset G) = h := by simpa using hl
  have hcard_m : Multiset.card (m : Multiset G) = h := by simpa using hm
  have hmem_l : ∀ y ∈ (l : Multiset G), y ∈ S := by
    intro y hy
    exact hlS y (by simpa using hy)
  have hmem_m : ∀ y ∈ (m : Multiset G), y ∈ S := by
    intro y hy
    exact hmS y (by simpa using hy)
  have hsum_ms : (l : Multiset G).sum = (m : Multiset G).sum := by
    simpa using hsum
  have hms : (l : Multiset G) = (m : Multiset G) :=
    hS (l : Multiset G) (m : Multiset G) hcard_l hcard_m hmem_l hmem_m hsum_ms
  exact Multiset.coe_eq_coe.mp hms

/-- **Ordered representations are contained in one permutation fibre.** Under `IsBhSidon h S`,
if `l` is one ordered length-`h` representation of a target sum, then every other ordered
length-`h` representation `m` of that target lies in `l.permutations`.

This is the finite-list container behind the informal ordered-count consequence `≤ h!`: duplicate
permutations can only shrink the container, while `List.length_permutations` gives exactly `h!`
slots before quotienting duplicates. -/
theorem IsBhSidon.list_mem_permutations_of_sum_eq {h : ℕ} {S : Set G} (hS : IsBhSidon h S)
    {l m : List G}
    (hl : l.length = h) (hm : m.length = h)
    (hlS : ∀ y ∈ l, y ∈ S) (hmS : ∀ y ∈ m, y ∈ S)
    (hsum : l.sum = m.sum) : m ∈ l.permutations := by
  rw [List.mem_permutations]
  exact hS.list_perm_of_sum_eq hl hm hlS hmS hsum |>.symm

/-- **Ordered representation count bound.**  If a target `t` has one ordered length-`h`
representation `l` in a `B_h`-Sidon set, then any finite container `R` of ordered length-`h`
representations of the same target has at most `h!` elements.

This is the promised counting interface for `list_mem_permutations_of_sum_eq`: every `m ∈ R` lies
in the single permutation fibre `l.permutations`; passing to `toFinset` accounts for duplicate
permutations, so the cardinality is bounded by `List.length_permutations = h!`. -/
theorem IsBhSidon.card_ordered_representations_le_factorial
    {h : ℕ} {S : Set G} (hS : IsBhSidon h S) {t : G} {l : List G}
    (hl : l.length = h) (hlS : ∀ y ∈ l, y ∈ S) (hlt : l.sum = t)
    (R : Finset (List G))
    (hR : ∀ m ∈ R, m.length = h ∧ (∀ y ∈ m, y ∈ S) ∧ m.sum = t) :
    R.card ≤ h.factorial := by
  classical
  have hsub : R ⊆ l.permutations.toFinset := by
    intro m hm
    rw [List.mem_toFinset]
    have hm' := hR m hm
    exact hS.list_mem_permutations_of_sum_eq hl hm'.1 hlS hm'.2.1 (by rw [hm'.2.2, hlt])
  calc
    R.card ≤ l.permutations.toFinset.card := Finset.card_le_card hsub
    _ ≤ l.permutations.length := List.toFinset_card_le _
    _ = h.factorial := by rw [List.length_permutations, hl]

end ArkLib.ProximityGap.BhSidon

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BhSidon.IsBhSidon.list_perm_of_sum_eq
#print axioms ArkLib.ProximityGap.BhSidon.IsBhSidon.list_mem_permutations_of_sum_eq
#print axioms ArkLib.ProximityGap.BhSidon.IsBhSidon.card_ordered_representations_le_factorial
