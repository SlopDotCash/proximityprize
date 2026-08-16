/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.BhSidonClosure
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AttackB1_BadSetCosetNonSidon

/-!
# Bridge: the general `B_2`-Sidon predicate equals the pairwise Sidon predicate (#444, §0)

The §0 ladder uses the general-`h` multiset predicate `IsBhSidon` (introduced in
`BhSidonClosure`).  The in-tree refutation kernel `_AttackB1` uses the *pairwise*
Sidon predicate `AtkB1.IsSidonSet` (`a + b = c + d ⇒ {a,b} = {c,d}` quantified over
the four points).  This file proves they coincide at `h = 2`:

  `IsBhSidon 2 S ↔ AtkB1.IsSidonSet S`

so the general-`h` ladder is anchored to the existing refutation kernel — the
`B_2` rung of `IsBhSidon` IS the plain Sidon condition the kernel already reasons
about.  Reusable glue for the §0 program.

**Honesty / scope.** A definitional bridge between two equivalent structural
predicates.  Universal / char-free / thinness-agnostic.  NOT a CORE bound, no
char-p transfer, no growth-law; the CORE wall is untouched.
-/

namespace ArkLib.ProximityGap.BhSidon

variable {G : Type*} [AddCommGroup G]

/-- The pairwise Sidon predicate forces the general `B_2` (multiset) predicate:
two size-`2` multisets `{a,b}`, `{c,d}` in `S` with `a + b = c + d` have
`{a,b} = {c,d}` as multisets. -/
theorem isBhSidon_two_of_pairwise {S : Set G} (h : AtkB1.IsSidonSet S) :
    IsBhSidon 2 S := by
  intro s t hs ht hsS htS hsum
  -- a size-2 multiset is `{a,b}`
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hs
  obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.mp ht
  have ha : a ∈ S := hsS a (by simp)
  have hb : b ∈ S := hsS b (by simp)
  have hc : c ∈ S := htS c (by simp)
  have hd : d ∈ S := htS d (by simp)
  have hsum' : a + b = c + d := by
    simpa [Multiset.sum_cons, Multiset.sum_singleton] using hsum
  rcases h a ha b hb c hc d hd hsum' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Multiset.pair_comm a b

/-- The general `B_2` (multiset) predicate forces the pairwise Sidon predicate. -/
theorem pairwise_of_isBhSidon_two {S : Set G} (h : IsBhSidon 2 S) :
    AtkB1.IsSidonSet S := by
  intro a ha b hb c hc d hd hsum
  -- feed `{a,b}` and `{c,d}` as size-2 multisets
  have hs : Multiset.card ({a, b} : Multiset G) = 2 := by simp
  have ht : Multiset.card ({c, d} : Multiset G) = 2 := by simp
  have hsS : ∀ x ∈ ({a, b} : Multiset G), x ∈ S := by
    intro x hx; rcases Multiset.mem_cons.mp hx with rfl | hx'
    · exact ha
    · rw [Multiset.mem_singleton] at hx'; subst hx'; exact hb
  have htS : ∀ x ∈ ({c, d} : Multiset G), x ∈ S := by
    intro x hx; rcases Multiset.mem_cons.mp hx with rfl | hx'
    · exact hc
    · rw [Multiset.mem_singleton] at hx'; subst hx'; exact hd
  have hsum' : ({a, b} : Multiset G).sum = ({c, d} : Multiset G).sum := by
    simpa [Multiset.sum_cons, Multiset.sum_singleton] using hsum
  have hmeq : ({a, b} : Multiset G) = {c, d} := h _ _ hs ht hsS htS hsum'
  -- read off `{a,b} = {c,d}` as unordered pair equality via `cons_eq_cons`
  rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons,
    Multiset.cons_eq_cons] at hmeq
  rcases hmeq with ⟨rfl, hbd⟩ | ⟨_hne, cs, hbcs, hdcs⟩
  · -- a = c and {b} = {d} ⇒ b = d
    have : b = d := by simpa using hbd
    exact Or.inl ⟨rfl, this⟩
  · -- {b} = c ::ₘ cs forces cs = 0, b = c; {d} = a ::ₘ cs forces d = a
    have hcs0 : cs = 0 := by
      have : Multiset.card ({b} : Multiset G) = 1 := by simp
      rw [hbcs, Multiset.card_cons] at this
      simpa using this
    subst hcs0
    have hbc : b = c := by simpa using hbcs
    have hda : d = a := by simpa using hdcs
    exact Or.inr ⟨hda.symm, hbc⟩

/-- **The bridge.** The general `B_2`-Sidon predicate is exactly the pairwise
Sidon predicate of the `_AttackB1` refutation kernel. -/
theorem isBhSidon_two_iff_pairwise {S : Set G} :
    IsBhSidon 2 S ↔ AtkB1.IsSidonSet S :=
  ⟨pairwise_of_isBhSidon_two, isBhSidon_two_of_pairwise⟩

end ArkLib.ProximityGap.BhSidon
