/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G146GlobalSubsetAccidentEnvelope

/-!
# G147: connected balanced-core recursion

G146 reduces every subset-sum collision to full-depth disjoint equal-sum cores.  This file supplies
the first exact connected-packet operation on those cores.  A balanced core is a nonempty pair of
disjoint finite sets with equal cardinality and equal additive sum.  It is *primitive* when it has
no proper balanced subcore.

Every balanced core is either primitive or splits into a proper balanced subcore and its coordinate
complement.  Both pieces are nonempty balanced cores, both have strictly smaller depth, they are
pairwise disjoint on each side, and their unions reconstruct the original core.  Thus induction on
depth reduces an arbitrary full-depth core to primitive connected packets.

This is a structural recursion theorem, not the missing arithmetic estimate.  The remaining
Möbius--Mann problem is to classify and count the primitive cores in the two production fields.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G147ConnectedBalancedCoreRecursion

open scoped BigOperators

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

/-- A nonempty, equal-cardinality, disjoint equal-sum signed core. -/
def IsBalancedCore (c : Finset F × Finset F) : Prop :=
  c.1.Nonempty ∧ c.1.card = c.2.card ∧ Disjoint c.1 c.2 ∧
    ∑ x ∈ c.1, x = ∑ x ∈ c.2, x

/-- A balanced core properly contained coordinatewise in another core. -/
def IsProperBalancedSubcore (d c : Finset F × Finset F) : Prop :=
  IsBalancedCore d ∧ d.1 ⊆ c.1 ∧ d.2 ⊆ c.2 ∧ d.1 ≠ c.1

/-- A connected/primitive core has no proper balanced subcore. -/
def IsPrimitiveBalancedCore (c : Finset F × Finset F) : Prop :=
  IsBalancedCore c ∧ ¬ ∃ d, IsProperBalancedSubcore d c

/-- Coordinatewise complement of a subcore inside its parent. -/
def coreRemainder (c d : Finset F × Finset F) : Finset F × Finset F :=
  (c.1 \ d.1, c.2 \ d.2)

theorem properSubcore_left_card_lt {c d : Finset F × Finset F}
    (hd : IsProperBalancedSubcore d c) : d.1.card < c.1.card := by
  exact Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hd.2.1, hd.2.2.2⟩)

theorem properSubcore_right_ne {c d : Finset F × Finset F}
    (hc : IsBalancedCore c) (hd : IsProperBalancedSubcore d c) : d.2 ≠ c.2 := by
  intro h
  apply hd.2.2.2
  exact Finset.eq_of_subset_of_card_le hd.2.1 (by
    rw [hc.2.1, ← h, ← hd.1.2.1])

theorem coreRemainder_left_nonempty {c d : Finset F × Finset F}
    (hd : IsProperBalancedSubcore d c) : (coreRemainder c d).1.Nonempty := by
  apply Finset.card_pos.mp
  rw [coreRemainder, Finset.card_sdiff_of_subset hd.2.1]
  have := properSubcore_left_card_lt hd
  omega

theorem coreRemainder_right_nonempty {c d : Finset F × Finset F}
    (hc : IsBalancedCore c) (hd : IsProperBalancedSubcore d c) :
    (coreRemainder c d).2.Nonempty := by
  apply Finset.card_pos.mp
  rw [coreRemainder, Finset.card_sdiff_of_subset hd.2.2.1]
  have hlt : d.2.card < c.2.card :=
    Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨hd.2.2.1, properSubcore_right_ne hc hd⟩)
  omega

/-- Removing a proper balanced subcore leaves another balanced core. -/
theorem coreRemainder_balanced {c d : Finset F × Finset F}
    (hc : IsBalancedCore c) (hd : IsProperBalancedSubcore d c) :
    IsBalancedCore (coreRemainder c d) := by
  obtain ⟨hcne, hccard, hcdisj, hcsum⟩ := hc
  obtain ⟨⟨hdne, hdcard, hddisj, hdsum⟩, hdL, hdR, hdproper⟩ := hd
  refine ⟨coreRemainder_left_nonempty ⟨⟨hdne, hdcard, hddisj, hdsum⟩,
    hdL, hdR, hdproper⟩, ?_, ?_, ?_⟩
  · simp only [coreRemainder]
    rw [Finset.card_sdiff_of_subset hdL, Finset.card_sdiff_of_subset hdR,
      hccard, hdcard]
  · apply Finset.disjoint_left.mpr
    intro x hxL hxR
    exact (Finset.disjoint_left.mp hcdisj) (Finset.sdiff_subset hxL)
      (Finset.sdiff_subset hxR)
  · have hL := Finset.sum_sdiff hdL (f := fun x : F => x)
    have hR := Finset.sum_sdiff hdR (f := fun x : F => x)
    simp only [coreRemainder]
    apply add_left_cancel (a := ∑ x ∈ d.1, x)
    calc
      (∑ x ∈ d.1, x) + ∑ x ∈ c.1 \ d.1, x =
          (∑ x ∈ c.1 \ d.1, x) + ∑ x ∈ d.1, x := add_comm _ _
      _ = ∑ x ∈ c.1, x := hL
      _ = ∑ x ∈ c.2, x := hcsum
      _ = (∑ x ∈ c.2 \ d.2, x) + ∑ x ∈ d.2, x := hR.symm
      _ = (∑ x ∈ d.2, x) + ∑ x ∈ c.2 \ d.2, x := add_comm _ _
      _ = (∑ x ∈ d.1, x) + ∑ x ∈ c.2 \ d.2, x := by rw [hdsum]

theorem coreRemainder_left_card_lt {c d : Finset F × Finset F}
    (hc : IsBalancedCore c) (hd : IsProperBalancedSubcore d c) :
    (coreRemainder c d).1.card < c.1.card := by
  rw [coreRemainder, Finset.card_sdiff_of_subset hd.2.1]
  exact Nat.sub_lt (Finset.card_pos.mpr hc.1) (Finset.card_pos.mpr hd.1.1)

theorem core_split_reconstruct {c d : Finset F × Finset F}
    (hd : IsProperBalancedSubcore d c) :
    d.1 ∪ (coreRemainder c d).1 = c.1 ∧
      d.2 ∪ (coreRemainder c d).2 = c.2 := by
  simp only [coreRemainder]
  exact ⟨Finset.union_sdiff_of_subset hd.2.1, Finset.union_sdiff_of_subset hd.2.2.1⟩

theorem core_split_disjoint {c d : Finset F × Finset F} :
    Disjoint d.1 (coreRemainder c d).1 ∧ Disjoint d.2 (coreRemainder c d).2 := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro x hxd hxrem
    exact (Finset.mem_sdiff.mp hxrem).2 hxd
  · apply Finset.disjoint_left.mpr
    intro x hxd hxrem
    exact (Finset.mem_sdiff.mp hxrem).2 hxd

/-- **G147 capstone: split-or-primitive.** Every balanced core is connected, or decomposes into
two nonempty balanced cores of strictly smaller depth which reconstruct it exactly. -/
theorem primitive_or_split (c : Finset F × Finset F) (hc : IsBalancedCore c) :
    IsPrimitiveBalancedCore c ∨
      ∃ d e : Finset F × Finset F,
        IsProperBalancedSubcore d c ∧ IsBalancedCore e ∧
        d.1.card < c.1.card ∧ e.1.card < c.1.card ∧
        Disjoint d.1 e.1 ∧ Disjoint d.2 e.2 ∧
        d.1 ∪ e.1 = c.1 ∧ d.2 ∪ e.2 = c.2 := by
  by_cases hp : ∃ d, IsProperBalancedSubcore d c
  · right
    obtain ⟨d, hd⟩ := hp
    refine ⟨d, coreRemainder c d, hd, coreRemainder_balanced hc hd,
      properSubcore_left_card_lt hd, coreRemainder_left_card_lt hc hd, ?_⟩
    exact ⟨(core_split_disjoint (c := c) (d := d)).1,
      (core_split_disjoint (c := c) (d := d)).2,
      (core_split_reconstruct hd).1, (core_split_reconstruct hd).2⟩
  · exact Or.inl ⟨hc, hp⟩

#print axioms properSubcore_left_card_lt
#print axioms properSubcore_right_ne
#print axioms coreRemainder_balanced
#print axioms coreRemainder_left_card_lt
#print axioms core_split_reconstruct
#print axioms primitive_or_split

end ArkLib.ProximityGap.Frontier.G147ConnectedBalancedCoreRecursion
