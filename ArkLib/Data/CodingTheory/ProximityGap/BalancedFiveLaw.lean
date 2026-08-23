/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BalancedFourLaw
import Mathlib.Tactic.LinearCombination

/-!
# The balanced five-set law: the coset structure behind the `a = 5` flat-`n` census

Campaign #357. The `a = 5` row of the depth-1 census measures as a **flat-`n` law** (one
rotation orbit, census `= n` — probe-verified at `n = 8, 16, 32` with subset counts
`(n/4)(n−4)`). This file proves the structure theorem behind it:

> **`balanced_five_iff`** — in a commutative ring whose doubling kernel is `{0, h}`
> (`h ≠ 0`, `2h = 0`), with `2q = h` and no 5-torsion: a five-element set has antipodally
> balanced pair sums **iff** it is a coset of the order-4 subgroup `{0, q, h, q + h}`
> plus one free point.

Mechanism:
* (completeness) a balance witness tree — at most four count instantiations deep — forces
  an antipodal pair `{x, x+h}` inside the set (the terminal branches are
  `linear_combination` identities resolved by the doubling kernel; one branch needs
  5-torsion-freeness); the residual four-element sum multiset `{2x+h} ∪ pairSums(T)`
  then balances only by matching `2x+h` against a couple sum, which forces a **second**
  antipodal pair `{w, w+h}` with `2w = 2x + h`, i.e. `w ∈ x + {q, q+h}`: the coset.
* (soundness) the coset's six internal sums split as `{2x, 2x+h} + 2·{2x+q, 2x+q+h}` and
  every cross sum pairs with its `+h` mate: five antipodal fibers.

The census consequence (`A5CensusValue`-side, separate file): the whole coset cancels in
the field — `∑_{coset} g^i = g^x(1+g^q)(1+g^h) = 0` — so the census value is `−g^v`, the
free point alone: one rotation orbit, **census `= n`, the first proven flat-`n` law**.

## References

* Probes `probe_a5_coset_shape.py`, `probe_general_a_structure.py`; issue #357.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.WindowTwoLayer

open Multiset

variable {R : Type*} [CommRing R] [DecidableEq R]

/-! ## The ten pair sums -/

theorem pairSums_five (a b c d e : R) :
    pairSums {a, b, c, d, e}
      = {a + b} + {a + c} + {a + d} + {a + e} + {b + c} + {b + d} + {b + e}
        + {c + d} + {c + e} + {d + e} := by
  rw [show ({a, b, c, d, e} : Multiset R) = a ::ₘ b ::ₘ c ::ₘ ({d, e} : Multiset R)
      from rfl,
    pairSums_cons, pairSums_cons, pairSums_cons, pairSums_pair]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
  ext t
  simp only [Multiset.count_add, Multiset.insert_eq_cons, Multiset.count_cons,
    Multiset.count_singleton]
  ring

section FiveLaw

variable {h q : R} (hh2 : h + h = 0) (hh0 : h ≠ 0)
  (hker : ∀ y : R, y + y = 0 → y = 0 ∨ y = h)
  (h5 : ∀ y : R, 5 * y = 0 → y = 0)

/-- Doubling-kernel step: `2(u − v) = 0` with `u ≠ v` forces the antipodal relation. -/
private theorem eq_add_h_of_double (hker : ∀ y : R, y + y = 0 → y = 0 ∨ y = h)
    {u v : R} (huv : u ≠ v) (h2 : (u - v) + (u - v) = 0) : u = v + h := by
  rcases hker _ h2 with h0 | hh
  · exact absurd (by linear_combination h0) huv
  · linear_combination hh

/-- Membership in the ten-sum multiset is one of the ten sums. -/
private theorem mem_ten {a b c d e s : R}
    (hs : 0 < (({a + b} : Multiset R) + {a + c} + {a + d} + {a + e} + {b + c} + {b + d}
      + {b + e} + {c + d} + {c + e} + {d + e}).count s) :
    s = a + b ∨ s = a + c ∨ s = a + d ∨ s = a + e ∨ s = b + c ∨ s = b + d ∨ s = b + e
      ∨ s = c + d ∨ s = c + e ∨ s = d + e := by
  have hmem := Multiset.count_pos.mp hs
  simpa [Multiset.mem_add] using hmem

/-- One balance witness: the `+h` translate of any of the ten sums is again one of the
ten sums. -/
private theorem witness {a b c d e : R}
    (hbal : Balanced h (({a + b} : Multiset R) + {a + c} + {a + d} + {a + e} + {b + c}
      + {b + d} + {b + e} + {c + d} + {c + e} + {d + e})) (s : R)
    (hs : 0 < (({a + b} : Multiset R) + {a + c} + {a + d} + {a + e} + {b + c} + {b + d}
      + {b + e} + {c + d} + {c + e} + {d + e}).count s) :
    s + h = a + b ∨ s + h = a + c ∨ s + h = a + d ∨ s + h = a + e ∨ s + h = b + c
      ∨ s + h = b + d ∨ s + h = b + e ∨ s + h = c + d ∨ s + h = c + e
      ∨ s + h = d + e := by
  refine mem_ten ?_
  rw [← hbal s]
  exact hs

/-- An antipodal pair of elements inside a multiset. -/
abbrev HasPair (M : Multiset R) (h : R) : Prop :=
  ∃ p r, p ∈ M ∧ r ∈ M ∧ r = p + h

include hh2 hh0 hker h5

/-- **The deep branch**: a disjoint-pair relation `c + d = a + b + h` plus balance forces
an antipodal pair. The witness tree is at most three levels deep; terminal branches close
by `linear_combination` + the doubling kernel, one by 5-torsion-freeness. -/
private theorem aux_pair {a b c d e : R}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hbal : Balanced h (pairSums {a, b, c, d, e}))
    (E1 : c + d = a + b + h) : HasPair ({a, b, c, d, e} : Multiset R) h := by
  rw [pairSums_five] at hbal
  have mema : a ∈ ({a, b, c, d, e} : Multiset R) := by simp
  have memb : b ∈ ({a, b, c, d, e} : Multiset R) := by simp
  have memc : c ∈ ({a, b, c, d, e} : Multiset R) := by simp
  have memd : d ∈ ({a, b, c, d, e} : Multiset R) := by simp
  have meme : e ∈ ({a, b, c, d, e} : Multiset R) := by simp
  -- first witness: the fiber of a + c
  rcases witness hbal (a + c)
      (Multiset.count_pos.mpr (by simp [Multiset.mem_add])) with
    g1 | g2 | g3 | g4 | g5 | g6 | g7 | g8 | g9 | g10
  · exact ⟨c, b, memc, memb, by linear_combination -g1⟩
  · exact absurd (show h = 0 by linear_combination g2) hh0
  · exact ⟨c, d, memc, memd, by linear_combination -g3⟩
  · exact ⟨c, e, memc, meme, by linear_combination -g4⟩
  · exact ⟨a, b, mema, memb, by linear_combination -g5⟩
  · -- b + d = a + c + h with E1 ⟹ 2(c − b) = 0
    exact ⟨b, c, memb, memc, eq_add_h_of_double hker (Ne.symm hbc)
      (by linear_combination E1 + g6)⟩
  · -- E2 : b + e = a + c + h — second witness at a + d
    have E2 : b + e = a + c + h := g7.symm
    rcases witness hbal (a + d)
        (Multiset.count_pos.mpr (by simp [Multiset.mem_add])) with
      f1 | f2 | f3 | f4 | f5 | f6 | f7 | f8 | f9 | f10
    · exact ⟨d, b, memd, memb, by linear_combination -f1⟩
    · exact ⟨d, c, memd, memc, by linear_combination -f2⟩
    · exact absurd (show h = 0 by linear_combination f3) hh0
    · exact ⟨d, e, memd, meme, by linear_combination -f4⟩
    · -- b + c = a + d + h with E1 ⟹ 2(c − a) = 2h
      exact ⟨a, c, mema, memc, eq_add_h_of_double hker (Ne.symm hac)
        (by linear_combination E1 - f5 + hh2)⟩
    · exact ⟨a, b, mema, memb, by linear_combination -f6⟩
    · -- a + d + h = b + e contradicts E2 (forces d = c)
      exact absurd (show d = c by linear_combination f7 + E2).symm hcd
    · exact ⟨a, c, mema, memc, by linear_combination -f8⟩
    · -- E3 : c + e = a + d + h — third witness at b + c
      have E3 : c + e = a + d + h := f9.symm
      rcases witness hbal (b + c)
          (Multiset.count_pos.mpr (by simp [Multiset.mem_add])) with
        k1 | k2 | k3 | k4 | k5 | k6 | k7 | k8 | k9 | k10
      · exact ⟨c, a, memc, mema, by linear_combination -k1⟩
      · exact ⟨b, a, memb, mema, by linear_combination -k2⟩
      · exact ⟨a, c, mema, memc, eq_add_h_of_double hker (Ne.symm hac)
          (by linear_combination E1 + k3)⟩
      · exact ⟨a, b, mema, memb, eq_add_h_of_double hker (Ne.symm hab)
          (by linear_combination E2 + k4)⟩
      · exact absurd (show h = 0 by linear_combination k5) hh0
      · exact ⟨c, d, memc, memd, by linear_combination -k6⟩
      · exact ⟨c, e, memc, meme, by linear_combination -k7⟩
      · exact ⟨b, d, memb, memd, by linear_combination -k8⟩
      · exact ⟨b, e, memb, meme, by linear_combination -k9⟩
      · -- E4 : d + e = b + c + h — the 5-torsion terminal branch
        have E4 : d + e = b + c + h := k10.symm
        have k : (5 : R) * (a - b) = 0 := by
          linear_combination (-2 : R) * E1 + (-4 : R) * E2 + E3 + (3 : R) * E4 - hh2
        exact absurd (sub_eq_zero.mp (h5 _ k)) hab
    · exact ⟨a, e, mema, meme, by linear_combination -f10⟩
  · exact ⟨a, d, mema, memd, by linear_combination -g8⟩
  · exact ⟨a, e, mema, meme, by linear_combination -g9⟩
  · -- E2' : d + e = a + c + h — second witness at a + d
    have E2' : d + e = a + c + h := g10.symm
    rcases witness hbal (a + d)
        (Multiset.count_pos.mpr (by simp [Multiset.mem_add])) with
      f1 | f2 | f3 | f4 | f5 | f6 | f7 | f8 | f9 | f10
    · exact ⟨d, b, memd, memb, by linear_combination -f1⟩
    · exact ⟨d, c, memd, memc, by linear_combination -f2⟩
    · exact absurd (show h = 0 by linear_combination f3) hh0
    · exact ⟨d, e, memd, meme, by linear_combination -f4⟩
    · -- b + c = a + d + h with E1 ⟹ 2(d − b) = 0
      exact ⟨b, d, memb, memd, eq_add_h_of_double hker (Ne.symm hbd)
        (by linear_combination E1 + f5)⟩
    · exact ⟨a, b, mema, memb, by linear_combination -f6⟩
    · -- F3 : b + e = a + d + h — third witness at a + e
      have F3 : b + e = a + d + h := f7.symm
      rcases witness hbal (a + e)
          (Multiset.count_pos.mpr (by simp [Multiset.mem_add])) with
        k1 | k2 | k3 | k4 | k5 | k6 | k7 | k8 | k9 | k10
      · exact ⟨e, b, meme, memb, by linear_combination -k1⟩
      · exact ⟨e, c, meme, memc, by linear_combination -k2⟩
      · exact ⟨e, d, meme, memd, by linear_combination -k3⟩
      · exact absurd (show h = 0 by linear_combination k4) hh0
      · -- F4a : b + c = a + e + h — the double-kernel terminal branch
        have F4a : b + c = a + e + h := k5.symm
        have t1 : (5 : R) * (d - a) = h := by
          linear_combination E1 + (3 : R) * E2' - F3 + (2 : R) * F4a + (2 : R) * hh2
        have t2 : (5 : R) * ((d - a) + (d - a)) = 0 := by
          linear_combination (2 : R) * t1 + hh2
        rcases hker _ (h5 _ t2) with h0 | hh'
        · exact absurd (sub_eq_zero.mp h0) (Ne.symm had)
        · exact ⟨a, d, mema, memd, by linear_combination hh'⟩
      · -- b + d = a + e + h with F3 ⟹ 2(e − d) = 0
        exact ⟨d, e, memd, meme, eq_add_h_of_double hker (Ne.symm hde)
          (by linear_combination F3 + k6)⟩
      · exact ⟨a, b, mema, memb, by linear_combination -k7⟩
      · -- c + d = a + e + h contradicts E1 (forces e = b)
        exact absurd (show e = b by linear_combination k8 + E1) (Ne.symm hbe)
      · exact ⟨a, c, mema, memc, by linear_combination -k9⟩
      · exact ⟨a, d, mema, memd, by linear_combination -k10⟩
    · exact ⟨a, c, mema, memc, by linear_combination -f8⟩
    · -- c + e = a + d + h with E2' ⟹ 2(d − c) = 0
      exact ⟨c, d, memc, memd, eq_add_h_of_double hker (Ne.symm hcd)
        (by linear_combination E2' + f9)⟩
    · exact ⟨a, e, mema, meme, by linear_combination -f10⟩

/-- **Every balanced five-set contains an antipodal pair.** -/
theorem antipodal_pair_of_balanced_five {a b c d e : R}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hbal : Balanced h (pairSums {a, b, c, d, e})) :
    HasPair ({a, b, c, d, e} : Multiset R) h := by
  have hbal' := hbal
  rw [pairSums_five] at hbal'
  have mema : a ∈ ({a, b, c, d, e} : Multiset R) := by simp
  have memb : b ∈ ({a, b, c, d, e} : Multiset R) := by simp
  have memc : c ∈ ({a, b, c, d, e} : Multiset R) := by simp
  have memd : d ∈ ({a, b, c, d, e} : Multiset R) := by simp
  have meme : e ∈ ({a, b, c, d, e} : Multiset R) := by simp
  have perm₁ : ({a, b, c, d, e} : Multiset R) = {a, b, c, e, d} := by
    simp only [Multiset.insert_eq_cons]
    exact congrArg (a ::ₘ ·) (congrArg (b ::ₘ ·) (congrArg (c ::ₘ ·)
      (Multiset.cons_swap _ _ _)))
  have perm₂ : ({a, b, c, d, e} : Multiset R) = {a, b, d, e, c} := by
    simp only [Multiset.insert_eq_cons]
    refine congrArg (a ::ₘ ·) (congrArg (b ::ₘ ·) ?_)
    calc c ::ₘ d ::ₘ ({e} : Multiset R) = d ::ₘ c ::ₘ ({e} : Multiset R) :=
        Multiset.cons_swap _ _ _
      _ = d ::ₘ e ::ₘ ({c} : Multiset R) := congrArg (d ::ₘ ·) (Multiset.cons_swap _ _ _)
  rcases witness hbal' (a + b)
      (Multiset.count_pos.mpr (by simp [Multiset.mem_add])) with
    g1 | g2 | g3 | g4 | g5 | g6 | g7 | g8 | g9 | g10
  · exact absurd (show h = 0 by linear_combination g1) hh0
  · exact ⟨b, c, memb, memc, by linear_combination -g2⟩
  · exact ⟨b, d, memb, memd, by linear_combination -g3⟩
  · exact ⟨b, e, memb, meme, by linear_combination -g4⟩
  · exact ⟨a, c, mema, memc, by linear_combination -g5⟩
  · exact ⟨a, d, mema, memd, by linear_combination -g6⟩
  · exact ⟨a, e, mema, meme, by linear_combination -g7⟩
  · exact aux_pair hh2 hh0 hker h5 hab hac had hae hbc hbd hbe hcd hce hde hbal g8.symm
  · -- c + e = a + b + h: apply the deep branch with d ↔ e
    rw [perm₁]
    rw [perm₁] at hbal
    exact aux_pair hh2 hh0 hker h5 hab hac hae had hbc hbe hbd hce hcd (Ne.symm hde)
      hbal g9.symm
  · -- d + e = a + b + h: apply the deep branch with c rotated to the end
    rw [perm₂]
    rw [perm₂] at hbal
    exact aux_pair hh2 hh0 hker h5 hab had hae hac hbd hbe hbc hde
      (Ne.symm hcd) (Ne.symm hce) hbal g10.symm

omit h5

/-- **The four-multiset matching law**: a balanced four-element multiset pairs off
antipodally, in one of the three matchings. -/
theorem balanced_four_multiset_matching {s₁ s₂ s₃ s₄ : R}
    (hbal : Balanced h ({s₁, s₂, s₃, s₄} : Multiset R)) :
    (s₂ = s₁ + h ∧ s₄ = s₃ + h) ∨ (s₃ = s₁ + h ∧ s₄ = s₂ + h)
      ∨ (s₄ = s₁ + h ∧ s₃ = s₂ + h) := by
  have hpos : 0 < ({s₁, s₂, s₃, s₄} : Multiset R).count (s₁ + h) := by
    rw [← hbal s₁]
    exact Multiset.count_pos.mpr (by simp)
  have hmem := Multiset.count_pos.mp hpos
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
  rcases hmem with h1 | h2 | h3 | h4
  · exact absurd (by linear_combination h1 : h = 0) hh0
  · -- s₂ = s₁ + h: the residual two-set must balance
    left
    refine ⟨h2.symm, ?_⟩
    have hsplit : ({s₁, s₂, s₃, s₄} : Multiset R)
        = ({s₁, s₁ + h} : Multiset R) + {s₃, s₄} := by
      rw [← h2]
      simp only [Multiset.insert_eq_cons, Multiset.singleton_add, Multiset.cons_add,
        Multiset.zero_add]
    rw [hsplit] at hbal
    exact (balanced_two_iff hh2 hh0 _ _).mp
      (balanced_residual (balanced_antipodal_pair hh2 _) hbal)
  · -- s₃ = s₁ + h
    right; left
    refine ⟨h3.symm, ?_⟩
    have hsplit : ({s₁, s₂, s₃, s₄} : Multiset R)
        = ({s₁, s₁ + h} : Multiset R) + {s₂, s₄} := by
      rw [← h3]
      ext t
      simp only [Multiset.count_add, Multiset.insert_eq_cons, Multiset.count_cons,
        Multiset.count_singleton]
      ring
    rw [hsplit] at hbal
    exact (balanced_two_iff hh2 hh0 _ _).mp
      (balanced_residual (balanced_antipodal_pair hh2 _) hbal)
  · -- s₄ = s₁ + h
    right; right
    refine ⟨h4.symm, ?_⟩
    have hsplit : ({s₁, s₂, s₃, s₄} : Multiset R)
        = ({s₁, s₁ + h} : Multiset R) + {s₂, s₃} := by
      rw [← h4]
      ext t
      simp only [Multiset.count_add, Multiset.insert_eq_cons, Multiset.count_cons,
        Multiset.count_singleton]
      ring
    rw [hsplit] at hbal
    exact (balanced_two_iff hh2 hh0 _ _).mp
      (balanced_residual (balanced_antipodal_pair hh2 _) hbal)

include h5

variable (hq : q + q = h)

include hq

/-- **The balanced five-set law, completeness half**: a balanced five-set is a coset of
`{0, q, h, q+h}` plus one free point. -/
theorem coset_shape_of_balanced_five {a b c d e : R}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hbal : Balanced h (pairSums {a, b, c, d, e})) :
    ∃ x v, ({a, b, c, d, e} : Multiset R) = {x, x + q, x + h, x + q + h, v} := by
  classical
  obtain ⟨p, r, hp, hr, hrp⟩ :=
    antipodal_pair_of_balanced_five hh2 hh0 hker h5 hab hac had hae hbc hbd hbe hcd hce
      hde hbal
  have hpr : p ≠ r := fun hc => hh0 (by linear_combination -hrp - hc)
  -- peel the pair off the five-set
  have hrmem : r ∈ ({a, b, c, d, e} : Multiset R).erase p :=
    (Multiset.mem_erase_of_ne (Ne.symm hpr)).mpr hr
  have hT3 : ((({a, b, c, d, e} : Multiset R).erase p).erase r).card = 3 := by
    rw [Multiset.card_erase_of_mem hrmem, Multiset.card_erase_of_mem hp]
    rfl
  obtain ⟨t₁, t₂, t₃, hT⟩ := Multiset.card_eq_three.mp hT3
  have hset : ({a, b, c, d, e} : Multiset R) = p ::ₘ r ::ₘ {t₁, t₂, t₃} := by
    rw [← hT, Multiset.cons_erase hrmem, Multiset.cons_erase hp]
  rw [hrp] at hset
  -- the residual four-multiset of sums balances
  have hbal5 : Balanced h (pairSums {p, p + h, t₁, t₂, t₃}) := by
    rw [show ({p, p + h, t₁, t₂, t₃} : Multiset R) = p ::ₘ (p + h) ::ₘ {t₁, t₂, t₃}
      from rfl, ← hset]
    exact hbal
  rw [pairSums_five] at hbal5
  have hre : ({p + (p + h)} : Multiset R) + {p + t₁} + {p + t₂} + {p + t₃}
        + {(p + h) + t₁} + {(p + h) + t₂} + {(p + h) + t₃} + {t₁ + t₂} + {t₁ + t₃}
        + {t₂ + t₃}
      = ((({p + t₁, (p + t₁) + h} : Multiset R) + {p + t₂, (p + t₂) + h}
          + {p + t₃, (p + t₃) + h}))
        + ({p + (p + h), t₁ + t₂, t₁ + t₃, t₂ + t₃} : Multiset R) := by
    have e1 : (p + h) + t₁ = (p + t₁) + h := by ring
    have e2 : (p + h) + t₂ = (p + t₂) + h := by ring
    have e3 : (p + h) + t₃ = (p + t₃) + h := by ring
    rw [e1, e2, e3]
    ext t
    simp only [Multiset.count_add, Multiset.insert_eq_cons, Multiset.count_cons,
      Multiset.count_singleton]
    ring
  rw [hre] at hbal5
  have hres : Balanced h ({p + (p + h), t₁ + t₂, t₁ + t₃, t₂ + t₃} : Multiset R) :=
    balanced_residual (balanced_add (balanced_add (balanced_antipodal_pair hh2 _)
      (balanced_antipodal_pair hh2 _)) (balanced_antipodal_pair hh2 _)) hbal5
  -- the matching law: `2p+h` must pair with a couple sum, forcing the second pair
  rcases balanced_four_multiset_matching hh2 hh0 hker hres with ⟨m1, m2⟩ | ⟨m1, m2⟩
    | ⟨m1, m2⟩
  · -- t₁ + t₂ = 2p (mod the fold) and t₂ = t₁ + h
    have ht₂ : t₂ = t₁ + h := by linear_combination m2
    have h2 : (t₁ - p - q) + (t₁ - p - q) = 0 := by linear_combination m1 - ht₂ - hq
    rcases hker _ h2 with k0 | kh
    · have e₁ : t₁ = p + q := by linear_combination k0
      have e₂ : t₂ = p + q + h := by linear_combination ht₂ + k0
      refine ⟨p, t₃, ?_⟩
      rw [hset, e₁, e₂]
      ext t
      simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
      ring
    · have e₁ : t₁ = p + q + h := by linear_combination kh
      have e₂ : t₂ = p + q := by linear_combination ht₂ + kh + hh2
      refine ⟨p, t₃, ?_⟩
      rw [hset, e₁, e₂]
      ext t
      simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
      ring
  · -- t₁ + t₃ = 2p (mod the fold) and t₃ = t₁ + h
    have ht₃ : t₃ = t₁ + h := by linear_combination m2
    have h2 : (t₁ - p - q) + (t₁ - p - q) = 0 := by linear_combination m1 - ht₃ - hq
    rcases hker _ h2 with k0 | kh
    · have e₁ : t₁ = p + q := by linear_combination k0
      have e₃ : t₃ = p + q + h := by linear_combination ht₃ + k0
      refine ⟨p, t₂, ?_⟩
      rw [hset, e₁, e₃]
      ext t
      simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
      ring
    · have e₁ : t₁ = p + q + h := by linear_combination kh
      have e₃ : t₃ = p + q := by linear_combination ht₃ + kh + hh2
      refine ⟨p, t₂, ?_⟩
      rw [hset, e₁, e₃]
      ext t
      simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
      ring
  · -- t₂ + t₃ = 2p (mod the fold) and t₃ = t₂ + h
    have ht₃ : t₃ = t₂ + h := by linear_combination m2
    have h2 : (t₂ - p - q) + (t₂ - p - q) = 0 := by linear_combination m1 - ht₃ - hq
    rcases hker _ h2 with k0 | kh
    · have e₂ : t₂ = p + q := by linear_combination k0
      have e₃ : t₃ = p + q + h := by linear_combination ht₃ + k0
      refine ⟨p, t₁, ?_⟩
      rw [hset, e₂, e₃]
      ext t
      simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
      ring
    · have e₂ : t₂ = p + q + h := by linear_combination kh
      have e₃ : t₃ = p + q := by linear_combination ht₃ + kh + hh2
      refine ⟨p, t₁, ?_⟩
      rw [hset, e₂, e₃]
      ext t
      simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
      ring

omit hq h5 hh0 hker

/-- **Soundness**: a coset plus a free point is balanced. -/
theorem balanced_of_coset_shape (hq : q + q = h) (x v : R) :
    Balanced h (pairSums {x, x + q, x + h, x + q + h, v}) := by
  rw [pairSums_five]
  have e1 : x + (x + q) = (x + x) + q := by ring
  have e2 : x + (x + h) = (x + x) + h := by ring
  have e3 : x + (x + q + h) = ((x + x) + q) + h := by ring
  have e4 : (x + q) + (x + h) = ((x + x) + q) + h := by ring
  have e5 : (x + q) + (x + q + h) = x + x := by linear_combination hq + hh2
  have e6 : (x + q) + v = (x + v) + q := by ring
  have e7 : (x + h) + (x + q + h) = (x + x) + q := by linear_combination hh2
  have e8 : (x + h) + v = (x + v) + h := by ring
  have e9 : (x + q + h) + v = ((x + v) + q) + h := by ring
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9]
  have hre : ({(x + x) + q} : Multiset R) + {(x + x) + h} + {((x + x) + q) + h} + {x + v}
        + {((x + x) + q) + h} + {x + x} + {(x + v) + q} + {(x + x) + q} + {(x + v) + h}
        + {((x + v) + q) + h}
      = ((({x + x, (x + x) + h} : Multiset R)
          + ({(x + x) + q, ((x + x) + q) + h} + {(x + x) + q, ((x + x) + q) + h}))
          + {x + v, (x + v) + h}) + {(x + v) + q, ((x + v) + q) + h} := by
    ext t
    simp only [Multiset.count_add, Multiset.insert_eq_cons, Multiset.count_cons,
      Multiset.count_singleton]
    ring
  rw [hre]
  exact balanced_add (balanced_add (balanced_add (balanced_antipodal_pair hh2 _)
    (balanced_add (balanced_antipodal_pair hh2 _) (balanced_antipodal_pair hh2 _)))
    (balanced_antipodal_pair hh2 _)) (balanced_antipodal_pair hh2 _)

include hh0 hker h5 hq

/-- **THE BALANCED FIVE-SET LAW.** In a commutative ring with doubling kernel `{0, h}`,
`2q = h` and no 5-torsion: a five-element set has antipodally balanced pair sums **iff**
it is a coset of `{0, q, h, q+h}` plus one free point. -/
theorem balanced_five_iff {a b c d e : R}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Balanced h (pairSums {a, b, c, d, e}) ↔
      ∃ x v, ({a, b, c, d, e} : Multiset R) = {x, x + q, x + h, x + q + h, v} := by
  constructor
  · exact coset_shape_of_balanced_five hh2 hh0 hker h5 hq hab hac had hae hbc hbd hbe
      hcd hce hde
  · rintro ⟨x, v, hset⟩
    rw [hset]
    exact balanced_of_coset_shape hh2 hq x v

end FiveLaw

/-! ## The smooth-scale instantiation -/

section ZModInstance

variable {m : ℕ}

/-- `ZMod (2^m)` has no 5-torsion. -/
theorem zmod_five_torsion_free (y : ZMod (2 ^ m)) (hy : 5 * y = 0) : y = 0 := by
  have hu : IsUnit (5 : ZMod (2 ^ m)) := by
    have : IsUnit ((5 : ℕ) : ZMod (2 ^ m)) := by
      rw [ZMod.isUnit_iff_coprime]
      exact Nat.Coprime.pow_right _ (by decide)
    simpa using this
  rcases hu with ⟨u, hu5⟩
  calc y = ↑u⁻¹ * (5 * y) := by rw [← hu5]; simp [← mul_assoc]
    _ = 0 := by rw [hy, mul_zero]

/-- **The balanced five-set law at every smooth scale**: balanced five-sets in
`ZMod (2^m)` are exactly cosets of the order-4 subgroup plus a free point. -/
theorem balanced_five_iff_zmod (hm : 2 ≤ m) {a b c d e : ZMod (2 ^ m)}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Balanced ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) (pairSums {a, b, c, d, e}) ↔
      ∃ x v, ({a, b, c, d, e} : Multiset (ZMod (2 ^ m)))
        = {x, x + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)),
            x + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)),
            x + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)),
            v} := by
  have hm1 : 1 ≤ m := by omega
  have hqq : ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))
      = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    rw [← Nat.cast_add]
    congr 1
    rw [← two_mul, ← pow_succ']
    congr 1
    omega
  exact balanced_five_iff (zmod_half_add_half hm1) (zmod_half_ne_zero hm1)
    (zmod_double_kernel hm1) zmod_five_torsion_free hqq hab hac had hae hbc hbd hbe
    hcd hce hde

end ZModInstance

/-! ## Source audit -/

#print axioms pairSums_five
#print axioms antipodal_pair_of_balanced_five
#print axioms balanced_four_multiset_matching
#print axioms coset_shape_of_balanced_five
#print axioms balanced_of_coset_shape
#print axioms balanced_five_iff
#print axioms balanced_five_iff_zmod

end ArkLib.ProximityGap.WindowTwoLayer
