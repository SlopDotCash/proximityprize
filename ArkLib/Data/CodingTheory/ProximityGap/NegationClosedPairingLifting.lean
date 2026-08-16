/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal
import Mathlib.Tactic

/-!
# Index-involution lifting: count-balance ⟹ a fixed-point-free antipodal pairing (#389)

The K1 negation-closed walk bound (`NegationClosedWalkBound.zeroSumCount_le_pairings`) is conditional
on a residual `H`: every zero-sum `2r`-tuple must be antipodally paired by an INDEX-level
fixed-point-free involution `σ` with `c (σ i) = − c i`. The Lam–Leung theorem
(`LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero`) only gives the MULTISET count-balance
`count w = count (−w)`. This file supplies the missing lift from count-balance to an index involution:

> `exists_isPairing_of_count_balanced` :  if the value fibers of `f : Fin (2r) → L` are antipodally
> balanced and no value is self-antipodal (`f i ≠ − f i`), then there is an `IsPairing σ` with
> `f (σ i) = − f i` for all `i`.

Proven by strong induction on the support finset (`exists_pairing_finset`): pick `i`, find a partner
`j ≠ i` with `f j = − f i` (`partner_exists`), delete the matched pair (balance survives,
`balance_erase`), recurse, and glue with the swap `(i j)` via `Equiv.swap`. This discharges `H` for
any negation-closed root set (composing with Lam–Leung), upgrading the conditional K1 bound to an
unconditional one. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.NegationClosedWalk

namespace ArkLib.ProximityGap.NegationClosedWalk

variable {L : Type*} [DecidableEq L] [Field L]

/-- Card of a single-erase of a filtered finset: removing `a` drops the count by `1`
exactly when `a ∈ s` and `p a`. -/
private lemma card_filter_erase {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → Prop) [DecidablePred p] (a : ι) :
    ((s.erase a).filter p).card
      = (s.filter p).card - (if a ∈ s ∧ p a then 1 else 0) := by
  rw [Finset.filter_erase]
  by_cases ha : a ∈ s ∧ p a
  · have : a ∈ s.filter p := Finset.mem_filter.mpr ⟨ha.1, ha.2⟩
    rw [if_pos ha, Finset.card_erase_of_mem this]
  · rw [if_neg ha]
    have : a ∉ s.filter p := by
      intro h; rw [Finset.mem_filter] at h; exact ha ⟨h.1, h.2⟩
    rw [Finset.erase_eq_of_notMem this, Nat.sub_zero]

/-- Antipodal balance of fiber cards survives deletion of a matched pair `(i, j)` with
`f j = − f i`: both the value `w` fiber and the value `−w` fiber lose the same number of
deleted positions, so balance is preserved on `(s.erase i).erase j`. -/
private lemma balance_erase {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → L)
    (hbal : ∀ w : L, (s.filter (fun i => f i = w)).card = (s.filter (fun i => f i = -w)).card)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) (hfj : f j = - f i) :
    ∀ w : L, (((s.erase i).erase j).filter (fun k => f k = w)).card
           = (((s.erase i).erase j).filter (fun k => f k = -w)).card := by
  intro w
  have hsmall : ∀ u : L, (((s.erase i).erase j).filter (fun k => f k = u)).card
      = (s.filter (fun k => f k = u)).card
        - (if i ∈ s ∧ f i = u then 1 else 0)
        - (if j ∈ s.erase i ∧ f j = u then 1 else 0) := by
    intro u
    rw [card_filter_erase (s.erase i) (fun k => f k = u) j,
        card_filter_erase s (fun k => f k = u) i]
  have hjerase : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  rw [hsmall w, hsmall (-w)]
  have e1 : (if i ∈ s ∧ f i = w then (1:ℕ) else 0) = (if f i = w then 1 else 0) := by
    rw [eq_comm]; congr 1; simp [hi]
  have e2 : (if j ∈ s.erase i ∧ f j = w then (1:ℕ) else 0) = (if f j = w then 1 else 0) := by
    rw [eq_comm]; congr 1; simp [hjerase]
  have e3 : (if i ∈ s ∧ f i = -w then (1:ℕ) else 0) = (if f i = -w then 1 else 0) := by
    rw [eq_comm]; congr 1; simp [hi]
  have e4 : (if j ∈ s.erase i ∧ f j = -w then (1:ℕ) else 0) = (if f j = -w then 1 else 0) := by
    rw [eq_comm]; congr 1; simp [hjerase]
  rw [e1, e2, e3, e4]
  have s1 : (if f i = -w then (1:ℕ) else 0) = (if f j = w then 1 else 0) := by
    rw [hfj]; congr 1; apply propext; rw [neg_eq_iff_eq_neg, eq_comm]
  have s2 : (if f j = -w then (1:ℕ) else 0) = (if f i = w then 1 else 0) := by
    rw [hfj]; congr 1; apply propext; rw [neg_eq_iff_eq_neg, neg_neg]
  rw [s1, s2, hbal w]
  omega

/-- From fiber-card balance, a non-self-antipodal value `f i` has an index partner `j ≠ i`
in `s` with `f j = − f i` (its fiber is nonempty since `count(−f i) = count(f i) ≥ 1`). -/
private lemma partner_exists {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → L)
    (hbal : ∀ w : L, (s.filter (fun i => f i = w)).card = (s.filter (fun i => f i = -w)).card)
    {i : ι} (hi : i ∈ s) (hv : f i ≠ - f i) :
    ∃ j ∈ s, j ≠ i ∧ f j = - f i := by
  set v := f i with hvdef
  have hcard : 1 ≤ (s.filter (fun k => f k = -v)).card := by
    rw [← hbal v]; apply Finset.card_pos.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
  rw [Finset.mem_filter] at hj
  refine ⟨j, hj.1, ?_, hj.2⟩
  intro hji; rw [hji] at hj; exact hv hj.2

/-- **General index-pairing on a finset.** If the value fibers of `f` over `s` are
antipodally balanced and no `i ∈ s` is self-antipodal (`f i ≠ − f i`), then there is a
permutation `σ` of `ι` that fixes the complement of `s`, is a fixed-point-free involution
on `s`, maps `s` into `s`, and negates values (`f (σ i) = − f i`). Strong induction on
`s`, deleting a matched pair `(i, j)` each step (`balance_erase` keeps the hypotheses). -/
private lemma exists_pairing_finset {ι : Type*} [DecidableEq ι] (f : ι → L) :
    ∀ s : Finset ι,
      (∀ w : L, (s.filter (fun i => f i = w)).card = (s.filter (fun i => f i = -w)).card) →
      (∀ i ∈ s, f i ≠ - f i) →
      ∃ σ : Equiv.Perm ι, Function.Involutive σ ∧ (∀ x, x ∉ s → σ x = x) ∧
        (∀ i ∈ s, σ i ≠ i ∧ σ i ∈ s ∧ f (σ i) = - f i) := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hbal hself
    rcases s.eq_empty_or_nonempty with hempty | ⟨i, hi⟩
    · refine ⟨Equiv.refl ι, fun x => rfl, ?_, ?_⟩
      · intro x _; rfl
      · intro k hk; rw [hempty] at hk; exact absurd hk (Finset.notMem_empty k)
    · have hvi : f i ≠ - f i := hself i hi
      obtain ⟨j, hjs, hji, hfj⟩ := partner_exists s f hbal hi hvi
      set s' := (s.erase i).erase j with hs'
      have hsub : s' ⊂ s := by
        apply (Finset.ssubset_iff_of_subset (by
          rw [hs']; exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _))).mpr
        exact ⟨i, hi, by rw [hs']; simp⟩
      have hbal' := balance_erase s f hbal hi hjs hji.symm hfj
      have hself' : ∀ k ∈ s', f k ≠ - f k := by
        intro k hk
        rw [hs'] at hk
        have hks : k ∈ s := (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk))
        exact hself k hks
      obtain ⟨σ', hσinv, hσout, hσin⟩ := ih s' hsub hbal' hself'
      have his' : i ∉ s' := by rw [hs']; simp
      have hjs' : j ∉ s' := by rw [hs']; simp
      have hfixi : σ' i = i := hσout i his'
      have hfixj : σ' j = j := hσout j hjs'
      set σ := (Equiv.swap i j).trans σ' with hσdef
      have hσapp : ∀ x, σ x = σ' ((Equiv.swap i j) x) := fun x => Equiv.trans_apply _ _ x
      have hsi : σ i = j := by rw [hσapp, Equiv.swap_apply_left, hfixj]
      have hsj : σ j = i := by rw [hσapp, Equiv.swap_apply_right, hfixi]
      have hsOut : ∀ x, x ∉ s → σ x = x := by
        intro x hx
        have hxi : x ≠ i := fun h => hx (h ▸ hi)
        have hxj : x ≠ j := fun h => hx (h ▸ hjs)
        rw [hσapp, Equiv.swap_apply_of_ne_of_ne hxi hxj]
        exact hσout x (fun hxin => hx ((Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hs' ▸ hxin)))))
      have hsIn' : ∀ x ∈ s', σ x = σ' x := by
        intro x hx
        have hxi : x ≠ i := fun h => his' (h ▸ hx)
        have hxj : x ≠ j := fun h => hjs' (h ▸ hx)
        rw [hσapp, Equiv.swap_apply_of_ne_of_ne hxi hxj]
      refine ⟨σ, ?_, hsOut, ?_⟩
      · intro x
        by_cases hxi : x = i
        · subst hxi; rw [hsi, hsj]
        by_cases hxj : x = j
        · subst hxj; rw [hsj, hsi]
        by_cases hxs' : x ∈ s'
        · rw [hsIn' x hxs', hsIn' (σ' x) ((hσin x hxs').2.1)]
          exact hσinv x
        · have hxs : x ∉ s := by
            intro h
            have : x ∈ s' := by
              rw [hs']; exact Finset.mem_erase.mpr ⟨hxj, Finset.mem_erase.mpr ⟨hxi, h⟩⟩
            exact hxs' this
          rw [hsOut x hxs, hsOut x hxs]
      · intro k hk
        by_cases hki : k = i
        · subst hki
          refine ⟨?_, ?_, ?_⟩
          · rw [hsi]; exact hji
          · rw [hsi]; exact hjs
          · rw [hsi]; exact hfj
        by_cases hkj : k = j
        · subst hkj
          refine ⟨?_, ?_, ?_⟩
          · rw [hsj]; exact (Ne.symm hji)
          · rw [hsj]; exact hi
          · rw [hsj, hfj, neg_neg]
        · have hks' : k ∈ s' := by
            rw [hs']; exact Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, hk⟩⟩
          obtain ⟨hne, hmem, hval⟩ := hσin k hks'
          rw [hsIn' k hks']
          refine ⟨hne, ?_, hval⟩
          exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hs' ▸ hmem))

/-- **The index-involution lifting lemma (discharges residual `H`).** If the value
multiset `(map f univ)` of an even-length tuple `f : Fin (2r) → L` is antipodally balanced
(`count w = count (−w)` for all `w`) and no coordinate is self-antipodal (`f i ≠ − f i`,
e.g. `f i ≠ 0` in characteristic `≠ 2`), then there is a fixed-point-free involution `σ` on
the indices pairing each `i` with a partner of negated value: `f (σ i) = − f i`. This lifts
multiset count-balance to an INDEX-level pairing — exactly the `∃ σ, IsPairing σ ∧
∀ i, f (σ i) = − f i` hypothesis consumed by `zeroSumCount_le_pairings`. -/
theorem exists_pairing_of_count_balanced {r : ℕ}
    (f : Fin (2 * r) → L)
    (hbal : ∀ w : L, (Finset.univ.val.map f).count w = (Finset.univ.val.map f).count (-w))
    (hself : ∀ i, f i ≠ - f i) :
    ∃ σ : Equiv.Perm (Fin (2 * r)),
      Function.Involutive σ ∧ (∀ i, σ i ≠ i) ∧ (∀ i, f (σ i) = - f i) := by
  classical
  have hcount : ∀ w : L, (Finset.univ.val.map f).count w
      = ((Finset.univ : Finset (Fin (2 * r))).filter (fun i => f i = w)).card := by
    intro w
    rw [Multiset.count_map]
    simp only [Finset.filter]
    congr 1
    apply Multiset.filter_congr
    intro a _
    exact eq_comm
  have hbalF : ∀ w : L,
      ((Finset.univ : Finset (Fin (2 * r))).filter (fun i => f i = w)).card
        = ((Finset.univ : Finset (Fin (2 * r))).filter (fun i => f i = -w)).card := by
    intro w; rw [← hcount, ← hcount]; exact hbal w
  obtain ⟨σ, hinv, _hout, hin⟩ :=
    exists_pairing_finset f Finset.univ hbalF (fun i _ => hself i)
  refine ⟨σ, hinv, ?_, ?_⟩
  · intro i; exact (hin i (Finset.mem_univ i)).1
  · intro i; exact (hin i (Finset.mem_univ i)).2.2

/-- Packaged as the `IsPairing` predicate (the exact shape consumed by
`zeroSumCount_le_pairings`'s residual `H`). -/
theorem exists_isPairing_of_count_balanced {r : ℕ}
    (f : Fin (2 * r) → L)
    (hbal : ∀ w : L, (Finset.univ.val.map f).count w = (Finset.univ.val.map f).count (-w))
    (hself : ∀ i, f i ≠ - f i) :
    ∃ σ : Equiv.Perm (Fin (2 * r)), IsPairing σ ∧ (∀ i, f (σ i) = - f i) := by
  obtain ⟨σ, hinv, hfix, hval⟩ := exists_pairing_of_count_balanced f hbal hself
  exact ⟨σ, ⟨hinv, hfix⟩, hval⟩

end ArkLib.ProximityGap.NegationClosedWalk

#print axioms ArkLib.ProximityGap.NegationClosedWalk.exists_pairing_of_count_balanced
#print axioms ArkLib.ProximityGap.NegationClosedWalk.exists_isPairing_of_count_balanced
