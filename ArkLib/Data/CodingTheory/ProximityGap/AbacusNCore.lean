/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# The abacus `n`-core and its emptiness criterion (#389)

This is the combinatorial companion to `RootsOfUnityVandermonde`. The β-numbers of a partition
`λ` (padded to `n` parts), `β_j = λ_j + (n-1-j)`, are `n` distinct naturals. James–Kerber's
*abacus* places one bead at each `β_j` on `n` vertical runners indexed by `β_j mod n`; sliding
every bead down its runner ("gravity") yields the β-set of the **`n`-core** of `λ`.

We formalize the abacus directly and prove the criterion used in the prize obstruction:

> **`nCoreEmpty_iff_injOn_mod`** — the abacus `n`-core is *empty* (gravity returns the trivial
> β-set `{0,1,…,n-1}`) **iff** the bead residues `β_j mod n` are pairwise distinct, i.e. the
> beads occupy every runner exactly once.

Combined with `genVandermonde_rootsOfUnity_det_ne_zero_iff`, this gives the exact statement: at a
smooth domain `μ_n`, the higher-order-MDS determinant for `λ` vanishes **iff** the `n`-core of
`λ` is nonempty. (That the abacus core agrees with rim-hook removal is the classical
James–Kerber theorem, cited; here `nCoreEmpty` is taken as the abacus definition.)

Axiom-clean; finite combinatorics over `Fin n`.
-/

open Finset

namespace ArkLib.ProximityGap.AbacusNCore

variable {n : ℕ}

/-- Number of beads on runner `r`: how many β-numbers are `≡ r (mod n)`. -/
def beadsOnRunner (β : Fin n → ℕ) (r : ℕ) : ℕ :=
  (univ.filter (fun j : Fin n => β j % n = r)).card

/-- The β-set after gravity: on each runner `r` the beads slide to the lowest `beadsOnRunner β r`
slots `r, r+n, r+2n, …`. -/
def gravityBeta (β : Fin n → ℕ) : Finset ℕ :=
  (range n).biUnion fun r => (range (beadsOnRunner β r)).image fun t => r + t * n

/-- The abacus `n`-core is **empty** when gravity returns the trivial β-set `{0,1,…,n-1}`
(the β-set of the empty partition on `n` beads). -/
def nCoreEmpty (β : Fin n → ℕ) : Prop := gravityBeta β = range n

/-- The total number of beads is `n`: every `j : Fin n` lands on exactly one runner. -/
theorem sum_beadsOnRunner (β : Fin n → ℕ) :
    ∑ r ∈ range n, beadsOnRunner β r = n := by
  classical
  unfold beadsOnRunner
  rw [← Finset.card_biUnion]
  · have : (range n).biUnion (fun r => univ.filter (fun j : Fin n => β j % n = r))
        = (univ : Finset (Fin n)) := by
      ext j
      simp only [mem_biUnion, mem_range, mem_filter, mem_univ, true_and]
      exact ⟨fun _ => trivial, fun _ => ⟨β j % n, Nat.mod_lt _ (by
        rcases n with _ | m
        · exact (Fin.elim0 j)
        · exact Nat.succ_pos m), rfl⟩⟩
    rw [this, Finset.card_univ, Fintype.card_fin]
  · intro a _ b _ hab
    simp only [Finset.disjoint_left, mem_filter, mem_univ, true_and]
    rintro j hja hjb; exact hab (hja ▸ hjb)

/-- Each runner has at most one bead iff the residue map is injective. -/
theorem injOn_mod_iff_beads_le_one (β : Fin n → ℕ) :
    Function.Injective (fun j : Fin n => β j % n) ↔ ∀ r ∈ range n, beadsOnRunner β r ≤ 1 := by
  classical
  unfold beadsOnRunner
  constructor
  · intro hinj r _
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact hinj (show β a % n = β b % n by rw [ha, hb])
  · intro h a b hab
    by_contra hne
    have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact a.elim0)
    have hr : β a % n ∈ range n := mem_range.mpr (Nat.mod_lt _ hn)
    have hsub : ({a, b} : Finset (Fin n)) ⊆ univ.filter (fun j : Fin n => β j % n = β a % n) := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      simp only [mem_filter, mem_univ, true_and]
      rcases hx with rfl | rfl
      · rfl
      · exact hab.symm
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at hcard
    have h21 : (2 : ℕ) ≤ 1 := le_trans hcard (h _ hr)
    omega

/-- All runners have at most one bead iff all have exactly one (since there are `n` beads on
`n` runners). -/
theorem beads_le_one_iff_eq_one (β : Fin n → ℕ) :
    (∀ r ∈ range n, beadsOnRunner β r ≤ 1) ↔ ∀ r ∈ range n, beadsOnRunner β r = 1 := by
  constructor
  · intro hle
    have hsum := sum_beadsOnRunner β
    by_contra hcon
    push Not at hcon
    obtain ⟨r₀, hr₀, hne⟩ := hcon
    have hlt : beadsOnRunner β r₀ < 1 := lt_of_le_of_ne (hle r₀ hr₀) hne
    have hcontra : ∑ r ∈ range n, beadsOnRunner β r < n := by
      calc ∑ r ∈ range n, beadsOnRunner β r
          < ∑ _r ∈ range n, 1 :=
            Finset.sum_lt_sum (fun i hi => hle i hi) ⟨r₀, hr₀, hlt⟩
        _ = n := by rw [Finset.sum_const, card_range]; simp
    rw [hsum] at hcontra; exact lt_irrefl n hcontra
  · intro h r hr; exact le_of_eq (h r hr)

/-- **Emptiness criterion.** The abacus `n`-core is empty iff the β-residues are pairwise
distinct (one bead per runner). -/
theorem nCoreEmpty_iff_injOn_mod (β : Fin n → ℕ) :
    nCoreEmpty β ↔ Function.Injective (fun j : Fin n => β j % n) := by
  classical
  rw [injOn_mod_iff_beads_le_one, beads_le_one_iff_eq_one]
  unfold nCoreEmpty gravityBeta
  constructor
  · -- gravity = range n  ⟹  each runner has exactly one bead
    intro hg r hr
    have hrn : r < n := mem_range.mp hr
    rcases Nat.lt_trichotomy (beadsOnRunner β r) 1 with h0 | h1 | h2
    · -- 0 beads: r ∈ range n = gravity, so r = r' + t*n with t < beads r'; forces r'=r,t=0,
      -- contradicting beads r = 0
      exfalso
      have hb0 : beadsOnRunner β r = 0 := by omega
      have hrmem : r ∈ (range n).biUnion
          fun r => (range (beadsOnRunner β r)).image fun t => r + t * n := by rw [hg]; exact hr
      rw [mem_biUnion] at hrmem
      obtain ⟨r', hr', hr'2⟩ := hrmem
      rw [mem_image] at hr'2
      obtain ⟨t, ht, heq⟩ := hr'2
      rw [mem_range] at hr' ht
      have hn : 0 < n := by omega
      have ht0 : t = 0 := by
        by_contra htne
        have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr htne
        have hle : n ≤ t * n := by calc n = 1 * n := (one_mul n).symm
          _ ≤ t * n := by gcongr
        omega
      subst ht0
      simp only [Nat.zero_mul, Nat.add_zero] at heq
      subst heq
      rw [hb0] at ht; exact Nat.lt_irrefl 0 ht
    · exact h1
    · -- ≥2 beads: r + 1*n ∈ gravity but r + n ≥ n ∉ range n
      exfalso
      have hmem : r + 1 * n ∈ (range n).biUnion
          fun r => (range (beadsOnRunner β r)).image fun t => r + t * n :=
        mem_biUnion.mpr ⟨r, hr, mem_image.mpr ⟨1, mem_range.mpr (by omega), rfl⟩⟩
      rw [hg, mem_range] at hmem
      have : 0 < n := by omega
      omega
  · -- each runner has exactly one bead ⟹ gravity = range n
    intro h
    ext x
    simp only [mem_biUnion, mem_range, mem_image]
    constructor
    · rintro ⟨r, hr, t, ht, rfl⟩
      rw [h r (mem_range.mpr hr), Nat.lt_one_iff] at ht
      subst ht; simpa using hr
    · intro hx
      refine ⟨x, hx, 0, ?_, ?_⟩
      · rw [h x (mem_range.mpr hx)]; exact Nat.zero_lt_one
      · simp

end ArkLib.ProximityGap.AbacusNCore
