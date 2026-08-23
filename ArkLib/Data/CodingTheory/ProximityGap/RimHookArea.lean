/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Relation
import Mathlib.Tactic.Ring

/-!
# Rim-hook (border-strip) removal and partition area (#389)

This file builds the size theory of rim hooks (border strips) directly on the β-set
(Maya-diagram) representation of a partition, the standard rigorous foundation for the
James–Kerber `n`-core theory and the layer Mathlib does not yet provide.

A partition is presented by a bead set `B : Finset ℕ` (the β-numbers). Its **area** `|λ|` is
`(∑ b ∈ B) - C(|B|, 2)` — the number of cells, since the minimal β-set `{0,1,…,|B|-1}` (the empty
partition) has sum `C(|B|,2)`. Removing a **rim hook of size `n`** is the bead-move that slides one
bead at position `p ≥ n` down to the empty slot `p - n` (this is the Maya-diagram form of removing
a connected size-`n` border strip).

Main results:
* **`area_removeRimHook`** — removing a rim `n`-hook decreases the area by **exactly `n`**. This is
  why `n`-cores govern divisibility by `n`.
* **`area_reducesTo`** — after any sequence of rim-`n`-hook removals, the area drops by a multiple
  of `n`; hence `|λ| ≡ |n\text{-core}| (\mathrm{mod}\ n)`.

Axiom-clean; big-operator arithmetic over `Finset ℕ`.
-/

open Finset

namespace ArkLib.ProximityGap.RimHookArea

variable {n : ℕ}

/-- The area `|λ|` of the partition with β-set `B`: `(∑ B) - C(|B|, 2)`, as an integer. -/
def area (B : Finset ℕ) : ℤ := (∑ b ∈ B, (b : ℤ)) - (B.card.choose 2 : ℤ)

/-- `B'` is obtained from `B` by removing a rim hook of size `n`: a bead at `p ≥ n` slides down
to the empty slot `p - n`. -/
def RemovesRimHook (B B' : Finset ℕ) (n : ℕ) : Prop :=
  ∃ p ∈ B, n ≤ p ∧ p - n ∉ B ∧ B' = insert (p - n) (B.erase p)

/-- Rim-hook removal preserves the number of beads. -/
theorem card_removeRimHook {B B' : Finset ℕ} (h : RemovesRimHook B B' n) :
    B'.card = B.card := by
  obtain ⟨p, hp, _, hpn', rfl⟩ := h
  have hpos : 1 ≤ B.card := Finset.card_pos.mpr ⟨p, hp⟩
  rw [Finset.card_insert_of_notMem (by simp [Finset.mem_erase, hpn']),
    Finset.card_erase_of_mem hp]
  omega

/-- **Border-strip size law.** Removing a rim `n`-hook decreases the partition area by exactly
`n`. -/
theorem area_removeRimHook {B B' : Finset ℕ} (h : RemovesRimHook B B' n) :
    area B' = area B - n := by
  obtain ⟨p, hp, hpn, hpn', rfl⟩ := h
  have hpe : p - n ∉ B.erase p := by simp [Finset.mem_erase, hpn']
  have hsum : ∑ b ∈ insert (p - n) (B.erase p), (b : ℤ) = (∑ b ∈ B, (b : ℤ)) - n := by
    rw [Finset.sum_insert hpe]
    have herase : (p : ℤ) + ∑ b ∈ B.erase p, (b : ℤ) = ∑ b ∈ B, (b : ℤ) :=
      Finset.add_sum_erase B (fun b => (b : ℤ)) hp
    have hcast : ((p - n : ℕ) : ℤ) = (p : ℤ) - n := by omega
    rw [hcast]; omega
  have hpos : 1 ≤ B.card := Finset.card_pos.mpr ⟨p, hp⟩
  have hcard : (insert (p - n) (B.erase p)).card = B.card := by
    rw [Finset.card_insert_of_notMem hpe, Finset.card_erase_of_mem hp]; omega
  unfold area
  rw [hsum, hcard]
  omega
/-- `ReducesTo B B'`: `B'` is reached from `B` by a (possibly empty) sequence of rim-`n`-hook
removals. -/
def ReducesTo (n : ℕ) (B B' : Finset ℕ) : Prop :=
  Relation.ReflTransGen (fun a b => RemovesRimHook a b n) B B'

/-- **Area drops by a multiple of `n`.** After any sequence of rim-`n`-hook removals the area
decreases by a nonnegative multiple of `n`; in particular `area B ≡ area B' (mod n)`. Taking `B'`
to be the `n`-core gives `|λ| ≡ |n\text{-core}| (mod n)`. -/
theorem area_reducesTo {B B' : Finset ℕ} (h : ReducesTo n B B') :
    ∃ k : ℕ, area B' = area B - k * n := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | tail _ hstep ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      rw [area_removeRimHook hstep, hk, Nat.cast_add, Nat.cast_one]
      ring

/-- Consequence: the area is congruent to the `n`-core's area modulo `n`. -/
theorem area_congr_reducesTo {B B' : Finset ℕ} (h : ReducesTo n B B') :
    (n : ℤ) ∣ (area B - area B') := by
  obtain ⟨k, hk⟩ := area_reducesTo h
  exact ⟨k, by rw [hk]; ring⟩
