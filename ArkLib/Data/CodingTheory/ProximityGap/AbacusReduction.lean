/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AbacusNCore

/-!
# Abacus reduction: the `n`-core form is rim-hook-irreducible (#389)

On the James–Kerber abacus, removing a rim `n`-hook from a partition corresponds to sliding one
bead **up** its runner by one slot: a bead at position `p ≥ n` moves to the empty slot `p - n`.
A β-set is the β-set of an `n`-**core** precisely when it admits *no* such move — every bead at
`p ≥ n` already has a bead below it at `p - n`. We call this `RimHookFree`.

This file proves the defining property of the core form produced by `gravityBeta`:

> **`gravityBeta_rimHookFree`** — the gravity (n-core) β-set admits no rim-`n`-hook removal.

So `gravityBeta β` is genuinely *reduced* under abacus rim-hook moves — the abacus-level content
of "it is the `n`-core." (The geometric identity *abacus bead-move = removing a connected border
strip of size `n` from the Young diagram* — the remaining half of James–Kerber — would require
rim-hook/border-strip theory that Mathlib does not yet provide; see the module docstring of
`AbacusNCore`.)

Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.AbacusReduction

open ArkLib.ProximityGap.AbacusNCore

variable {n : ℕ}

/-- A bead set `B` is **rim-hook-free** when no bead can slide up its runner: every bead at a
position `p ≥ n` already has a bead at `p - n`. This is the abacus characterization of being the
β-set of an `n`-core. -/
def RimHookFree (B : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ B, n ≤ p → p - n ∈ B

/-- **The `n`-core form admits no rim-hook removal.** -/
theorem gravityBeta_rimHookFree (β : Fin n → ℕ) : RimHookFree (gravityBeta β) n := by
  classical
  intro p hp hpn
  unfold gravityBeta at hp ⊢
  rw [mem_biUnion] at hp
  obtain ⟨r, hr, hp2⟩ := hp
  rw [mem_image] at hp2
  obtain ⟨t, ht, rfl⟩ := hp2
  rw [mem_range] at hr ht
  -- p = r + t*n ≥ n with r < n forces t ≥ 1; then p - n = r + (t-1)*n is on the same runner
  have htpos : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h1
    · subst h0; simp only [Nat.zero_mul, Nat.add_zero] at hpn; omega
    · exact h1
  have hge : n ≤ t * n := by
    calc n = 1 * n := (one_mul n).symm
      _ ≤ t * n := by gcongr
  have hsub : (t - 1) * n = t * n - n := by
    cases t with
    | zero => omega
    | succ m => simp [Nat.succ_sub_one, Nat.succ_mul]
  rw [mem_biUnion]
  refine ⟨r, mem_range.mpr hr, ?_⟩
  rw [mem_image]
  exact ⟨t - 1, mem_range.mpr (by omega), by omega⟩

end ArkLib.ProximityGap.AbacusReduction
