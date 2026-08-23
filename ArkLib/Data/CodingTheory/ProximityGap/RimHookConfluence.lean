/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RimHookArea
import ArkLib.Data.CodingTheory.ProximityGap.AbacusReduction

/-!
# Well-definedness of the `n`-core: confluence of rim-hook removal (#389)

The `n`-core of a partition is the result of removing rim `n`-hooks until none remain. For this to
be a well-defined invariant one must show the result is **independent of the order of removals**.
We prove this at the abacus level via the key structural invariant:

* **`runnerCount_removeRimHook`** — a rim-hook removal `p ↦ p-n` preserves the number of beads on
  every runner (residue class mod `n`), since `p ≡ p-n (mod n)`.
* **`rimHookFree_eq_of_runnerCount`** — a rim-hook-free bead set is *uniquely determined* by its
  per-runner counts (each runner is the down-closed block `{r, r+n, …}`).
* **`nCore_unique`** — therefore any two `n`-cores reachable from the same partition are equal: the
  `n`-core is well-defined.

This is the abacus-confluence half of James–Kerber (the remaining half — that an abacus bead-move
is geometrically a connected border strip — needs the Young-diagram rim-hook theory absent from
Mathlib). Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.RimHookConfluence

open ArkLib.ProximityGap.RimHookArea ArkLib.ProximityGap.AbacusReduction

variable {n : ℕ}

/-- Number of beads on runner `r`: beads of `B` with residue `r` mod `n`. -/
def runnerCount (B : Finset ℕ) (n r : ℕ) : ℕ := (B.filter (fun b => b % n = r)).card

/-- A rim-hook removal preserves the bead count on every runner: the moved bead `p` and its target
`p - n` lie on the same runner (`p ≡ p - n [MOD n]`). -/
theorem runnerCount_removeRimHook {B B' : Finset ℕ} (hn : 0 < n)
    (h : RemovesRimHook B B' n) (r : ℕ) :
    runnerCount B' n r = runnerCount B n r := by
  classical
  obtain ⟨p, hp, hpn, hpn', rfl⟩ := h
  unfold runnerCount
  have hres : (p - n) % n = p % n := by
    conv_rhs => rw [← Nat.sub_add_cancel hpn]
    rw [Nat.add_mod_right]
  have hpe : p - n ∉ B.erase p := by simp [Finset.mem_erase, hpn']
  by_cases hr : p % n = r
  · -- runner r: remove p, add p-n, both residue r ⟹ card unchanged
    rw [Finset.filter_insert]
    simp only [hres, hr, if_true]
    rw [Finset.card_insert_of_notMem (by simp [Finset.mem_filter, Finset.mem_erase, hpn']),
      Finset.filter_erase, Finset.card_erase_of_mem (by simp [Finset.mem_filter, hp, hr])]
    have : 1 ≤ (B.filter (fun b => b % n = r)).card :=
      Finset.card_pos.mpr ⟨p, by simp [Finset.mem_filter, hp, hr]⟩
    omega
  · -- other runners untouched
    rw [Finset.filter_insert]
    simp only [hres, hr, if_false]
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem (by simp [Finset.mem_filter, hr])]


/-- Runner counts are invariant under any sequence of rim-hook removals. -/
theorem runnerCount_reducesTo {B B' : Finset ℕ} (hn : 0 < n)
    (h : ReducesTo n B B') (r : ℕ) : runnerCount B' n r = runnerCount B n r := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [runnerCount_removeRimHook hn hstep r, ih]

/-- A predecessor-closed finite set of naturals is an initial segment `range`. -/
theorem downClosed_eq_range {T : Finset ℕ} (h : ∀ t ∈ T, 1 ≤ t → t - 1 ∈ T) :
    T = range T.card := by
  classical
  have step : ∀ d t, t ∈ T → t - d ∈ T := by
    intro d
    induction d with
    | zero => intro t ht; simpa using ht
    | succ k ih =>
        intro t ht
        rcases Nat.eq_zero_or_pos (t - k) with h0 | h1
        · have he : t - (k + 1) = t - k := by omega
          rw [he]; exact ih t ht
        · have he : t - (k + 1) = (t - k) - 1 := by omega
          rw [he]; exact h (t - k) (ih t ht) h1
  have desc : ∀ t ∈ T, ∀ j, j ≤ t → j ∈ T := by
    intro t ht j hj
    have := step (t - j) t ht
    rwa [show t - (t - j) = j by omega] at this
  ext m
  simp only [mem_range]
  constructor
  · intro hm
    -- {0,…,m} ⊆ T ⟹ m+1 ≤ card
    have hsub : range (m + 1) ⊆ T := by
      intro j hj; rw [mem_range] at hj; exact desc m hm j (by omega)
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this; omega
  · intro hm
    -- if m ∉ T then all of T is < m, so card ≤ m < card
    by_contra hmT
    have hlt : ∀ t ∈ T, t < m := by
      intro t ht
      by_contra hge
      push_neg at hge
      exact hmT (desc t ht m hge)
    have hsub : T ⊆ range m := fun t ht => mem_range.mpr (hlt t ht)
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this; omega

/-- **Per-runner membership.** For a rim-hook-free bead set, `r + t·n` is a bead iff `t` is below
the runner-`r` count: each runner is the down-closed block `{r, r+n, …, r+(c_r-1)n}`. -/
theorem mem_runner_iff (hn : 0 < n) {B : Finset ℕ} (hfree : RimHookFree B n)
    {r : ℕ} (hr : r < n) (t : ℕ) : r + t * n ∈ B ↔ t < runnerCount B n r := by
  classical
  set Tset := (B.filter (fun b => b % n = r)).image (fun b => b / n) with hT
  have hmem : ∀ s, s ∈ Tset ↔ r + s * n ∈ B := by
    intro s
    simp only [hT, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨b, ⟨hbB, hbr⟩, hbs⟩
      have hbeq : b = r + s * n := by
        conv_lhs => rw [← Nat.div_add_mod b n, hbr, hbs]
        ring
      rwa [hbeq] at hbB
    · intro hb
      refine ⟨r + s * n, ⟨hb, ?_⟩, ?_⟩
      · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
      · rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hr, Nat.zero_add]
  have hpred : ∀ s ∈ Tset, 1 ≤ s → s - 1 ∈ Tset := by
    intro s hs hs1
    rw [hmem] at hs ⊢
    have hge : n ≤ r + s * n := by
      calc n = 1 * n := (one_mul n).symm
        _ ≤ s * n := by gcongr
        _ ≤ r + s * n := Nat.le_add_left _ _
    have hmem2 := hfree (r + s * n) hs hge
    have heq : r + s * n - n = r + (s - 1) * n := by
      cases s with
      | zero => omega
      | succ m => rw [Nat.succ_sub_one, Nat.succ_mul]; omega
    rwa [heq] at hmem2
  have hinj : Set.InjOn (fun b => b / n) (B.filter (fun b => b % n = r) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    simp only at hab
    have hae : a = r + (a / n) * n := by
      conv_lhs => rw [← Nat.div_add_mod a n, ha.2]
      ring
    have hbe : b = r + (b / n) * n := by
      conv_lhs => rw [← Nat.div_add_mod b n, hb.2]
      ring
    rw [hae, hbe, hab]
  have hcard : Tset.card = runnerCount B n r := by
    rw [hT, Finset.card_image_of_injOn hinj]; rfl
  have hrange : Tset = range (runnerCount B n r) := by
    rw [← hcard]; exact downClosed_eq_range hpred
  rw [← hmem, hrange, mem_range]

/-- **Canonical form.** A rim-hook-free bead set is the union over runners of the down-closed
blocks — hence completely determined by its per-runner counts. -/
theorem rimHookFree_eq_canonical (hn : 0 < n) {B : Finset ℕ} (hfree : RimHookFree B n) :
    B = (range n).biUnion fun r => (range (runnerCount B n r)).image fun t => r + t * n := by
  classical
  ext b
  simp only [Finset.mem_biUnion, mem_range, Finset.mem_image]
  constructor
  · intro hb
    have hbr : b % n < n := Nat.mod_lt _ hn
    have hbeq : b = b % n + (b / n) * n := by
      conv_lhs => rw [← Nat.div_add_mod b n]
      ring
    refine ⟨b % n, hbr, b / n, ?_, ?_⟩
    · rw [← mem_runner_iff hn hfree hbr (b / n), ← hbeq]; exact hb
    · exact hbeq.symm
  · rintro ⟨r, hr, t, ht, rfl⟩
    rw [mem_runner_iff hn hfree hr t]; exact ht

/-- **The `n`-core is well-defined.** Any two rim-hook-free forms reachable from the same partition
are equal — the result of removing rim `n`-hooks does not depend on the order of removals. -/
theorem nCore_unique (hn : 0 < n) {B B₁ B₂ : Finset ℕ}
    (h₁ : ReducesTo n B B₁) (h₂ : ReducesTo n B B₂)
    (hf₁ : RimHookFree B₁ n) (hf₂ : RimHookFree B₂ n) : B₁ = B₂ := by
  rw [rimHookFree_eq_canonical hn hf₁, rimHookFree_eq_canonical hn hf₂]
  refine Finset.biUnion_congr rfl (fun r _ => ?_)
  rw [runnerCount_reducesTo hn h₁ r, runnerCount_reducesTo hn h₂ r]

end ArkLib.ProximityGap.RimHookConfluence
