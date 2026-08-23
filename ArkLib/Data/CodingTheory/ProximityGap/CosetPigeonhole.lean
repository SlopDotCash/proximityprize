/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusCollapse

/-!
# The pigeonhole quarter: large exponent sets always contain a full coset

Campaign #357. The contains-a-coset obligation is **unconditional** on the top quarter of
sizes, with no balance hypothesis at all: a subset of the smooth scale with more than
`3·(n/4)` elements must fill some coset of the order-4 subgroup (each of the `n/4` cosets
holds at most 3 elements of a coset-free set):

> **`contains_coset_of_large`** — `A ⊆ range (2^m)`, `3 · 2^(m-2) < |A|` ⟹ the reduction
> of `A` contains a full coset `{x, x+q, x+h, x+q+h}`.

Consequence: every `ContainsCosetHyp` instance with `|A| > 3n/4` is discharged outright —
combined with the exhaustive sweeps (n = 16: complete · n = 32: complete · n = 64: a = 8)
this pins the obligation's remaining verification surface exactly.

## References

* `probe_coset_core_conjecture.py`, the C sweeps (issue thread); issue #357.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.WindowTwoLayer

variable {m : ℕ}

/-- **The pigeonhole quarter**: any subset of the scale with more than `3·(n/4)` elements
fills a coset of the order-4 subgroup — no balance needed. -/
theorem contains_coset_of_large (hm : 2 ≤ m) {A : Finset ℕ}
    (hsub : A ⊆ Finset.range (2 ^ m)) (hbig : 3 * 2 ^ (m - 2) < A.card) :
    ∃ x : ZMod (2 ^ m),
      x ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)) ∧
      x + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))
        ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)) ∧
      x + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)) ∧
      x + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)) := by
  classical
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero _ (by norm_num)⟩
  set Q : ℕ := 2 ^ (m - 2) with hQ
  have hQQ : Q + Q = 2 ^ (m - 1) := by
    have h := pow_succ 2 (m - 2)
    rw [show m - 2 + 1 = m - 1 by omega] at h
    omega
  have hHH : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
    omega
  -- partition A by residue class mod Q; some class has 4 elements
  have hclass : ∃ r < Q, 4 ≤ (A.filter (fun i => i % Q = r)).card := by
    by_contra hno
    push_neg at hno
    have hbound : A.card ≤ 3 * Q := by
      have hcover : A.card = ∑ r ∈ Finset.range Q, (A.filter (fun i => i % Q = r)).card := by
        rw [← Finset.card_biUnion]
        · congr 1
          ext i
          simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
          constructor
          · intro hi
            exact ⟨i % Q, Nat.mod_lt _ (by positivity), hi, rfl⟩
          · rintro ⟨r, -, hi, -⟩
            exact hi
        · intro r _ r' _ hrr
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro i h1 h2
          have e1 := (Finset.mem_filter.mp h1).2
          have e2 := (Finset.mem_filter.mp h2).2
          exact hrr (e1 ▸ e2 ▸ rfl)
      rw [hcover]
      calc ∑ r ∈ Finset.range Q, (A.filter (fun i => i % Q = r)).card
          ≤ ∑ _r ∈ Finset.range Q, 3 := by
            refine Finset.sum_le_sum fun r hr => ?_
            have := hno r (Finset.mem_range.mp hr)
            omega
        _ = 3 * Q := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
    omega
  obtain ⟨r, hrQ, hr4⟩ := hclass
  -- the class members are r, r+Q, r+2Q, r+3Q — exactly four candidates below 2^m
  set C : Finset ℕ := A.filter (fun i => i % Q = r) with hC
  have hCsub : C ⊆ Finset.range (2 ^ m) := fun i hi =>
    hsub (Finset.mem_filter.mp hi).1
  have hCmem : ∀ i ∈ C, i = r ∨ i = r + Q ∨ i = r + 2 * Q ∨ i = r + 3 * Q := by
    intro i hi
    have h1 : i % Q = r := (Finset.mem_filter.mp hi).2
    have h2 : i < 2 ^ m := Finset.mem_range.mp (hCsub hi)
    have h4Q : 4 * Q = 2 ^ m := by omega
    have := Nat.div_add_mod i Q
    have hdiv : i / Q < 4 := by
      by_contra hge
      push_neg at hge
      have : 4 * Q ≤ (i / Q) * Q := Nat.mul_le_mul_right _ hge
      have := Nat.div_mul_le_self i Q
      omega
    interval_cases h : (i / Q) <;> omega
  -- with at least 4 members among 4 candidates, all four are present
  have hall : r ∈ C ∧ r + Q ∈ C ∧ r + 2 * Q ∈ C ∧ r + 3 * Q ∈ C := by
    by_contra hmiss
    have hsub4 : C ⊆ ({r, r + Q, r + 2 * Q, r + 3 * Q} : Finset ℕ) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hCmem i hi with h | h | h | h <;> tauto
    -- if one candidate is missing, C fits in a 3-element set
    push_neg at hmiss
    have hQ0 : 0 < Q := pow_pos (by norm_num) _
    by_cases c1 : r ∈ C
    · by_cases c2 : r + Q ∈ C
      · by_cases c3 : r + 2 * Q ∈ C
        · have c4 := hmiss c1 c2 c3
          have : C ⊆ ({r, r + Q, r + 2 * Q} : Finset ℕ) := by
            intro i hi
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rcases hCmem i hi with h | h | h | h
            · tauto
            · tauto
            · tauto
            · exact absurd (h ▸ hi) c4
          have := Finset.card_le_card this
          have hle : ({r, r + Q, r + 2 * Q} : Finset ℕ).card ≤ 3 :=
            le_trans (Finset.card_insert_le _ _) (by
              have := Finset.card_insert_le (r + Q) ({r + 2 * Q} : Finset ℕ)
              simp at this ⊢
              omega)
          omega
        · have : C ⊆ ({r, r + Q, r + 3 * Q} : Finset ℕ) := by
            intro i hi
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rcases hCmem i hi with h | h | h | h
            · tauto
            · tauto
            · exact absurd (h ▸ hi) c3
            · tauto
          have := Finset.card_le_card this
          have hle : ({r, r + Q, r + 3 * Q} : Finset ℕ).card ≤ 3 :=
            le_trans (Finset.card_insert_le _ _) (by
              have := Finset.card_insert_le (r + Q) ({r + 3 * Q} : Finset ℕ)
              simp at this ⊢
              omega)
          omega
      · have : C ⊆ ({r, r + 2 * Q, r + 3 * Q} : Finset ℕ) := by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hCmem i hi with h | h | h | h
          · tauto
          · exact absurd (h ▸ hi) c2
          · tauto
          · tauto
        have := Finset.card_le_card this
        have hle : ({r, r + 2 * Q, r + 3 * Q} : Finset ℕ).card ≤ 3 :=
          le_trans (Finset.card_insert_le _ _) (by
            have := Finset.card_insert_le (r + 2 * Q) ({r + 3 * Q} : Finset ℕ)
            simp at this ⊢
            omega)
        omega
    · have : C ⊆ ({r + Q, r + 2 * Q, r + 3 * Q} : Finset ℕ) := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hCmem i hi with h | h | h | h
        · exact absurd (h ▸ hi) c1
        · tauto
        · tauto
        · tauto
      have := Finset.card_le_card this
      have hle : ({r + Q, r + 2 * Q, r + 3 * Q} : Finset ℕ).card ≤ 3 :=
        le_trans (Finset.card_insert_le _ _) (by
          have := Finset.card_insert_le (r + 2 * Q) ({r + 3 * Q} : Finset ℕ)
          simp at this ⊢
          omega)
      omega
  obtain ⟨m1, m2, m3, m4⟩ := hall
  -- assemble the coset at x = cast r
  have hmem : ∀ {i : ℕ}, i ∈ C →
      ((i : ℕ) : ZMod (2 ^ m)) ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)) := by
    intro i hi
    exact Multiset.mem_map.mpr ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩
  refine ⟨((r : ℕ) : ZMod (2 ^ m)), hmem m1, ?_, ?_, ?_⟩
  · have : ((r : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))
        = (((r + Q : ℕ) : ℕ) : ZMod (2 ^ m)) := by
      rw [hQ, ← Nat.cast_add]
    rw [this]
    exact hmem m2
  · have : ((r : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        = (((r + 2 * Q : ℕ) : ℕ) : ZMod (2 ^ m)) := by
      rw [← Nat.cast_add]
      congr 1
      omega
    rw [this]
    exact hmem m3
  · have : ((r : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))
        + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        = (((r + 3 * Q : ℕ) : ℕ) : ZMod (2 ^ m)) := by
      rw [hQ, ← Nat.cast_add, ← Nat.cast_add]
      congr 1
      omega
    rw [this]
    exact hmem m4

/-! ## Source audit -/

#print axioms contains_coset_of_large

end ArkLib.ProximityGap.WindowTwoLayer
