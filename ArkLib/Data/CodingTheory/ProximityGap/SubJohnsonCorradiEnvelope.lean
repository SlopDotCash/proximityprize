/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BoundarySliceEveryLine
import Mathlib.Algebra.Order.Chebyshev

/-!
# The Corrádi envelope: the sub-Johnson list upper bound, every word (#389)

The subset-sum fibre law's attained half is proven (`ladder_list_ge_fibre`).  This file
proves the matching **upper envelope for every word** by Corrádi/Cauchy–Schwarz counting:

> **`rs_list_corradi_bound`** — for any word `w` and any agreement threshold `a ≥ k`,
> with `L` = the number of `rsCode dom k` codewords at agreement `≥ a` with `w`:
>
>   `L·a² + n·(k−1) ≤ n·a + n·(k−1)·L`,
>
> equivalently `L ≤ n(a−k+1)/(a² − n(k−1))` whenever `a² > n(k−1)` — the whole strictly
> sub-Johnson range (`a² > n(k−1)` is even slightly wider than Johnson's `a² > nk`).

Mechanism: distinct codewords agree pairwise on `≤ k−1` points (degree-`<k`
determination), so with `deg(i) := #{list codewords agreeing with `w` at `i`}` the second
moment satisfies `Σ deg² = Σ_{c,c'}|A_c ∩ A_{c'}| ≤ Σ|A_c| + L(L−1)(k−1)`, while
Cauchy–Schwarz gives `(Σ deg)² ≤ n·Σ deg²`.

At `(16,3)`: `L ≤ 3` at `a = 8`, `L ≤ 4` at `a = 7`, against the proven fibre lower
bound `2` — the exact law is pinched between two machine-checked brackets on the entire
strictly sub-Johnson range; only `a² ≤ n(k−1)` (beyond Johnson) remains with the census
wall.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- Two `rsCode` codewords agreeing on `k` common points coincide. -/
private lemma rs_eq_of_agree {dom : Fin n ↪ F} {k : ℕ}
    {c c' : Fin n → F} (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hc' : c' ∈ (rsCode dom k : Submodule F (Fin n → F)))
    {S : Finset (Fin n)} (hS : k ≤ S.card) (hag : ∀ i ∈ S, c i = c' i) : c = c' := by
  obtain ⟨P, hP, rfl⟩ := hc
  obtain ⟨P', hP', rfl⟩ := hc'
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS
  have hPeq : P = P' := by
    refine Polynomial.eq_of_degrees_lt_of_eval_index_eq T
      (fun x _ y _ hxy => dom.injective hxy) ?_ ?_ ?_
    · rw [hTcard]; exact hP
    · rw [hTcard]; exact hP'
    · intro i hi
      exact hag i (hTS hi)
  rw [hPeq]

open Classical in
/-- **THE CORRÁDI ENVELOPE**: the additive sub-Johnson list bound, every word. -/
theorem rs_list_corradi_bound (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k) (hka : k ≤ a)
    (w : Fin n → F) :
    (Finset.univ.filter (fun c : Fin n → F =>
        c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (Finset.univ.filter (fun i : Fin n => c i = w i)).card)).card * (a * a)
      + n * (k - 1)
      ≤ n * a + n * (k - 1) *
        (Finset.univ.filter (fun c : Fin n → F =>
          c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
          a ≤ (Finset.univ.filter (fun i : Fin n => c i = w i)).card)).card := by
  classical
  set Lset := Finset.univ.filter (fun c : Fin n → F =>
      c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
      a ≤ (Finset.univ.filter (fun i : Fin n => c i = w i)).card) with hLdef
  set L := Lset.card with hL
  set t := k - 1 with ht
  set deg : Fin n → ℕ := fun i => (Lset.filter (fun c => c i = w i)).card with hdeg
  -- first double count
  have hS : ∑ c ∈ Lset, (Finset.univ.filter (fun i : Fin n => c i = w i)).card
      = ∑ i : Fin n, deg i := by
    simp only [hdeg, Finset.card_filter]
    exact Finset.sum_comm
  have hSge : L * a ≤ ∑ i : Fin n, deg i := by
    rw [← hS, hL]
    calc Lset.card * a = ∑ _c ∈ Lset, a := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum (fun c hc => (Finset.mem_filter.mp hc).2.2)
  set S := ∑ i : Fin n, deg i with hSdef
  -- second double count
  have hQ : ∑ i : Fin n, deg i ^ 2
      = ∑ c ∈ Lset, ∑ c' ∈ Lset,
          (Finset.univ.filter (fun i : Fin n => c i = w i ∧ c' i = w i)).card := by
    have hsq : ∀ i : Fin n, deg i ^ 2
        = ∑ c ∈ Lset, ∑ c' ∈ Lset,
            (if c i = w i ∧ c' i = w i then 1 else 0) := by
      intro i
      show (Lset.filter (fun c => c i = w i)).card ^ 2 = _
      rw [Finset.card_filter, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
      by_cases h1 : c i = w i <;> by_cases h2 : c' i = w i <;> simp [h1, h2]
    calc ∑ i : Fin n, deg i ^ 2
        = ∑ i : Fin n, ∑ c ∈ Lset, ∑ c' ∈ Lset,
            (if c i = w i ∧ c' i = w i then 1 else 0) :=
          Finset.sum_congr rfl fun i _ => hsq i
    _ = ∑ c ∈ Lset, ∑ i : Fin n, ∑ c' ∈ Lset,
            (if c i = w i ∧ c' i = w i then 1 else 0) := Finset.sum_comm
    _ = ∑ c ∈ Lset, ∑ c' ∈ Lset, ∑ i : Fin n,
            (if c i = w i ∧ c' i = w i then 1 else 0) :=
          Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = _ := by
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
          rw [Finset.card_filter]
  -- the pair bound
  have hQle : ∑ i : Fin n, deg i ^ 2 ≤ S + L * ((L - 1) * t) := by
    rw [hQ]
    have hper : ∀ c ∈ Lset, ∑ c' ∈ Lset,
        (Finset.univ.filter (fun i : Fin n => c i = w i ∧ c' i = w i)).card
        ≤ (Finset.univ.filter (fun i : Fin n => c i = w i)).card + (L - 1) * t := by
      intro c hc
      rw [← Finset.sum_filter_add_sum_filter_not Lset (fun c' => c' = c)]
      refine add_le_add ?_ ?_
      · refine le_trans (Finset.sum_le_sum (fun c' _ =>
          Finset.card_le_card (fun i hi => Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.1⟩))) ?_
        rw [Finset.sum_const, smul_eq_mul]
        refine le_trans (Nat.mul_le_mul_right _
          (Finset.card_le_one.mpr (fun x hx y hy =>
            ((Finset.mem_filter.mp hx).2).trans
              ((Finset.mem_filter.mp hy).2).symm))) ?_
        rw [one_mul]
      · have hcardne : (Lset.filter (fun c' => ¬ c' = c)).card ≤ L - 1 := by
          have hsplit : (Lset.filter (fun c' => c' = c)).card
              + (Lset.filter (fun c' => ¬ c' = c)).card = Lset.card :=
            Finset.card_filter_add_card_filter_not _
          have hone : 1 ≤ (Lset.filter (fun c' => c' = c)).card :=
            Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, rfl⟩⟩
          omega
        refine le_trans (Finset.sum_le_sum (g := fun _ => t) (fun c' hc' => ?_)) ?_
        · -- each off-diagonal intersection ≤ t
          by_contra hgt
          push Not at hgt
          have hne : c' ≠ c := (Finset.mem_filter.mp hc').2
          have hagree : ∀ i ∈ Finset.univ.filter
              (fun i : Fin n => c i = w i ∧ c' i = w i), c i = c' i := by
            intro i hi
            obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hi
            rw [h1, h2]
          exact hne ((rs_eq_of_agree (Finset.mem_filter.mp hc).2.1
            (Finset.mem_filter.mp (Finset.mem_of_mem_filter c' hc')).2.1
            (by omega : k ≤ (Finset.univ.filter
              (fun i : Fin n => c i = w i ∧ c' i = w i)).card) hagree)).symm
        · rw [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right t hcardne
    calc ∑ c ∈ Lset, ∑ c' ∈ Lset,
        (Finset.univ.filter (fun i : Fin n => c i = w i ∧ c' i = w i)).card
        ≤ ∑ c ∈ Lset, ((Finset.univ.filter (fun i : Fin n => c i = w i)).card
            + (L - 1) * t) := Finset.sum_le_sum hper
    _ = (∑ c ∈ Lset, (Finset.univ.filter (fun i : Fin n => c i = w i)).card)
          + Lset.card * ((L - 1) * t) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    _ = S + L * ((L - 1) * t) := by rw [hS, ← hL]
  -- Cauchy–Schwarz
  have hCS : S ^ 2 ≤ n * ∑ i : Fin n, deg i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := deg)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  -- assembly
  by_cases hL0 : L = 0
  · rw [hL0]
    have h1 : n * t ≤ n * a := Nat.mul_le_mul_left n (by omega)
    omega
  have hL1 : 1 ≤ L := Nat.pos_of_ne_zero hL0
  by_cases hcase : L * a ≤ n
  · have h1 : L * (a * a) ≤ n * a := by
      calc L * (a * a) = (L * a) * a := by ring
      _ ≤ n * a := Nat.mul_le_mul_right a hcase
    have h2 : n * t ≤ n * t * L := Nat.le_mul_of_pos_right _ hL1
    omega
  · push Not at hcase
    have hchain : (L * a) * S ≤ n * S + n * (L * ((L - 1) * t)) := by
      calc (L * a) * S ≤ S * S := Nat.mul_le_mul_right S hSge
      _ = S ^ 2 := (sq S).symm
      _ ≤ n * ∑ i : Fin n, deg i ^ 2 := hCS
      _ ≤ n * (S + L * ((L - 1) * t)) := Nat.mul_le_mul_left n hQle
      _ = n * S + n * (L * ((L - 1) * t)) := by ring
    have h3 : (L * a - n) * S ≤ n * (L * ((L - 1) * t)) := by
      rw [Nat.sub_mul]
      exact Nat.sub_le_iff_le_add.mpr (hchain.trans_eq (Nat.add_comm _ _))
    have h4 : (L * a - n) * (L * a) ≤ n * (L * ((L - 1) * t)) :=
      le_trans (Nat.mul_le_mul_left _ hSge) h3
    -- cancel one factor of L
    have h5 : ((L * a - n) * a) * L ≤ (n * ((L - 1) * t)) * L := by
      calc ((L * a - n) * a) * L = (L * a - n) * (L * a) := by ring
      _ ≤ n * (L * ((L - 1) * t)) := h4
      _ = (n * ((L - 1) * t)) * L := by ring
    have h6 : (L * a - n) * a ≤ n * ((L - 1) * t) :=
      Nat.le_of_mul_le_mul_right h5 hL1
    -- expand the subtractions
    have h7 : L * (a * a) - n * a ≤ n * ((L - 1) * t) := by
      calc L * (a * a) - n * a = (L * a) * a - n * a := by ring_nf
      _ = (L * a - n) * a := (Nat.sub_mul _ _ _).symm
      _ ≤ _ := h6
    have h8 : n * ((L - 1) * t) = n * (L * t) - n * t := by
      rw [Nat.sub_mul, one_mul, Nat.mul_sub]
    have h9 : n * t ≤ n * (L * t) := by
      refine Nat.mul_le_mul_left n ?_
      calc t = 1 * t := (one_mul t).symm
      _ ≤ L * t := Nat.mul_le_mul_right t hL1
    have h10 : L * (a * a) ≤ n * a + (n * (L * t) - n * t) := by
      rw [← h8]
      exact Nat.sub_le_iff_le_add.mp (h7.trans_eq rfl) |>.trans_eq (Nat.add_comm _ _)
    calc L * (a * a) + n * t ≤ (n * a + (n * (L * t) - n * t)) + n * t :=
          Nat.add_le_add_right h10 _
    _ = n * a + n * (L * t) := by
          rw [Nat.add_assoc, Nat.sub_add_cancel h9]
    _ = n * a + n * t * L := by ring

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.rs_list_corradi_bound
