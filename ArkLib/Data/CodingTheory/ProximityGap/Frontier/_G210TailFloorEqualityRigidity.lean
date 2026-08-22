/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G209TailFloorPartitionEngine

/-!
# G210: equality rigidity for the dyadic depth-two tail floor (#466, #509)

G209 proves that a positive partition `ks` of `n-1` into at most `n/2` parts satisfies

`sum k in ks, k^2 >= 2n-3`.

This file identifies the equality case exactly.  For even `n >= 2`, equality holds if and only if

* the class-count cap is saturated: `card ks = n/2`; and
* every occupied multiplicity is `1` or `2`.

The sum condition then forces exactly one part equal to `1`; all other `n/2-1` parts equal `2`.
Thus G209's witness `[2,...,2,1]` is not merely one minimizer: it is the unique multiplicity
histogram, up to permutation.

This is the correct unconditional replacement for an empirically tempting but false-shaped claim
that every sufficiently large prime realizes the floor.  For the CORE object, equality is a
per-prime flatness certificate.  Failure means that the characteristic-p quotient-class map merges
at least two involution-pair contributions, producing a part at least `3` or leaving the class-count
cap unsaturated.  FS15-FS18 can bound such resultant accidents only in fixed-depth prime families;
they do not certify the sponsor prime or an eventual threshold.

This is structural frontier movement, not a prize closure.  The simultaneous signed `r=5,6`
cyclotomic covariance remains open / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G210

open Multiset
open ArkLib.ProximityGap.Frontier.G209

/-- Equality in the summed G209 engine forces equality in every pointwise inequality, hence every
positive part is at most two. -/
theorem all_le_two_of_engine_eq
    (ks : Multiset ℕ)
    (hpos : ∀ k ∈ ks, 1 ≤ k)
    (heq : 3 * ks.sum = (ks.map (· ^ 2)).sum + 2 * ks.card) :
    ∀ k ∈ ks, k ≤ 2 := by
  induction ks using Multiset.induction with
  | empty => simp
  | @cons a s ih =>
      have ha := three_mul_le_sq_add_two a
      have hs := three_mul_sum_le_sumSq_add_two_mul_card s
      simp only [Multiset.sum_cons, Multiset.map_cons, Multiset.card_cons] at heq
      have hae : 3 * a = a ^ 2 + 2 := by omega
      have hse : 3 * s.sum = (s.map (· ^ 2)).sum + 2 * s.card := by omega
      intro k hk
      simp only [Multiset.mem_cons] at hk
      rcases hk with hk | hk
      · subst k
        have ha1 : 1 ≤ a := hpos a (Multiset.mem_cons_self a s)
        nlinarith
      · exact ih (fun x hx => hpos x (Multiset.mem_cons_of_mem hx)) hse k hk

/-- Conversely, a multiset whose positive parts are all at most two saturates the summed engine. -/
theorem engine_eq_of_all_le_two
    (ks : Multiset ℕ)
    (hpos : ∀ k ∈ ks, 1 ≤ k)
    (hle : ∀ k ∈ ks, k ≤ 2) :
    3 * ks.sum = (ks.map (· ^ 2)).sum + 2 * ks.card := by
  induction ks using Multiset.induction with
  | empty => simp
  | @cons a s ih =>
      have ha1 : 1 ≤ a := hpos a (Multiset.mem_cons_self a s)
      have ha2 : a ≤ 2 := hle a (Multiset.mem_cons_self a s)
      have hae := three_mul_eq_sq_add_two_of_le_two ha1 ha2
      have hse := ih
        (fun x hx => hpos x (Multiset.mem_cons_of_mem hx))
        (fun x hx => hle x (Multiset.mem_cons_of_mem hx))
      simp only [Multiset.sum_cons, Multiset.map_cons, Multiset.card_cons]
      omega

/-- **Exact equality case of the G209 tail floor.**  The lower bound is attained exactly when the
class-count cap is saturated and every multiplicity is `1` or `2`. -/
theorem tail_sumSq_eq_iff_flat
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (ks : Multiset ℕ)
    (hpos : ∀ k ∈ ks, 1 ≤ k)
    (hsum : ks.sum = n - 1)
    (hcard : ks.card ≤ n / 2) :
    (ks.map (· ^ 2)).sum = 2 * n - 3 ↔
      ks.card = n / 2 ∧ ∀ k ∈ ks, k ≤ 2 := by
  obtain ⟨m, rfl⟩ := heven
  have hm : 1 ≤ m := by omega
  have hdiv : (m + m) / 2 = m := by omega
  rw [hdiv] at hcard ⊢
  constructor
  · intro hsq
    have heng := three_mul_sum_le_sumSq_add_two_mul_card ks
    rw [hsum, hsq] at heng
    have hcardEq : ks.card = m := by omega
    have heq : 3 * ks.sum = (ks.map (· ^ 2)).sum + 2 * ks.card := by
      rw [hsum, hsq, hcardEq]
      omega
    exact ⟨hcardEq, all_le_two_of_engine_eq ks hpos heq⟩
  · rintro ⟨hcardEq, hle⟩
    have heq := engine_eq_of_all_le_two ks hpos hle
    rw [hsum, hcardEq] at heq
    omega

/-- For a positive `1/2`-valued multiset, the number of ones is exactly the deficit of its sum from
twice its cardinality. -/
theorem sum_add_count_one_eq_two_mul_card
    (ks : Multiset ℕ)
    (hpos : ∀ k ∈ ks, 1 ≤ k)
    (hle : ∀ k ∈ ks, k ≤ 2) :
    ks.sum + ks.count 1 = 2 * ks.card := by
  induction ks using Multiset.induction with
  | empty => simp
  | @cons a s ih =>
      have ha1 : 1 ≤ a := hpos a (Multiset.mem_cons_self a s)
      have ha2 : a ≤ 2 := hle a (Multiset.mem_cons_self a s)
      have hs := ih
        (fun x hx => hpos x (Multiset.mem_cons_of_mem hx))
        (fun x hx => hle x (Multiset.mem_cons_of_mem hx))
      have ha : a = 1 ∨ a = 2 := by omega
      rcases ha with rfl | rfl <;>
        simp only [Multiset.sum_cons, Multiset.count_cons, Multiset.card_cons] <;>
        simp_all <;> omega

/-- **Unique extremal histogram.**  At the G209 floor there is exactly one multiplicity-one class;
all remaining saturated classes have multiplicity two. -/
theorem tail_floor_forces_exactly_one_one
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (ks : Multiset ℕ)
    (hpos : ∀ k ∈ ks, 1 ≤ k)
    (hsum : ks.sum = n - 1)
    (hcard : ks.card ≤ n / 2)
    (hsq : (ks.map (· ^ 2)).sum = 2 * n - 3) :
    ks.card = n / 2 ∧ ks.count 1 = 1 ∧ ∀ k ∈ ks, k = 1 ∨ k = 2 := by
  have hflat := (tail_sumSq_eq_iff_flat n hn heven ks hpos hsum hcard).mp hsq
  have hone := sum_add_count_one_eq_two_mul_card ks hpos hflat.2
  refine ⟨hflat.1, ?_, ?_⟩
  · rw [hsum, hflat.1] at hone
    obtain ⟨m, rfl⟩ := heven
    have hm : 1 ≤ m := by omega
    have hdiv : (m + m) / 2 = m := by omega
    rw [hdiv] at hone
    omega
  · intro k hk
    have hk1 := hpos k hk
    have hk2 := hflat.2 k hk
    omega

#print axioms all_le_two_of_engine_eq
#print axioms engine_eq_of_all_le_two
#print axioms tail_sumSq_eq_iff_flat
#print axioms sum_add_count_one_eq_two_mul_card
#print axioms tail_floor_forces_exactly_one_one

end ArkLib.ProximityGap.Frontier.G210
