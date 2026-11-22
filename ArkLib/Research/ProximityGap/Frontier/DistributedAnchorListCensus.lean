/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-! # Signed exponent sums and disjoint antipodal list counts

The signed locator at a dyadic anchor is determined by the leaf signature and
the exponent sum modulo twice the quotient order. Opposite rotation needs one
extra bit, the parity of the number of exponents in the upper half.
-/

namespace ProximityGap.DistributedAnchorListCensus

open Finset

/-- An upper-half exponent wraps exactly once when shifted half a turn. -/
theorem sum_opposite (h : ℕ) (S : Finset ℕ) (hs : ∀ j ∈ S, j < 2 * h) :
    (∑ j ∈ S, (j + h) % (2 * h)) + 2 * h * (S.filter (h ≤ ·)).card =
      (∑ j ∈ S, j) + S.card * h := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    have hjlt := hs j (mem_insert_self j S)
    have prev := ih (fun i hi => hs i (mem_insert_of_mem hi))
    have hjstep : (j + h) % (2 * h) + (if h ≤ j then 2 * h else 0) = j + h := by
      split_ifs with hle
      · have hlt : j + h - 2 * h < 2 * h := by omega
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt]
        omega
      · rw [Nat.mod_eq_of_lt (by omega)]
        omega
    by_cases ha : h ≤ j
    · simp [filter_insert, ha, hj, mul_add, add_mul] at hjstep ⊢
      omega
    · simp [filter_insert, ha, hj, add_mul] at hjstep ⊢
      omega

/-- The original signed exponent and the wrap parity determine the opposite signed exponent. -/
theorem signed_opposite (h : ℕ) (S : Finset ℕ) (hs : ∀ j ∈ S, j < 2 * h) :
    (∑ j ∈ S, (j + h) % (2 * h)) % (4 * h) =
      ((∑ j ∈ S, j) + S.card * h + 2 * h * ((S.filter (h ≤ ·)).card % 2)) % (4 * h) := by
  let c := (S.filter (h ≤ ·)).card
  have hc : c = c % 2 + 2 * (c / 2) := (Nat.mod_add_div c 2).symm
  have hw : 2 * h * c + 2 * h * (c % 2) = 4 * h * (c / 2 + c % 2) := by
    calc
      _ = 2 * h * (c % 2 + 2 * (c / 2)) + 2 * h * (c % 2) := by
        conv_lhs => lhs; rhs; rw [hc]
      _ = _ := by ring
  change _ = ((∑ j ∈ S, j) + S.card * h + 2 * h * (c % 2)) % _
  rw [← sum_opposite h S hs]
  change _ = ((∑ j ∈ S, (j + h) % (2 * h)) + 2 * h * c + 2 * h * (c % 2)) % _
  rw [Nat.add_assoc, hw, Nat.add_mul_mod_self_left]

/-- Assigning each subset to one pair lets each antipodal overlap be subtracted exactly once. -/
theorem card_paired_union {ι α : Type*} [Fintype ι] [DecidableEq α]
    (A B : ι → Finset α) (group : α → ι)
    (hg : ∀ i, ∀ x ∈ A i ∪ B i, group x = i) :
    (univ.biUnion fun i => A i ∪ B i).card + (∑ i, (A i ∩ B i).card) =
      ∑ i, ((A i).card + (B i).card) := by
  classical
  rw [card_biUnion, ← sum_add_distrib]
  · exact sum_congr rfl fun i _ => card_union_add_card_inter (A i) (B i)
  · intro i _ j _ h
    exact disjoint_left.mpr fun x hx hy => h ((hg i x hx).symm.trans (hg j x hy))

/-- With `r` reserved fibers, a largest palette of size `k`, and `t` labels altogether,
the two site constraints determine the largest uniform number of sites per selected label. -/
theorem gain_iff (r h k t g : ℕ) (hr : 0 < r) (hh : 0 < h) (hk : 0 < k) (ht : 0 < t) :
    (k * g ≤ h ∧ t * g + (h - 1) ≤ r * h) ↔
      g ≤ min (h / k) (((r - 1) * h + 1) / t) := by
  rw [le_min_iff, Nat.le_div_iff_mul_le hk, Nat.le_div_iff_mul_le ht,
    Nat.mul_comm g k, Nat.mul_comm g t]
  cases r with
  | zero => omega
  | succ r =>
    simp only [Nat.succ_sub_one, Nat.succ_mul]
    omega

/-- Additional agreements, certified union size and error count of a named degree-17 witness. -/
def productionReceipt (order reserve maxSlots totalSlots singles overlaps : ℕ) : ℕ × ℕ × ℕ :=
  let h := 2 ^ 30 / order
  let g := min (h / maxSlots) (((reserve - 1) * h + 1) / totalSlots)
  (g, singles - overlaps, 2 ^ 30 - (18 * h - 1 + g))

/-- Substitute the four marginal and intersection counts into the allocation formula. -/
theorem named_receipts :
    productionReceipt 64 4 599 (4 * 599) (2 * (276234019 + 267652861))
        (6930791 + 6659874) = (21006, 1074183095, 771730931) ∧
    productionReceipt 64 4 1351 (4 * 1351) (2 * (560613009 + 531156953))
        (16350133 + 18699241) = (9313, 2148490550, 771742624) ∧
    productionReceipt 128 8 5 40
        (2 * (140076180 + 112223900 + 155732600) + 130789633 + 130847174)
        (287694 + 266240) = (1468006, 1077148233, 921278875) ∧
    productionReceipt 128 8 11 83
        (2 * (308147376 + 315525804) + 246901138 + 246858106 + 171801200 + 236108990)
        (317856 + 254592 + 328626 + 532480) = (707472, 2147582240, 922039409) := by
  decide

end ProximityGap.DistributedAnchorListCensus
