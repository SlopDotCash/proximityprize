/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.PowerSeriesComposition

/-!
# BCIKS20 Appendix A.4 — term-level zero/positive reindex helpers

Small multiset facts for the P2 reindex: split a value multiset into its zero
multiplicity and strictly-positive part, then package the positive part as a `Nat.Partition`.
-/

namespace BCIKS20.HenselNumerator

open ArkLib.PowerSeriesComposition

/-- The number of zero entries in a value multiset. -/
def zeroCount (m : Multiset ℕ) : ℕ :=
  m.count 0

/-- The strictly-positive entries of a value multiset. -/
def positivePart (m : Multiset ℕ) : Multiset ℕ :=
  m.filter (fun n => n ≠ 0)

@[simp]
theorem zeroCount_eq_count_zero (m : Multiset ℕ) :
    zeroCount m = m.count 0 := rfl

@[simp]
theorem positivePart_eq_filter_ne_zero (m : Multiset ℕ) :
    positivePart m = m.filter (fun n => n ≠ 0) := rfl

/-- The positive part contains no zeros. -/
theorem zero_notMem_positivePart (m : Multiset ℕ) :
    (0 : ℕ) ∉ positivePart m := by
  simp [positivePart]

/-- Counting any positive value in the positive part agrees with counting it in the original
multiset. -/
theorem positivePart_count_of_ne_zero (m : Multiset ℕ) {n : ℕ} (hn : n ≠ 0) :
    (positivePart m).count n = m.count n := by
  simp [positivePart, hn]

/-- The original multiset is its zero block plus its positive part. -/
theorem replicate_zero_add_positivePart (m : Multiset ℕ) :
    Multiset.replicate (zeroCount m) 0 + positivePart m = m := by
  classical
  ext n
  by_cases hn : n = 0
  · subst hn
    simp [zeroCount, positivePart]
  · rw [Multiset.count_add, Multiset.count_replicate, if_neg (Ne.symm hn), zero_add]
    simp [positivePart, hn]

/-- Filtering out zeros preserves the multiset sum. -/
theorem positivePart_sum (m : Multiset ℕ) :
    (positivePart m).sum = m.sum := by
  classical
  have h := congrArg Multiset.sum (replicate_zero_add_positivePart m)
  simpa [zeroCount, Nat.add_comm] using h

/-- The positive-part cardinality plus the zero count is the original cardinality. -/
theorem positivePart_card_add_zeroCount (m : Multiset ℕ) :
    (positivePart m).card + zeroCount m = m.card := by
  classical
  have h := congrArg Multiset.card (replicate_zero_add_positivePart m)
  simpa [zeroCount, Nat.add_comm] using h

/-- The original cardinality splits as zero count plus positive-part cardinality. -/
theorem zeroCount_add_positivePart_card (m : Multiset ℕ) :
    zeroCount m + (positivePart m).card = m.card := by
  rw [Nat.add_comm, positivePart_card_add_zeroCount]

/-- The positive part of a value multiset, packaged as a `Nat.Partition` of the original sum. -/
def positivePartition (m : Multiset ℕ) : Nat.Partition m.sum where
  parts := positivePart m
  parts_pos := by
    intro n hn
    exact Nat.pos_iff_ne_zero.mpr (fun h => zero_notMem_positivePart m (h ▸ hn))
  parts_sum := positivePart_sum m

@[simp]
theorem positivePartition_parts (m : Multiset ℕ) :
    (positivePartition m).parts = positivePart m := rfl

@[simp]
theorem positivePartition_parts_sum (m : Multiset ℕ) :
    (positivePartition m).parts.sum = m.sum :=
  (positivePartition m).parts_sum

@[simp]
theorem positivePartition_parts_card (m : Multiset ℕ) :
    (positivePartition m).parts.card = (positivePart m).card := rfl

/-- Zero-peeling for `countPerms`: a zero block contributes only its placement binomial. -/
theorem countPerms_replicate_zero_add (j0 : ℕ) (lam : Multiset ℕ) (h0 : (0 : ℕ) ∉ lam) :
    (Multiset.replicate j0 0 + lam).countPerms
      = (j0 + lam.card).choose j0 * lam.countPerms := by
  classical
  set m : Multiset ℕ := Multiset.replicate j0 0 + lam with hm
  have hcount0 : m.count 0 = j0 := by
    rw [hm, Multiset.count_add, Multiset.count_replicate_self,
      Multiset.count_eq_zero_of_notMem h0, add_zero]
  have hcountv : ∀ v, v ≠ 0 → m.count v = lam.count v := by
    intro v hv
    rw [hm, Multiset.count_add, Multiset.count_replicate, if_neg (by simpa [eq_comm] using hv),
      zero_add]
  rw [countPerms_eq_multinomial, countPerms_eq_multinomial]
  by_cases hj : j0 = 0
  · subst hj
    simp only [Multiset.replicate_zero, zero_add] at hm
    rw [hm]
    simp
  · have h0nf : (0 : ℕ) ∉ lam.toFinset := by rwa [Multiset.mem_toFinset]
    have htf : m.toFinset = insert 0 lam.toFinset := by
      rw [hm]
      ext x
      simp only [Multiset.toFinset_add, Finset.mem_union, Multiset.mem_toFinset,
        Multiset.mem_replicate, Finset.mem_insert]
      constructor
      · rintro (⟨_, rfl⟩ | h)
        · exact Or.inl rfl
        · exact Or.inr h
      · rintro (rfl | h)
        · exact Or.inl ⟨hj, rfl⟩
        · exact Or.inr h
    rw [htf, Nat.multinomial_insert h0nf]
    have hsum : ∑ i ∈ lam.toFinset, m.count i = lam.card := by
      rw [Finset.sum_congr rfl (fun v hv => hcountv v (by rintro rfl; exact h0nf hv))]
      rw [← Multiset.toFinset_sum_count_eq lam]
    rw [hcount0, hsum]
    congr 1
    refine Nat.multinomial_congr ?_
    intro v hv
    exact hcountv v (by rintro rfl; exact h0nf hv)

/-- Zero-peeling applied to the canonical zero/positive split of a multiset. -/
theorem countPerms_eq_choose_zeroCount_mul_positivePart (m : Multiset ℕ) :
    m.countPerms =
      (zeroCount m + (positivePart m).card).choose (zeroCount m) * (positivePart m).countPerms := by
  calc
    m.countPerms = (Multiset.replicate (zeroCount m) 0 + positivePart m).countPerms := by
      rw [replicate_zero_add_positivePart m]
    _ = (zeroCount m + (positivePart m).card).choose (zeroCount m)
          * (positivePart m).countPerms :=
      countPerms_replicate_zero_add (zeroCount m) (positivePart m) (zero_notMem_positivePart m)

/-- Zero-peeling, re-keyed to the positive-part/Y-Hasse binomial. -/
theorem countPerms_replicate_zero_add_choose_sl (j0 : ℕ) (lam : Multiset ℕ)
    (h0 : (0 : ℕ) ∉ lam) :
    (Multiset.replicate j0 0 + lam).countPerms
      = (j0 + lam.card).choose lam.card * lam.countPerms := by
  rw [countPerms_replicate_zero_add j0 lam h0]
  congr 1
  simpa [Nat.add_sub_cancel_right] using Nat.choose_symm (Nat.le_add_left lam.card j0)

end BCIKS20.HenselNumerator
