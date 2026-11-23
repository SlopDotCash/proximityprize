/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import ArkLib.Research.ProximityGap.Frontier._CompletionCountAssembly

/-!
# From per-pair completion caps to a global long-triple count

`_CompletionCountAssembly` bounds the surviving completions of one high-union
pair. The reciprocal-locator argument then sums that local bound over all high
pairs and divides by three, because each triple contains three pairs. This
module proves that summation.

The statement is deliberately free of any symmetry assumption. For an ordered
pair `(i, j)` the completion set is `rest i j`, the heads other than `i` and
`j`. If at most `K` of those completions are short, at least
`|rest i j| - K = b - 2 - K` are long, and summing over all ordered high pairs
gives

    (#ordered high pairs) * (b - 2 - K) <= (ordered long-triple mass).

The right side counts ordered triples, so no `long`-invariance is needed: the
pointwise bound is applied pair by pair and the long-triple sum only has to
dominate each of them.

`first_sponsor_long_triple_fraction` then evaluates the draft's numbers:
`b = 1073741825`, `K = 4809` (4806 proven completions plus two deleted heads
and at most one collinear completion) and the high-pair fraction `30343/100000`
give more than thirty percent of all unordered triples as long.
-/

set_option autoImplicit false

namespace ProximityGap.PairCompletionAggregate

open scoped BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The heads other than `i` and `j`. -/
def rest (i j : I) : Finset I := ((Finset.univ : Finset I).erase i).erase j

/-- Membership in `rest` is exactly being distinct from both heads. -/
theorem mem_rest {i j l : I} : l ∈ rest i j ↔ l ≠ i ∧ l ≠ j := by
  simp [rest, Finset.mem_erase, and_comm]

/-- Two distinct heads leave `b - 2` completions. -/
theorem card_rest {i j : I} (hij : i ≠ j) : (rest i j).card = Fintype.card I - 2 := by
  have hj : j ∈ (Finset.univ : Finset I).erase i := by
    simp [Ne.symm hij]
  rw [rest, Finset.card_erase_of_mem hj,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  omega

/-- Two distinct heads force at least two heads in total. -/
theorem two_le_card {i j : I} (hij : i ≠ j) : 2 ≤ Fintype.card I := by
  have hsub : ({i, j} : Finset I) ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.card_le_card hsub
  rwa [Finset.card_pair hij, Finset.card_univ] at h

/-- An indicator sum over a finset is the cardinality of its filter. -/
theorem sum_ite_one_eq_card_finset (s : Finset I) (p : I → Prop) [DecidablePred p] :
    (∑ l ∈ s, (if p l then (1 : ℤ) else 0)) = ((s.filter p).card : ℤ) := by
  rw [← Finset.sum_filter]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- Summing the per-pair completion count over all ordered high pairs. -/
theorem aggregate_pair_completions (hi : I → I → Prop) [DecidableRel hi]
    (long : I → I → I → Prop) [∀ i j l, Decidable (long i j l)] (K : ℕ)
    (hcap : ∀ i j, i ≠ j → hi i j → ((rest i j).filter (fun l => ¬ long i j l)).card ≤ K) :
    (∑ i, ∑ j ∈ (Finset.univ : Finset I).erase i, (if hi i j then (1 : ℤ) else 0)) *
        ((Fintype.card I : ℤ) - 2 - (K : ℤ)) ≤
      ∑ i, ∑ j ∈ (Finset.univ : Finset I).erase i,
        ∑ l ∈ rest i j, (if long i j l then (1 : ℤ) else 0) := by
  classical
  have hpoint : ∀ i j, j ∈ (Finset.univ : Finset I).erase i →
      (if hi i j then (1 : ℤ) else 0) * ((Fintype.card I : ℤ) - 2 - (K : ℤ)) ≤
        ∑ l ∈ rest i j, (if long i j l then (1 : ℤ) else 0) := by
    intro i j hj
    have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    by_cases hhi : hi i j
    · rw [if_pos hhi, one_mul, sum_ite_one_eq_card_finset]
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := rest i j) (p := fun l => long i j l)
      have hcap' := hcap i j hij hhi
      have hcard := card_rest hij
      have h3 : ((rest i j).card : ℤ) = (Fintype.card I : ℤ) - 2 := by
        rw [hcard, Nat.cast_sub (two_le_card hij)]
        norm_num
      have h1 : (((rest i j).filter (fun l => long i j l)).card : ℤ) +
          (((rest i j).filter (fun l => ¬ long i j l)).card : ℤ) = ((rest i j).card : ℤ) := by
        exact_mod_cast hsplit
      have h2 : (((rest i j).filter (fun l => ¬ long i j l)).card : ℤ) ≤ (K : ℤ) := by
        exact_mod_cast hcap'
      linarith
    · rw [if_neg hhi, zero_mul]
      exact Finset.sum_nonneg (fun l _ => by split <;> norm_num)
  calc (∑ i, ∑ j ∈ (Finset.univ : Finset I).erase i, (if hi i j then (1 : ℤ) else 0)) *
        ((Fintype.card I : ℤ) - 2 - (K : ℤ))
      = ∑ i, ∑ j ∈ (Finset.univ : Finset I).erase i,
          (if hi i j then (1 : ℤ) else 0) * ((Fintype.card I : ℤ) - 2 - (K : ℤ)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
    _ ≤ ∑ i, ∑ j ∈ (Finset.univ : Finset I).erase i,
          ∑ l ∈ rest i j, (if long i j l then (1 : ℤ) else 0) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j hj
        exact hpoint i j hj

/-- The draft's numbers: with `b = 1073741825` and `K = 4809`, the aggregation
clears thirty percent of all unordered triples. -/
theorem first_sponsor_long_triple_fraction :
    let b : ℤ := 1073741825
    let pairs := b * (b - 1) / 2
    let triples := b * (b - 1) * (b - 2) / 6
    let highPairs := 30343 * pairs / 100000
    3 * (3 * triples / 10) ≤ highPairs * (b - 2 - 4809) := by
  norm_num

/-- The same comparison read as a lower bound on long triples. -/
theorem first_sponsor_long_triples_lower :
    let b : ℤ := 1073741825
    let pairs := b * (b - 1) / 2
    let triples := b * (b - 1) * (b - 2) / 6
    let highPairs := 30343 * pairs / 100000
    3 * triples / 10 ≤ highPairs * (b - 2 - 4809) / 3 := by
  norm_num

end ProximityGap.PairCompletionAggregate

#print axioms ProximityGap.PairCompletionAggregate.mem_rest
#print axioms ProximityGap.PairCompletionAggregate.card_rest
#print axioms ProximityGap.PairCompletionAggregate.two_le_card
#print axioms ProximityGap.PairCompletionAggregate.sum_ite_one_eq_card_finset
#print axioms ProximityGap.PairCompletionAggregate.aggregate_pair_completions
#print axioms ProximityGap.PairCompletionAggregate.first_sponsor_long_triple_fraction
#print axioms ProximityGap.PairCompletionAggregate.first_sponsor_long_triples_lower
