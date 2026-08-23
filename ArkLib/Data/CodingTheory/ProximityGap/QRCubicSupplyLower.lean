/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QRCubicOrderedClosedForm

/-!
# The QR domain is δ*-BAD: a quadratic cubic-supply lower bound (#389)

`qr_zeroSum_ordered_eq` counts the ORDERED zero-sum triples of nonzero squares
(`= #QR*·M = Θ(n²)`).  This file converts that to a lower bound on the **unordered**
count — the actual cubic-word list size on the QR domain (the sum-zero `3`-subset count,
`= cubicSupply` via the in-tree `cubic_list_eq_zeroSum`):

> **`qr_cubic_supply_lower`** — `#QR*·M ≤ 27·#{T ⊆ QR* : |T|=3, ∑T = 0} + 3·#QR*`,
> hence the sum-zero `3`-subset count is `≥ (#QR*·M − 3·#QR*)/27 = Θ(n²)`.

So the QR (index-2) domain carries **quadratically many** explainable `3`-cores at the
near-capacity radius `1 − 3/n` — its additive richness makes it `δ*`-unfavourable (large
supply ⟹ many bad scalars ⟹ small `δ*`), the opposite of the `δ*`-good 2-power NTT
domain `μ_16 ⊂ F₂₅₇` where the same supply is exactly `0`
(`cubicSupply_mu16_F257_eq_zero`).

Conversion: the orbit map `(a,b,c) ↦ {a,b,c}` sends the distinct-entry triples into the
sum-zero `3`-subsets with each fiber `⊆ T ×ˢ T ×ˢ T` (`≤ 27`); the degenerate (`≥2`
equal) triples number `≤ 3·#QR*` (each repeat pattern fixes the triple from one free
square via the zero-sum constraint).  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The sum-zero `3`-subsets of `QR*` — the cubic-word list (`= cubicSupply`). -/
def qrSumZeroSubsets : Finset (Finset F) :=
  (qrStar (F := F)).powersetCard 3 |>.filter (fun T => ∑ x ∈ T, x = 0)

/-- The distinct-entry zero-sum triples. -/
def qrDistinctTriples : Finset (F × F × F) :=
  (qrZeroSumTriples (F := F)).filter
    (fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2)

/-- The orbit map: a triple to its underlying set. -/
def tripleSet (t : F × F × F) : Finset F := {t.1, t.2.1, t.2.2}

omit [Field F] [Fintype F] in
theorem tripleSet_card_le (t : F × F × F) : (tripleSet t).card ≤ 3 := by
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine le_trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) ?_
  simp [Finset.card_singleton]

/-- The orbit map sends distinct zero-sum triples into the sum-zero `3`-subsets. -/
theorem image_tripleSet_subset :
    (qrDistinctTriples (F := F)).image tripleSet ⊆ qrSumZeroSubsets := by
  intro T hT
  rw [Finset.mem_image] at hT
  obtain ⟨t, ht, rfl⟩ := hT
  rw [qrDistinctTriples, Finset.mem_filter, mem_qrZeroSumTriples] at ht
  obtain ⟨⟨ha, hb, hc, hsum⟩, hd1, hd2, hd3⟩ := ht
  rw [qrSumZeroSubsets, Finset.mem_filter, Finset.mem_powersetCard]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · rw [tripleSet, Finset.card_insert_of_notMem (by simp [hd1, hd2]),
      Finset.card_insert_of_notMem (by simp [hd3]), Finset.card_singleton]
  · rw [tripleSet, Finset.sum_insert (by simp [hd1, hd2]),
      Finset.sum_insert (by simp [hd3]), Finset.sum_singleton]
    linear_combination hsum

/-- Each fiber of the orbit map has `≤ 27` elements (it sits in `T ×ˢ T ×ˢ T`). -/
theorem fiber_card_le (T : Finset F) :
    ((qrDistinctTriples (F := F)).filter (fun t => tripleSet t = T)).card ≤ 27 := by
  classical
  rcases Nat.lt_or_ge T.card 4 with hlt | hgt
  · have hle : T.card ≤ 3 := by omega
    refine le_trans (Finset.card_le_card (t := T ×ˢ T ×ˢ T) ?_) ?_
    · intro t ht
      rw [Finset.mem_filter] at ht
      have hTeq : tripleSet t = T := ht.2
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · rw [← hTeq]; simp [tripleSet]
      · rw [← hTeq]; simp [tripleSet]
      · rw [← hTeq]; simp [tripleSet]
    · rw [Finset.card_product, Finset.card_product]
      calc T.card * (T.card * T.card) ≤ 3 * (3 * 3) :=
            Nat.mul_le_mul hle (Nat.mul_le_mul hle hle)
        _ = 27 := by norm_num
  · have hempty : (qrDistinctTriples (F := F)).filter (fun t => tripleSet t = T) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro t _ hTeq
      have : T.card ≤ 3 := hTeq ▸ tripleSet_card_le t
      omega
    rw [hempty]; simp

/-- **Distinct zero-sum triples are `≤ 27 ×` the sum-zero 3-subsets.** -/
theorem qrDistinctTriples_card_le :
    (qrDistinctTriples (F := F)).card ≤ 27 * (qrSumZeroSubsets (F := F)).card := by
  classical
  refine le_trans (Finset.card_le_mul_card_image _ 27 (fun T _ => fiber_card_le T)) ?_
  exact Nat.mul_le_mul_left _ (Finset.card_le_card image_tripleSet_subset)

/-- A repeat-pattern slice of the zero-sum triples — given a key coordinate that
determines the whole triple within the slice — has `≤ #QR*` elements. -/
theorem qr_pattern_le (P : F × F × F → Prop) [DecidablePred P] (key : F × F × F → F)
    (hmem : ∀ t ∈ (qrZeroSumTriples (F := F)).filter P, key t ∈ qrStar)
    (hinj : ∀ t ∈ (qrZeroSumTriples (F := F)).filter P,
        ∀ t' ∈ (qrZeroSumTriples (F := F)).filter P, key t = key t' → t = t') :
    ((qrZeroSumTriples (F := F)).filter P).card ≤ (qrStar (F := F)).card := by
  classical
  refine Finset.card_le_card_of_injOn key (fun t ht => hmem t ht) ?_
  intro t ht t' ht' heq
  rw [Finset.mem_coe] at ht ht'
  exact hinj t ht t' ht' heq

open Classical in
/-- **The degenerate (`≥2`-equal) zero-sum triples number `≤ 3·#QR*`.** Each of the three
repeat patterns fixes the triple from one square coordinate via the zero-sum constraint. -/
theorem qrDegenerate_card_le :
    ((qrZeroSumTriples (F := F)).filter
      (fun t => ¬ (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2))).card
      ≤ 3 * (qrStar (F := F)).card := by
  classical
  set S := qrZeroSumTriples (F := F)
  have hsub : S.filter (fun t => ¬ (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2))
      ⊆ (S.filter (fun t => t.1 = t.2.1)) ∪ (S.filter (fun t => t.1 = t.2.2))
        ∪ (S.filter (fun t => t.2.1 = t.2.2)) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htS, hnd⟩ := ht
    push Not at hnd
    by_cases h1 : t.1 = t.2.1
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨htS, h1⟩))
    · by_cases h2 : t.1 = t.2.2
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨htS, h2⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨htS, hnd h1 h2⟩)
  have hAB : (S.filter (fun t => t.1 = t.2.1)).card ≤ (qrStar (F := F)).card :=
    qr_pattern_le _ (fun t => t.1)
      (fun t ht => (mem_qrZeroSumTriples.mp (Finset.mem_filter.mp ht).1).1)
      (fun t ht t' ht' heq => by
        rw [Finset.mem_filter, mem_qrZeroSumTriples] at ht ht'
        obtain ⟨⟨_, _, _, hs⟩, he⟩ := ht
        obtain ⟨⟨_, _, _, hs'⟩, he'⟩ := ht'
        have hk : t.1 = t'.1 := heq
        refine Prod.ext hk (Prod.ext ?_ ?_)
        · rw [← he, ← he', hk]
        · rw [show t.2.2 = -t.1 - t.2.1 by linear_combination hs,
            show t'.2.2 = -t'.1 - t'.2.1 by linear_combination hs', ← he, ← he', hk])
  have hAC : (S.filter (fun t => t.1 = t.2.2)).card ≤ (qrStar (F := F)).card :=
    qr_pattern_le _ (fun t => t.1)
      (fun t ht => (mem_qrZeroSumTriples.mp (Finset.mem_filter.mp ht).1).1)
      (fun t ht t' ht' heq => by
        rw [Finset.mem_filter, mem_qrZeroSumTriples] at ht ht'
        obtain ⟨⟨_, _, _, hs⟩, he⟩ := ht
        obtain ⟨⟨_, _, _, hs'⟩, he'⟩ := ht'
        have hk : t.1 = t'.1 := heq
        refine Prod.ext hk (Prod.ext ?_ ?_)
        · rw [show t.2.1 = -t.1 - t.2.2 by linear_combination hs,
            show t'.2.1 = -t'.1 - t'.2.2 by linear_combination hs', ← he, ← he', hk]
        · rw [← he, ← he', hk])
  have hBC : (S.filter (fun t => t.2.1 = t.2.2)).card ≤ (qrStar (F := F)).card :=
    qr_pattern_le _ (fun t => t.2.1)
      (fun t ht => (mem_qrZeroSumTriples.mp (Finset.mem_filter.mp ht).1).2.1)
      (fun t ht t' ht' heq => by
        rw [Finset.mem_filter, mem_qrZeroSumTriples] at ht ht'
        obtain ⟨⟨_, _, _, hs⟩, he⟩ := ht
        obtain ⟨⟨_, _, _, hs'⟩, he'⟩ := ht'
        have hk : t.2.1 = t'.2.1 := heq
        refine Prod.ext ?_ (Prod.ext hk ?_)
        · rw [show t.1 = -t.2.1 - t.2.2 by linear_combination hs,
            show t'.1 = -t'.2.1 - t'.2.2 by linear_combination hs', ← he, ← he', hk]
        · rw [← he, ← he', hk])
  calc (S.filter (fun t => ¬ (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2))).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ (S.filter (fun t => t.1 = t.2.1)).card + (S.filter (fun t => t.1 = t.2.2)).card
          + (S.filter (fun t => t.2.1 = t.2.2)).card :=
        le_trans (Finset.card_union_le _ _)
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ (qrStar (F := F)).card + (qrStar (F := F)).card + (qrStar (F := F)).card :=
        Nat.add_le_add (Nat.add_le_add hAB hAC) hBC
    _ = 3 * (qrStar (F := F)).card := by ring

/-- **THE QR CUBIC-SUPPLY LOWER BOUND**: `#QR*·M ≤ 27·(sum-zero 3-subsets) + 3·#QR*`.
With `M = (q−5)/4`, `#QR* = (q−1)/2` this forces the QR-domain cubic supply
`≥ (#QR*·M − 3·#QR*)/27 = Θ(n²)` — the additively-rich QR domain is `δ*`-bad. -/
theorem qr_cubic_supply_lower (hneg1 : IsSquare (-1 : F)) :
    (qrStar (F := F)).card * (qrConsec (F := F)).card
      ≤ 27 * (qrSumZeroSubsets (F := F)).card + 3 * (qrStar (F := F)).card := by
  classical
  have hpart : (qrZeroSumTriples (F := F)).card
      = (qrDistinctTriples (F := F)).card
        + ((qrZeroSumTriples (F := F)).filter
            (fun t => ¬ (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2))).card := by
    rw [qrDistinctTriples, Finset.filter_card_add_filter_neg_card_eq_card]
  rw [← qr_zeroSum_ordered_eq (F := F) hneg1, hpart]
  exact Nat.add_le_add qrDistinctTriples_card_le qrDegenerate_card_le

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.qr_cubic_supply_lower
