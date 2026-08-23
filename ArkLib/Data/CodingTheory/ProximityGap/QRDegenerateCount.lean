/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QRCubicExactValue

/-!
# The exact degenerate count and the exact QR cubic-supply identity (#389)

Upgrades the `qr_cubic_supply_bracket` (which used `#degenerate <= 3.#QR*`) to an EXACT
identity by counting the degenerate (>=2-equal) zero-sum triples exactly.

* `qrNegTwo` -- the "minus-two-closed" squares `{a in QR* : -2a in QR*}`.
* `qr_pattern_{ab,ac,bc}_card` -- each single-repeat pattern has card `#qrNegTwo`
  (coordinate bijection `a <-> (a,a,-2a)` etc.).
* `qr_patterns_disjoint` / `qrDegenerate_card_eq` -- the three patterns are pairwise
  disjoint (two coincidences force `3.t.i = 0`, impossible for a nonzero square when
  char != 3), so `#degenerate = 3.#qrNegTwo`.
* `qr_cubic_supply_exact` -- hence `6.#subsets + 3.#qrNegTwo = #QR*.M` EXACTLY (`-1` a
  square, char != 3).

This is the degenerate-sharp form of the QR cubic-word supply.  Specialising `#qrNegTwo`
(`= #QR*` if `-2` is a square, i.e. `q = 1 (mod 8)`, else `0`, via the mod-8 law) yields the
closed form `(q-1)(q-17)/48` resp. `(q-1)(q-5)/48`.  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The "minus-two-closed" squares: `{a ∈ QR* : −2a ∈ QR*}`. -/
def qrNegTwo : Finset F := (qrStar (F := F)).filter (fun a => -2 * a ∈ qrStar)

theorem mem_qrNegTwo {a : F} : a ∈ qrNegTwo ↔ a ∈ qrStar ∧ -2 * a ∈ qrStar := by
  simp only [qrNegTwo, Finset.mem_filter]

/-- A repeat-pattern slice's card equals `#qrNegTwo`, via a coordinate bijection. -/
theorem qr_pattern_card_eq (P : F × F × F → Prop) [DecidablePred P]
    (build : F → F × F × F) (key : F × F × F → F)
    (hbuild : ∀ a, a ∈ qrNegTwo (F := F) → build a ∈ (qrZeroSumTriples (F := F)).filter P)
    (hkey_build : ∀ a, key (build a) = a)
    (hkey_mem : ∀ t ∈ (qrZeroSumTriples (F := F)).filter P, key t ∈ qrNegTwo (F := F))
    (hbuild_key : ∀ t ∈ (qrZeroSumTriples (F := F)).filter P, build (key t) = t) :
    ((qrZeroSumTriples (F := F)).filter P).card = (qrNegTwo (F := F)).card := by
  classical
  refine Finset.card_nbij' key build ?_ ?_ ?_ ?_
  · intro t ht; rw [Finset.mem_coe] at ht; exact hkey_mem t ht
  · intro a ha; rw [Finset.mem_coe] at ha; exact hbuild a ha
  · intro t ht; rw [Finset.mem_coe] at ht; exact hbuild_key t ht
  · intro a _; exact hkey_build a

theorem qr_pattern_ab_card :
    ((qrZeroSumTriples (F := F)).filter (fun t => t.1 = t.2.1)).card
      = (qrNegTwo (F := F)).card := by
  refine qr_pattern_card_eq _ (fun a => (a, a, -2 * a)) (fun t => t.1) ?_ (fun _ => rfl) ?_ ?_
  · intro a ha
    obtain ⟨ha1, ha2⟩ := mem_qrNegTwo.mp ha
    rw [Finset.mem_filter, mem_qrZeroSumTriples]
    exact ⟨⟨ha1, ha1, ha2, by ring⟩, rfl⟩
  · intro t ht
    rw [Finset.mem_filter, mem_qrZeroSumTriples] at ht
    obtain ⟨⟨h1, _, h3', hsum⟩, heq⟩ := ht
    rw [mem_qrNegTwo]
    refine ⟨h1, ?_⟩
    have hc : -2 * t.1 = t.2.2 := by linear_combination -hsum - heq
    rw [hc]; exact h3'
  · intro t ht
    rw [Finset.mem_filter, mem_qrZeroSumTriples] at ht
    obtain ⟨⟨_, _, _, hsum⟩, heq⟩ := ht
    have hc : -2 * t.1 = t.2.2 := by linear_combination -hsum - heq
    exact Prod.ext rfl (Prod.ext heq hc)

theorem qr_pattern_ac_card :
    ((qrZeroSumTriples (F := F)).filter (fun t => t.1 = t.2.2)).card
      = (qrNegTwo (F := F)).card := by
  refine qr_pattern_card_eq _ (fun a => (a, -2 * a, a)) (fun t => t.1) ?_ (fun _ => rfl) ?_ ?_
  · intro a ha
    obtain ⟨ha1, ha2⟩ := mem_qrNegTwo.mp ha
    rw [Finset.mem_filter, mem_qrZeroSumTriples]
    exact ⟨⟨ha1, ha2, ha1, by ring⟩, rfl⟩
  · intro t ht
    rw [Finset.mem_filter, mem_qrZeroSumTriples] at ht
    obtain ⟨⟨h1, h2', _, hsum⟩, heq⟩ := ht
    rw [mem_qrNegTwo]
    refine ⟨h1, ?_⟩
    have hc : -2 * t.1 = t.2.1 := by linear_combination -hsum - heq
    rw [hc]; exact h2'
  · intro t ht
    rw [Finset.mem_filter, mem_qrZeroSumTriples] at ht
    obtain ⟨⟨_, _, _, hsum⟩, heq⟩ := ht
    have hc : -2 * t.1 = t.2.1 := by linear_combination -hsum - heq
    exact Prod.ext rfl (Prod.ext hc heq)

theorem qr_pattern_bc_card :
    ((qrZeroSumTriples (F := F)).filter (fun t => t.2.1 = t.2.2)).card
      = (qrNegTwo (F := F)).card := by
  refine qr_pattern_card_eq _ (fun a => (-2 * a, a, a)) (fun t => t.2.1) ?_ (fun _ => rfl) ?_ ?_
  · intro a ha
    obtain ⟨ha1, ha2⟩ := mem_qrNegTwo.mp ha
    rw [Finset.mem_filter, mem_qrZeroSumTriples]
    exact ⟨⟨ha2, ha1, ha1, by ring⟩, rfl⟩
  · intro t ht
    rw [Finset.mem_filter, mem_qrZeroSumTriples] at ht
    obtain ⟨⟨h1, h2', _, hsum⟩, heq⟩ := ht
    rw [mem_qrNegTwo]
    refine ⟨h2', ?_⟩
    have hc : -2 * t.2.1 = t.1 := by linear_combination -hsum - heq
    rw [hc]; exact h1
  · intro t ht
    rw [Finset.mem_filter, mem_qrZeroSumTriples] at ht
    obtain ⟨⟨_, _, _, hsum⟩, heq⟩ := ht
    have hc : -2 * t.2.1 = t.1 := by linear_combination -hsum - heq
    exact Prod.ext hc (Prod.ext rfl heq)


theorem qr_patterns_disjoint (h3 : (3 : F) ≠ 0) :
    Disjoint ((qrZeroSumTriples (F := F)).filter (fun t => t.1 = t.2.1))
      (((qrZeroSumTriples (F := F)).filter (fun t => t.1 = t.2.2))
        ∪ ((qrZeroSumTriples (F := F)).filter (fun t => t.2.1 = t.2.2))) := by
  classical
  rw [Finset.disjoint_left]
  intro t ht htu
  rw [Finset.mem_filter, mem_qrZeroSumTriples] at ht
  obtain ⟨⟨h1, _, _, hsum⟩, hab⟩ := ht
  have ht1 : t.1 ≠ 0 := (mem_qrStar.mp h1).1
  have hzero : (3 : F) * t.1 = 0 := by
    rcases Finset.mem_union.mp htu with hac | hbc
    · rw [Finset.mem_filter] at hac; linear_combination hsum + hab + hac.2
    · rw [Finset.mem_filter] at hbc; linear_combination hsum + 2 * hab + hbc.2
  rcases mul_eq_zero.mp hzero with h | h
  · exact h3 h
  · exact ht1 h

/-- **The exact degenerate count**: the `≥2`-equal zero-sum triples number exactly
`3·#qrNegTwo` (char ≠ 3) — sharpening `qrDegenerate_card_le`. -/
theorem qrDegenerate_card_eq (h3 : (3 : F) ≠ 0) :
    ((qrZeroSumTriples (F := F)).filter
      (fun t => ¬ (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2))).card
      = 3 * (qrNegTwo (F := F)).card := by
  classical
  have hpred : (qrZeroSumTriples (F := F)).filter
      (fun t => ¬ (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2))
      = ((qrZeroSumTriples (F := F)).filter (fun t => t.1 = t.2.1))
        ∪ (((qrZeroSumTriples (F := F)).filter (fun t => t.1 = t.2.2))
          ∪ ((qrZeroSumTriples (F := F)).filter (fun t => t.2.1 = t.2.2))) := by
    rw [← Finset.filter_or, ← Finset.filter_or]
    apply Finset.filter_congr
    intro t _
    constructor
    · intro h; by_contra hcon; push Not at hcon; exact h ⟨hcon.1, hcon.2.1, hcon.2.2⟩
    · rintro (h | h | h) ⟨hab, hac, hbc⟩
      · exact hab h
      · exact hac h
      · exact hbc h
  rw [hpred, Finset.card_union_of_disjoint (qr_patterns_disjoint h3),
    Finset.card_union_of_disjoint, qr_pattern_ab_card, qr_pattern_ac_card, qr_pattern_bc_card]
  · ring
  · -- P_ac and P_bc disjoint
    rw [Finset.disjoint_left]
    intro t ht htbc
    rw [Finset.mem_filter, mem_qrZeroSumTriples] at ht
    obtain ⟨⟨h1, _, _, hsum⟩, hac⟩ := ht
    rw [Finset.mem_filter] at htbc
    have ht1 : t.1 ≠ 0 := (mem_qrStar.mp h1).1
    have hzero : (3 : F) * t.1 = 0 := by linear_combination hsum + 2 * hac - htbc.2
    rcases mul_eq_zero.mp hzero with h | h
    · exact h3 h
    · exact ht1 h

/-- **The exact QR cubic-supply identity**: `6·#subsets + 3·#qrNegTwo = #QR*·M`
(`−1` a square, char ≠ 3) — the degenerate-sharp form of `qr_cubic_supply_ordered_eq`. -/
theorem qr_cubic_supply_exact (hneg1 : IsSquare (-1 : F)) (h3 : (3 : F) ≠ 0) :
    6 * (qrSumZeroSubsets (F := F)).card + 3 * (qrNegTwo (F := F)).card
      = (qrStar (F := F)).card * (qrConsec (F := F)).card := by
  rw [← qrDegenerate_card_eq h3]
  exact qr_cubic_supply_ordered_eq hneg1

end ProximityGap.PairRank
