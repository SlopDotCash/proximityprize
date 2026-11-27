/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._Close07a_DoublingFoldMap
import ArkLib.Research.ProximityGap.Frontier._Close07b_DoublingInduction
import ArkLib.Research.ProximityGap.Frontier._Close07c_OddGradeVanishesFull

/-!
# Close C07d — the guarded E6 doubling recursion (#444)

This file settles the E6 doubling family of `_BridgeB07`, `_Close07a_DoublingFoldMap`,
`_Close07b_DoublingInduction` and `_Close07c_OddGradeVanishesFull`. It proves the guarded even
half `BridgeB07.DoublingBijectionGuarded`, which was the open statement of the family, and it
refutes the unguarded residuals that were meant to imply it.

## Main results

* `badVals_double_eq_image`: for even `n > 0`, even `k` and `m' ≥ 1`, the level-`2n`
  grade-`2m'` bad-value set is the `Close07a.foldVal`-image of the level-`n` bad-value set at
  capacity `k / 2` and grade `m'`. The grade-`1` constraint forces every bad carrier to be
  antipodally closed (`Close07b.grade_one_zero_iff_antipodalClosed`), hence of the form
  `Close07a.foldSubset n A'`, and `Close07a.fhat_foldSubset` transports the graded vectors. This
  is the carrier-symmetry forcing that `Close07a.FoldImageHyp` left open, together with the
  parity guard on `k` that the residual lacked.
* `cf_double`: the count identity `cf (2n) k (2m') = cf n (k / 2) m'` under the same guards, for
  every even `n > 0` and not only on the `2`-adic tower.
* `doublingBijectionGuarded_holds` proves `BridgeB07.DoublingBijectionGuarded`, and
  `oddGradeVanishesGuarded_holds` proves `BridgeB07.OddGradeVanishesGuarded` by transport from
  `Close07c.cf_odd_eq_zero`.

## Refutations of the unguarded forms

At odd capacity `k` and grade `2m' ≥ 2` the level-`2n` bad-value set is empty
(`badVals_double_odd_eq_empty`), because antipodally closed carriers have even size while
admissible carriers have the odd size `k + 2m'`. Since `cf 2 0 1 ≠ 0`, the instance `n = 2`,
`k = 1`, `m' = 1` refutes `Close07a.FoldImageHyp` (`not_foldImageHyp`),
`Close07b.FoldingBijection` (`not_foldingBijection`) and `BridgeB07.DoublingBijection`
(`not_doublingBijection`). This instance has an even positive level and a positive grade, so
the only defect it exploits is the missing parity guard on `k`. The hypotheses of
`Close07a.doublingBijection_of_foldImage` and `Close07b.E6_even_fold` are therefore
unsatisfiable, and `cf_double` replaces both. Finally `BridgeB07.OddGradeVanishes` fails at
`n = 1`, `k = 0`, `m = 1`, where the lower-grade condition is vacuous (`not_oddGradeVanishes`).

## Scope

`cf` is the graded count of the empirical formula E6. The knowledge base
(`docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`, §F) records that it is not
the cascade count that governs `m*`, so this closure is structural and does not touch the δ*
prize directly.

Issue #444. Target E6.
-/

open Finset

namespace ArkLib.ProximityGap.Close07d

/-! ### Transport between the verbatim copies of the E6 object -/

/-- `_Close07b` re-declares `fhat` verbatim, so the two graded vectors agree definitionally. -/
theorem fhat_eq_close07b (A : Finset ℕ) (m n : ℕ) :
    BridgeB07.fhat A m n = Close07b.fhat A m n := rfl

/-- `_Close07c` re-declares `cf` verbatim, so the two counts agree definitionally. -/
theorem cf_eq_close07c (n k m : ℕ) : BridgeB07.cf n k m = Close07c.cf n k m := rfl

/-! ### The fold maps on zero values and on carriers -/

/-- `Close07a.foldVal` sends the zero level-`n` vector to the zero level-`2n` vector. -/
theorem foldVal_zero (n : ℕ) (hn : Even n) :
    Close07a.foldVal n hn (fun _ => (0 : ℤ)) = fun _ => 0 := by
  funext i
  unfold Close07a.foldVal
  split <;> simp

/-- For `n > 0`, a folded vector vanishes exactly when the level-`n` vector does. -/
theorem foldVal_eq_zero_iff (n : ℕ) (hn : Even n) (hpos : 0 < n) (w : Fin (n / 2) → ℤ) :
    Close07a.foldVal n hn w = (fun _ => 0) ↔ w = fun _ => 0 := by
  constructor
  · intro h
    apply Close07a.foldVal_injective n hn hpos
    rw [h, foldVal_zero]
  · rintro rfl
    exact foldVal_zero n hn

/-- The fold `A' ∪ (A' + n)` of a subset of `{0, …, n - 1}` lies in `{0, …, 2n - 1}`. -/
theorem foldSubset_subset_range (n : ℕ) {A' : Finset ℕ} (hA' : A' ⊆ range n) :
    Close07a.foldSubset n A' ⊆ range (2 * n) := by
  intro x hx
  unfold Close07a.foldSubset at hx
  rw [mem_union, mem_image] at hx
  rw [mem_range]
  rcases hx with hx | ⟨b, hb, rfl⟩
  · have := mem_range.mp (hA' hx); omega
  · have := mem_range.mp (hA' hb); omega

/-- Folding a subset of `{0, …, n - 1}` doubles its cardinality. -/
theorem card_foldSubset (n : ℕ) {A' : Finset ℕ} (hA' : A' ⊆ range n) :
    (Close07a.foldSubset n A').card = 2 * A'.card := by
  unfold Close07a.foldSubset
  rw [card_union_of_disjoint
      (Close07a.foldSubset_disjoint n A' (fun a ha => mem_range.mp (hA' ha))),
    card_image_of_injective _ (fun x y h => Nat.add_right_cancel h)]
  ring

/-- The fold of a subset of `{0, …, n - 1}` is antipodally closed at level `2n`. -/
theorem antipodalClosed_foldSubset (n : ℕ) {A' : Finset ℕ} (hA' : A' ⊆ range n) :
    Close07b.AntipodalClosed (Close07a.foldSubset n A') n := by
  intro i hi
  unfold Close07a.foldSubset
  simp only [mem_union, mem_image]
  constructor
  · rintro (h | ⟨b, hb, hbi⟩)
    · exact Or.inr ⟨i, h, rfl⟩
    · have := mem_range.mp (hA' hb); omega
  · rintro (h | ⟨b, hb, hbi⟩)
    · have := mem_range.mp (hA' h); omega
    · have : b = i := by omega
      subst this; exact Or.inl hb

/-- An antipodally closed subset of `{0, …, 2n - 1}` is the fold of its lower half. -/
theorem eq_foldSubset_of_antipodalClosed (n : ℕ) {A : Finset ℕ} (hA : A ⊆ range (2 * n))
    (hcl : Close07b.AntipodalClosed A n) :
    A = Close07a.foldSubset n (A.filter (· < n)) := by
  ext x
  unfold Close07a.foldSubset
  simp only [mem_union, mem_image, mem_filter]
  constructor
  · intro hx
    by_cases hlt : x < n
    · exact Or.inl ⟨hx, hlt⟩
    · have hx2 := mem_range.mp (hA hx)
      refine Or.inr ⟨x - n, ⟨?_, by omega⟩, by omega⟩
      have := (hcl (x - n) (by omega)).mpr
      rw [show x - n + n = x by omega] at this
      exact this hx
  · rintro (⟨hx, _⟩ | ⟨b, ⟨hb, hbn⟩, rfl⟩)
    · exact hx
    · exact (hcl b hbn).mp hb

/-! ### The guarded doubling recursion -/

/-- **The guarded fold-image identity.** For even `n > 0`, even `k` and `m' ≥ 1`, the level-`2n`
grade-`2m'` bad-value set is exactly the `Close07a.foldVal`-image of the level-`n` bad-value set
at capacity `k / 2` and grade `m'`. -/
theorem badVals_double_eq_image (n k m' : ℕ) (hn : Even n) (hpos : 0 < n) (hk : Even k)
    (hm : 1 ≤ m') :
    BridgeB07.badVals (2 * n) k (2 * m') =
      (BridgeB07.badVals n (k / 2) m').image (Close07a.foldVal n hn) := by
  obtain ⟨k2, rfl⟩ := hk
  have hk2 : (k2 + k2) / 2 = k2 := by omega
  rw [hk2]
  ext v
  rw [BridgeB07.mem_badVals_iff, mem_image]
  constructor
  · rintro ⟨hv0, A, hAadm, hlow, hAv⟩
    rw [BridgeB07.admissible, mem_powersetCard] at hAadm
    obtain ⟨hAsub, hAcard⟩ := hAadm
    have h1 : BridgeB07.fhat A 1 (2 * n) = 0 := hlow 1 le_rfl (by omega)
    have hcl : Close07b.AntipodalClosed A n :=
      (Close07b.grade_one_zero_iff_antipodalClosed hpos hAsub).mp (by
        rw [← fhat_eq_close07b]; exact h1)
    set A' := A.filter (· < n)
    have hA'sub : A' ⊆ range n := fun x hx => mem_range.mpr (mem_filter.mp hx).2
    have hAeq := eq_foldSubset_of_antipodalClosed n hAsub hcl
    have hcardA' : A'.card = k2 + m' := by
      have := card_foldSubset n hA'sub
      rw [← hAeq] at this; omega
    refine ⟨BridgeB07.fhat A' m' n, ?_, ?_⟩
    · rw [BridgeB07.mem_badVals_iff]
      refine ⟨?_, A', ?_, ?_, rfl⟩
      · intro h0
        apply hv0
        rw [← hAv, hAeq, Close07a.fhat_foldSubset n hn hpos A'
          (fun a ha => mem_range.mp (hA'sub ha)), h0, foldVal_zero]
      · rw [BridgeB07.admissible, mem_powersetCard]; exact ⟨hA'sub, hcardA'⟩
      · intro j hj1 hjm
        have hz : BridgeB07.fhat A (2 * j) (2 * n) = 0 := hlow (2 * j) (by omega) (by omega)
        rw [hAeq, Close07a.fhat_foldSubset n hn hpos A'
          (fun a ha => mem_range.mp (hA'sub ha))] at hz
        exact (foldVal_eq_zero_iff n hn hpos _).mp hz
    · rw [← hAv, hAeq, Close07a.fhat_foldSubset n hn hpos A'
        (fun a ha => mem_range.mp (hA'sub ha))]
  · rintro ⟨w, hw, rfl⟩
    rw [BridgeB07.mem_badVals_iff] at hw
    obtain ⟨hw0, A', hA'adm, hlow', hA'w⟩ := hw
    rw [BridgeB07.admissible, mem_powersetCard] at hA'adm
    obtain ⟨hA'sub, hA'card⟩ := hA'adm
    have hlt : ∀ a ∈ A', a < n := fun a ha => mem_range.mp (hA'sub ha)
    refine ⟨?_, Close07a.foldSubset n A', ?_, ?_, ?_⟩
    · intro h0; exact hw0 ((foldVal_eq_zero_iff n hn hpos w).mp h0)
    · rw [BridgeB07.admissible, mem_powersetCard]
      refine ⟨foldSubset_subset_range n hA'sub, ?_⟩
      rw [card_foldSubset n hA'sub, hA'card]; ring
    · intro j hj1 hjm
      rcases Nat.even_or_odd j with ⟨j2, rfl⟩ | hodd
      · have h2 : j2 + j2 = 2 * j2 := by ring
        rw [h2, Close07a.fhat_foldSubset n hn hpos A' hlt, hlow' j2 (by omega) (by omega)]
        exact foldVal_zero n hn
      · rw [fhat_eq_close07b]
        exact Close07b.fhat_odd_eq_zero_of_antipodalClosed hpos hodd
          (foldSubset_subset_range n hA'sub) (antipodalClosed_foldSubset n hA'sub)
    · rw [Close07a.fhat_foldSubset n hn hpos A' hlt, hA'w]

/-- **The guarded doubling count identity.** For even `n > 0`, even `k` and `m' ≥ 1`,
`cf (2n) k (2m') = cf n (k / 2) m'`. -/
theorem cf_double (n k m' : ℕ) (hn : Even n) (hpos : 0 < n) (hk : Even k) (hm : 1 ≤ m') :
    BridgeB07.cf (2 * n) k (2 * m') = BridgeB07.cf n (k / 2) m' := by
  unfold BridgeB07.cf
  rw [badVals_double_eq_image n k m' hn hpos hk hm,
    card_image_of_injective _ (Close07a.foldVal_injective n hn hpos)]

/-- **The guarded even half of E6 holds**: `BridgeB07.DoublingBijectionGuarded` is a theorem. -/
theorem doublingBijectionGuarded_holds : BridgeB07.DoublingBijectionGuarded := by
  intro t k m' hk hm'
  exact cf_double (2 ^ (t + 1)) k m' ⟨2 ^ t, by ring⟩ (by positivity) hk hm'

/-- **The guarded odd half of E6 holds**: `BridgeB07.OddGradeVanishesGuarded` is a theorem, by
transport from `Close07c.cf_odd_eq_zero`. -/
theorem oddGradeVanishesGuarded_holds : BridgeB07.OddGradeVanishesGuarded := by
  intro n k m hn hm hm1
  rw [cf_eq_close07c]
  exact Close07c.cf_odd_eq_zero hn hm hm1

/-! ### Refutations of the unguarded forms -/

/-- **Odd capacity kills the even grades.** For `n > 0`, odd `k` and `m' ≥ 1`, the level-`2n`
grade-`2m'` bad-value set is empty: the grade-`1` constraint forces antipodal closure, hence even
cardinality, while admissible carriers have the odd size `k + 2m'`. -/
theorem badVals_double_odd_eq_empty (n k m' : ℕ) (hpos : 0 < n) (hk : Odd k) (hm : 1 ≤ m') :
    BridgeB07.badVals (2 * n) k (2 * m') = ∅ := by
  ext v
  simp only [Finset.notMem_empty, iff_false]
  rw [BridgeB07.mem_badVals_iff]
  rintro ⟨_, A, hAadm, hlow, _⟩
  rw [BridgeB07.admissible, mem_powersetCard] at hAadm
  obtain ⟨hAsub, hAcard⟩ := hAadm
  have hcl : Close07b.AntipodalClosed A n :=
    (Close07b.grade_one_zero_iff_antipodalClosed hpos hAsub).mp (by
      rw [← fhat_eq_close07b]; exact hlow 1 le_rfl (by omega))
  have hA'sub : A.filter (· < n) ⊆ range n := fun x hx => mem_range.mpr (mem_filter.mp hx).2
  have hc := card_foldSubset n hA'sub
  rw [← eq_foldSubset_of_antipodalClosed n hAsub hcl, hAcard] at hc
  obtain ⟨r, rfl⟩ := hk
  omega

/-- The level-`4` grade-`2` count at capacity `1` vanishes. -/
theorem cf_four_one_two_eq_zero : BridgeB07.cf 4 1 2 = 0 := by
  have h0 : BridgeB07.badVals 4 1 2 = ∅ :=
    badVals_double_odd_eq_empty 2 1 1 (by norm_num) odd_one le_rfl
  rw [BridgeB07.cf, h0, Finset.card_empty]

/-- The level-`2` grade-`1` count at capacity `0` is nonzero, by transport from
`Close07c.cf_two_zero_one_ne_zero`. -/
theorem cf_two_zero_one_ne_zero : BridgeB07.cf 2 0 1 ≠ 0 := by
  rw [cf_eq_close07c]
  exact Close07c.cf_two_zero_one_ne_zero

/-- **`Close07a.FoldImageHyp` is false**, at `n = 2`, `k = 1`, `m' = 1`. -/
theorem not_foldImageHyp : ¬ Close07a.FoldImageHyp := by
  intro h
  have : BridgeB07.cf 4 1 2 = BridgeB07.cf 2 0 1 :=
    Close07a.doublingBijection_of_foldImage h 2 1 1 ⟨1, rfl⟩ (by norm_num)
  rw [cf_four_one_two_eq_zero] at this
  exact cf_two_zero_one_ne_zero this.symm

/-- **`Close07b.FoldingBijection` is false**, at `nn = 2`, `k = 1`, `m' = 1`. -/
theorem not_foldingBijection : ¬ Close07b.FoldingBijection := by
  intro h
  have : BridgeB07.cf 4 1 2 = BridgeB07.cf 2 0 1 := h 2 1 1
  rw [cf_four_one_two_eq_zero] at this
  exact cf_two_zero_one_ne_zero this.symm

/-- **`BridgeB07.DoublingBijection` is false**, at `n = 2`, `k = 1`, `m' = 1`. -/
theorem not_doublingBijection : ¬ BridgeB07.DoublingBijection := by
  intro h
  have : BridgeB07.cf 4 1 2 = BridgeB07.cf 2 0 1 := h 2 1 1
  rw [cf_four_one_two_eq_zero] at this
  exact cf_two_zero_one_ne_zero this.symm

/-- **`BridgeB07.OddGradeVanishes` is false**, at `n = 1`, `k = 0`, `m = 1`. -/
theorem not_oddGradeVanishes : ¬ BridgeB07.OddGradeVanishes := by
  intro h
  have : BridgeB07.cf 2 0 1 = 0 := h 1 0 1 odd_one
  exact cf_two_zero_one_ne_zero this

end ArkLib.ProximityGap.Close07d

#print axioms ArkLib.ProximityGap.Close07d.fhat_eq_close07b
#print axioms ArkLib.ProximityGap.Close07d.cf_eq_close07c
#print axioms ArkLib.ProximityGap.Close07d.foldVal_zero
#print axioms ArkLib.ProximityGap.Close07d.foldVal_eq_zero_iff
#print axioms ArkLib.ProximityGap.Close07d.foldSubset_subset_range
#print axioms ArkLib.ProximityGap.Close07d.card_foldSubset
#print axioms ArkLib.ProximityGap.Close07d.antipodalClosed_foldSubset
#print axioms ArkLib.ProximityGap.Close07d.eq_foldSubset_of_antipodalClosed
#print axioms ArkLib.ProximityGap.Close07d.badVals_double_eq_image
#print axioms ArkLib.ProximityGap.Close07d.cf_double
#print axioms ArkLib.ProximityGap.Close07d.doublingBijectionGuarded_holds
#print axioms ArkLib.ProximityGap.Close07d.oddGradeVanishesGuarded_holds
#print axioms ArkLib.ProximityGap.Close07d.badVals_double_odd_eq_empty
#print axioms ArkLib.ProximityGap.Close07d.cf_four_one_two_eq_zero
#print axioms ArkLib.ProximityGap.Close07d.cf_two_zero_one_ne_zero
#print axioms ArkLib.ProximityGap.Close07d.not_foldImageHyp
#print axioms ArkLib.ProximityGap.Close07d.not_foldingBijection
#print axioms ArkLib.ProximityGap.Close07d.not_doublingBijection
#print axioms ArkLib.ProximityGap.Close07d.not_oddGradeVanishes
