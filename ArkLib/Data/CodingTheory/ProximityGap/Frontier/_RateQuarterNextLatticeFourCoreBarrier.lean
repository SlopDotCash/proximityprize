/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConstantWeightPlotkinBound

/-!
# Rate-quarter next lattice: the three- and four-core overlap barriers

Write the smooth three-line construction at `m = 3*r+1`.  After maximal
private thickening its decoded-line cores have size

`z = 8*m+r = 25*r+8`,

inside a universe of size `n = 16*m = 48*r+16`.  The landed `mu_16`
locator cell has pair-core size `3*m = 9*r+3`.

This file proves that four cores of size at least `z` cannot all retain that
pair cap once `r >= 13`.  Equivalently, every four-core improvement of the
known construction forces a genuinely new pair intersection of size at least
`3*m+1`.  The proof is the exact-diagonal constant-weight Plotkin inequality;
there is no asymptotic estimate.

At the next agreement lattice, a one-fresh line needs a core of size
`z' = z+1 = 25*r+9`.  Already three such cores cannot all retain the old pair
cap: inclusion--exclusion would put at least `48*r+18` coordinates in their
union, two more than the `48*r+16`-point universe.  Thus every one-fresh
improvement at the next lattice forces a pair intersection of size at least
`3*m+1`, whether it uses three lines or four or more.

This is a barrier, not the rate-quarter upper bound.  It sharply identifies
what a stronger multi-line counterconstruction must supply: a higher-degree
split-locator relation rather than another copy of the cubic `mu_16` cell.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.RateQuarterNextLatticeFourCoreBarrier

open ConstantWeightPlotkinBound

attribute [local instance] Classical.propDecidable

variable {U : Type} [Fintype U] [DecidableEq U]

/-- Three next-lattice one-fresh cores of size `25*r+9` in a
`48*r+16`-point universe force one pair intersection above the old
`9*r+3` (`=3m`) smooth-locator cap.

Indeed, if all three pair intersections had size at most `9*r+3`, the
three-set inclusion--exclusion lower bound would give union size at least
`3*(25*r+9)-3*(9*r+3)=48*r+18`, while the universe has size only
`48*r+16`. -/
theorem exists_pair_inter_card_ge_nine_mul_add_four_of_three_next_cores
    {r : Nat}
    (hU : Fintype.card U = 48 * r + 16)
    (S : Fin 3 → Finset U)
    (hsize : ∀ i, 25 * r + 9 ≤ (S i).card) :
    ∃ i j : Fin 3, i ≠ j ∧ 9 * r + 4 ≤ (S i ∩ S j).card := by
  by_contra hnot
  push Not at hnot
  let A := S (0 : Fin 3)
  let B := S (1 : Fin 3)
  let C := S (2 : Fin 3)
  have hAB : (A ∩ B).card ≤ 9 * r + 3 := by
    have hsmall := hnot (0 : Fin 3) (1 : Fin 3) (by decide)
    simpa only [A, B] using (show (S 0 ∩ S 1).card ≤ 9 * r + 3 by omega)
  have hAC : (A ∩ C).card ≤ 9 * r + 3 := by
    have hsmall := hnot (0 : Fin 3) (2 : Fin 3) (by decide)
    simpa only [A, C] using (show (S 0 ∩ S 2).card ≤ 9 * r + 3 by omega)
  have hBC : (B ∩ C).card ≤ 9 * r + 3 := by
    have hsmall := hnot (1 : Fin 3) (2 : Fin 3) (by decide)
    simpa only [B, C] using (show (S 1 ∩ S 2).card ≤ 9 * r + 3 by omega)
  have hA : 25 * r + 9 ≤ A.card := by simpa only [A] using hsize 0
  have hB : 25 * r + 9 ≤ B.card := by simpa only [B] using hsize 1
  have hC : 25 * r + 9 ≤ C.card := by simpa only [C] using hsize 2
  have hABbook := Finset.card_union_add_card_inter A B
  have hABCbook := Finset.card_union_add_card_inter (A ∪ B) C
  have hdistrib : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
    ext x
    simp only [mem_inter, mem_union]
    tauto
  have hlast : ((A ∪ B) ∩ C).card ≤ (A ∩ C).card + (B ∩ C).card := by
    rw [hdistrib]
    exact Finset.card_union_le _ _
  have hunion : (A ∪ B ∪ C).card ≤ 48 * r + 16 := by
    calc
      (A ∪ B ∪ C).card ≤ (Finset.univ : Finset U).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card U := Finset.card_univ
      _ = 48 * r + 16 := hU
  omega

/-- The three-core next-lattice barrier in the natural `m=3*r+1` notation:
three one-fresh cores of size `8m+r+1` force a pair core of size `3m+1`. -/
theorem exists_pair_inter_card_ge_three_mul_add_one_of_three_next_cores
    {m r : Nat} (hm : m = 3 * r + 1)
    (hU : Fintype.card U = 16 * m)
    (S : Fin 3 → Finset U)
    (hsize : ∀ i, 8 * m + r + 1 ≤ (S i).card) :
    ∃ i j : Fin 3, i ≠ j ∧ 3 * m + 1 ≤ (S i ∩ S j).card := by
  subst m
  have h := exists_pair_inter_card_ge_nine_mul_add_four_of_three_next_cores
    (U := U) (r := r) (by omega) S (by
      intro i
      have hi := hsize i
      omega)
  simpa only [show 3 * (3 * r + 1) + 1 = 9 * r + 4 by omega] using h

/-- Four `25*r+8`-point cores in a `48*r+16`-point universe force one pair
intersection above the old `9*r+3` (`=3m`) smooth-locator cap. -/
theorem exists_pair_inter_card_ge_nine_mul_add_four
    {r : Nat} (hr : 13 ≤ r)
    (hU : Fintype.card U = 48 * r + 16)
    (S : Fin 4 → Finset U)
    (hsize : ∀ i, 25 * r + 8 ≤ (S i).card) :
    ∃ i j : Fin 4, i ≠ j ∧ 9 * r + 4 ≤ (S i ∩ S j).card := by
  by_contra hnot
  push Not at hnot
  let T : Fin 4 → Finset U := fun i =>
    Classical.choose (Finset.exists_subset_card_eq (hsize i))
  have hTsub : ∀ i, T i ⊆ S i := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).1
  have hTcard : ∀ i, (T i).card = 25 * r + 8 := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).2
  have hTpair : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 9 * r + 3 := by
    intro i j hij
    have hpairS : (S i ∩ S j).card ≤ 9 * r + 3 := by
      have hsmall := hnot i j hij
      omega
    exact (Finset.card_le_card
      (Finset.inter_subset_inter (hTsub i) (hTsub j))).trans hpairS
  have hplot := constantWeight_plotkin T (25 * r + 8) (9 * r + 3)
    hTcard hTpair
  rw [Fintype.card_fin, hU] at hplot
  have hgapIdentity :
      (25 * r + 8) ^ 2 =
        (48 * r + 16) * (9 * r + 3) +
          (193 * r ^ 2 + 112 * r + 16) := by
    ring
  have hgap :
      (25 * r + 8) ^ 2 - (48 * r + 16) * (9 * r + 3) =
        193 * r ^ 2 + 112 * r + 16 := by
    omega
  have hdiff : (25 * r + 8) - (9 * r + 3) = 16 * r + 5 := by
    omega
  rw [hgap, hdiff] at hplot
  have hrr : 13 * r ≤ r ^ 2 := by
    calc
      13 * r ≤ r * r := Nat.mul_le_mul_right r hr
      _ = r ^ 2 := by ring
  nlinarith

/-- The same barrier in the natural `m=3*r+1` notation used by the smooth
construction: four cores of size `8m+r` force a pair core of size `3m+1`. -/
theorem exists_pair_inter_card_ge_three_mul_add_one
    {m r : Nat} (hm : m = 3 * r + 1) (hr : 13 ≤ r)
    (hU : Fintype.card U = 16 * m)
    (S : Fin 4 → Finset U)
    (hsize : ∀ i, 8 * m + r ≤ (S i).card) :
    ∃ i j : Fin 4, i ≠ j ∧ 3 * m + 1 ≤ (S i ∩ S j).card := by
  subst m
  have h := exists_pair_inter_card_ge_nine_mul_add_four hr (by omega) S (by
    intro i
    have hi := hsize i
    omega)
  simpa only [show 3 * (3 * r + 1) + 1 = 9 * r + 4 by omega] using h

end ArkLib.ProximityGap.Frontier.RateQuarterNextLatticeFourCoreBarrier

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateQuarterNextLatticeFourCoreBarrier

#print axioms exists_pair_inter_card_ge_nine_mul_add_four_of_three_next_cores
#print axioms exists_pair_inter_card_ge_three_mul_add_one_of_three_next_cores
#print axioms exists_pair_inter_card_ge_nine_mul_add_four
#print axioms exists_pair_inter_card_ge_three_mul_add_one
