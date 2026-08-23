/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HammingBallVolume

/-!
# The Hamming (sphere-packing) bound

The dual of the Gilbert–Varshamov existence count: a code `C ⊆ (ι → F)` with minimum distance
`≥ 2r+1` packs disjoint radius-`r` balls, so it cannot be too large:

  `|C| · Vol_q(δ, n)  ≤  qⁿ = |ι → F|`    (`r = ⌊δ·n⌋`),   i.e.   `|C| ≤ qⁿ / Vol_q(δ, n)`.

Proof: minimum distance `≥ 2r+1` makes the radius-`r` balls pairwise disjoint (a common point would
put two codewords within `2r` of each other, by the triangle inequality), so their sizes sum to at
most `qⁿ`; each ball has size `Vol_q(δ, n)` (`hammingBallVolume_eq_ncard_hammingBall`).

Together with `GilbertVarshamov.exists_packing_card_mul_hammingBallVolume_ge` this brackets the
maximal code size by `Vol` from both sides.

## Main result (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `card_mul_hammingBallVolume_le_of_minDist`.
-/

namespace CodingTheory

open Finset

/-- **Hamming / sphere-packing bound.** A code with pairwise distance `≥ 2⌊δ·n⌋+1` satisfies
`|C| · Vol_q(δ, n) ≤ qⁿ`. -/
theorem card_mul_hammingBallVolume_le_of_minDist
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Fintype F] [DecidableEq F]
    (C : Finset (ι → F)) (δ : ℝ)
    (hpack : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' →
      2 * ⌊δ * Fintype.card ι⌋₊ + 1 ≤ hammingDist c c') :
    C.card * hammingBallVolume (Fintype.card F) δ (Fintype.card ι)
      ≤ Fintype.card (ι → F) := by
  classical
  set r : ℕ := ⌊δ * Fintype.card ι⌋₊ with hr
  have hdisj : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' →
      Disjoint ((ListDecodable.hammingBall c r).toFinset)
               ((ListDecodable.hammingBall c' r).toFinset) := by
    intro c hc c' hc' hcc'
    rw [Finset.disjoint_left]
    intro x hxc hxc'
    rw [Set.mem_toFinset, ListDecodable.hammingBall, Set.mem_setOf_eq] at hxc hxc'
    have hxc2 : hammingDist c x ≤ r := by convert hxc using 2
    have hxc'2 : hammingDist c' x ≤ r := by convert hxc' using 2
    have htri : hammingDist c c' ≤ 2 * r := by
      calc hammingDist c c' ≤ hammingDist c x + hammingDist x c' := hammingDist_triangle c x c'
        _ = hammingDist c x + hammingDist c' x := by rw [hammingDist_comm x c']
        _ ≤ r + r := add_le_add hxc2 hxc'2
        _ = 2 * r := by ring
    have hp := hpack c hc c' hc' hcc'
    omega
  calc C.card * hammingBallVolume (Fintype.card F) δ (Fintype.card ι)
      = ∑ _c ∈ C, hammingBallVolume (Fintype.card F) δ (Fintype.card ι) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = ∑ c ∈ C, (ListDecodable.hammingBall c r).toFinset.card := by
        apply Finset.sum_congr rfl
        intro c _
        rw [← Set.ncard_eq_toFinset_card', ← hammingBallVolume_eq_ncard_hammingBall δ c]
    _ = (C.biUnion (fun c => (ListDecodable.hammingBall c r).toFinset)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset (ι → F)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card (ι → F) := Finset.card_univ

end CodingTheory

-- Axiom audit.
#print axioms CodingTheory.card_mul_hammingBallVolume_le_of_minDist
