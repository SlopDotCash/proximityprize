/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HammingBallVolume

/-!
# Gilbert–Varshamov sphere-covering count

The counting core of the Gilbert–Varshamov bound: if the radius-`r` Hamming balls centred at a
code `C` cover the whole ambient space `ι → F` (`r = ⌊δ·n⌋`), then

  `qⁿ = |ι → F|  ≤  |C| · Vol_q(δ, n)`.

Equivalently `|C| ≥ qⁿ / Vol`. Taking `C` to be a *maximal* code of minimum distance `> r` makes the
covering hypothesis automatic (any uncovered point could be adjoined), yielding the classical GV
existence bound; this file isolates the covering ⇒ count step (the easy, code-independent half),
built directly on `hammingBallVolume_eq_ncard_hammingBall`.

## Main result (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `card_le_card_mul_hammingBallVolume_of_covering`.
-/

namespace CodingTheory

open Finset

/-- **Gilbert–Varshamov covering count.** If the radius-`⌊δ·n⌋` Hamming balls centred at the
codewords of `C` cover `ι → F`, then `|ι → F| ≤ |C| · Vol_q(δ, n)`. -/
theorem card_le_card_mul_hammingBallVolume_of_covering
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Fintype F] [DecidableEq F]
    (C : Finset (ι → F)) (δ : ℝ)
    (hcover : ∀ x : ι → F, ∃ c ∈ C,
      x ∈ ListDecodable.hammingBall c ⌊δ * Fintype.card ι⌋₊) :
    Fintype.card (ι → F)
      ≤ C.card * hammingBallVolume (Fintype.card F) δ (Fintype.card ι) := by
  classical
  set r : ℕ := ⌊δ * Fintype.card ι⌋₊ with hr
  have hsub :
      (Finset.univ : Finset (ι → F))
        ⊆ C.biUnion (fun c => (ListDecodable.hammingBall c r).toFinset) := by
    intro x _
    obtain ⟨c, hc, hx⟩ := hcover x
    rw [Finset.mem_biUnion]
    exact ⟨c, hc, Set.mem_toFinset.mpr hx⟩
  calc Fintype.card (ι → F)
      = (Finset.univ : Finset (ι → F)).card := (Finset.card_univ).symm
    _ ≤ (C.biUnion (fun c => (ListDecodable.hammingBall c r).toFinset)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ c ∈ C, (ListDecodable.hammingBall c r).toFinset.card := Finset.card_biUnion_le
    _ = ∑ _c ∈ C, hammingBallVolume (Fintype.card F) δ (Fintype.card ι) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [← Set.ncard_eq_toFinset_card', ← hammingBallVolume_eq_ncard_hammingBall δ c]
    _ = C.card * hammingBallVolume (Fintype.card F) δ (Fintype.card ι) := by
        rw [Finset.sum_const, smul_eq_mul]

end CodingTheory

-- Axiom audit.
#print axioms CodingTheory.card_le_card_mul_hammingBallVolume_of_covering
