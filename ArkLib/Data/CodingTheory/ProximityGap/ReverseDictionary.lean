/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EpsMCAInterleavedList

/-!
# The reverse dictionary: list-decoding lower bounds from MCA exactness (#357, item 17)

Item 17 of the 26-thread review: the LD⇔MCA dictionary has only ever been consumed
forward (list bounds ⟹ MCA bounds).  This file lands the reverse engine — the
contrapositive of `epsMCA_le_of_interleavedList_card_le`:

**`exists_interleavedList_card_gt_of_epsMCA_gt`** — whenever the (now plentiful)
exact MCA values exceed the dictionary bound for a putative list size `L`, some pair
has interleaved list size `> L` at the collapse floor:

  `(1 + (n − (2t − n))·L)/q < ε_mca(C, δ)  ⟹  ∃ f₁ f₂, L < |Λ(C^{≡2}, f₁, f₂, 2t−n)|`.

Every exact window-interior MCA value (`MCAWindowInteriorExact`, `JohnsonExactPoint`,
the staircase exacts) now produces machine-checked **interleaved list-decoding lower
bounds** — new combinatorial data flowing in the direction the literature has not
exploited: from correlated agreement back to list decoding.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **The reverse dictionary.**  If the MCA error exceeds the forward dictionary's
bound for list size `L`, some pair has interleaved list size exceeding `L` at the
collapse floor. -/
theorem exists_interleavedList_card_gt_of_epsMCA_gt (C : Finset (ι → F))
    (hC : Round17CAPair.PairClosed C) (δ : ℝ≥0) (L : ℕ)
    (h : ((1 + (Fintype.card ι -
        (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) * L : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞)
      < epsMCA (F := F) (A := F) (↑C : Set (ι → F)) δ) :
    ∃ f₁ f₂ : ι → F, L < (InterleavedMCACollapse.interleavedList C f₁ f₂
      (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)).card := by
  by_contra hno
  push Not at hno
  exact absurd (epsMCA_le_of_interleavedList_card_le C hC δ L hno) (not_le.mpr h)

end ProximityGap

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.exists_interleavedList_card_gt_of_epsMCA_gt
