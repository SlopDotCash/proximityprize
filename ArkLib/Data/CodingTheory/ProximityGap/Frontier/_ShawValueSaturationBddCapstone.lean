/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueCapstone

/-!
# Shaw-value `O(1)` ⇔ bounded-range rung (#444, door-(iv) Lane-2)

The prose reduction at the heart of the campaign is `prize ⇔ Sh(n) = O(1)`.  The arithmetic
`prize ⇔ bounded Shaw value` rung is already machine-checked in `ShawValueCapstone`
(`rawPrizeFamilyBound_iff_shawValueFamilyBound`).  What was **not** yet kernel-locked is the other
half of the `O(1)` phrase: the elementary logical fact that

> *a uniform constant bounding the Shaw-value family exists*  ⇔  *the Shaw-value family is bounded
> above (`BddAbove` of its range)*,

i.e. the formal content of "`O(1)`".  The empirical door-(iv) Lane-1 datum (the measured prize
ratio `R(n) = M / sqrt(n L)` saturating into a flat band, DISPROOF_LOG) is exactly an observation
that the Shaw-value family *appears* bounded above; this file pins, axiom-clean, the logical bridge
from "the family is bounded above" to "a uniform prize constant `C` exists" — the precise sense in
which a *proof* of saturation would be a *proof* of the prize.

This is **Lane-2 infrastructure only**.  It proves no anti-concentration, no cancellation, and no
prize bound: it states that the open analytic task ("show the normalized worst-frequency value is
bounded above") is *logically equivalent* to the prize-shaped existence statement, with all the
division-by-scale bookkeeping discharged.  The hard content — that the supremum is actually finite
for the thin monomial sum — remains OPEN.

Main statements:

* `exists_shawValueFamilyBound_iff_bddAbove_range` — `(∃ C, shawValueFamilyBound …) ↔
  BddAbove (Set.range (shawValue ∘ family))`.
* `exists_rawPrizeFamilyBound_iff_bddAbove_shawRange` — the same with the **raw** prize-family bound
  on the left (composing the existing `prize ⇔ Shaw` rung), so the prize is `O(1)` of the Shaw
  values directly.
* `bddAbove_shawRange_of_eventually_le` — the sequence/"saturation" form over `ℕ`: if the Shaw
  values are bounded by `B` for all `i ≥ N` (a flat tail) then the whole range is bounded above
  (a finite head is always bounded), so the prize `O(1)` existence follows.  This is the exact
  logical step "measured saturation ⟹ a finite uniform constant exists".
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.ShawValueSaturationBdd

open ArkLib.ProximityGap.Frontier.ShawValueCapstone

/-- The Shaw-value evaluated along a parameter family, as a function `ι → ℝ`. -/
noncomputable def shawFamily {ι : Type*} (M n L : ι → ℝ) : ι → ℝ :=
  fun i => shawValue (M i) (n i) (L i)

@[simp] theorem shawFamily_apply {ι : Type*} (M n L : ι → ℝ) (i : ι) :
    shawFamily M n L i = shawValue (M i) (n i) (L i) := rfl

/-- A uniform Shaw-value bound by `C` is exactly an upper bound (in the `∀`-sense) for the
Shaw-value family function. -/
theorem shawValueFamilyBound_iff_forall_le {ι : Type*} {M n L : ι → ℝ} {C : ℝ} :
    shawValueFamilyBound M n L C ↔ ∀ i, shawFamily M n L i ≤ C := Iff.rfl

/-- **`O(1)` ⇔ bounded-above range.**  A uniform constant bounding the Shaw-value family exists iff
the range of the Shaw-value family is bounded above.  This is the formal content of "the Shaw value
is `O(1)`". -/
theorem exists_shawValueFamilyBound_iff_bddAbove_range {ι : Type*} {M n L : ι → ℝ} :
    (∃ C, shawValueFamilyBound M n L C) ↔ BddAbove (Set.range (shawFamily M n L)) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro y ⟨i, rfl⟩
    exact hC i
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i => ?_⟩
    exact hC ⟨i, rfl⟩

/-- **Prize is `O(1)` of the Shaw values.**  Under pointwise positivity of the prize scale, a uniform
*raw* prize-family bound exists iff the Shaw-value range is bounded above.  Composes the existing
`prize ⇔ Shaw` arithmetic rung with the `O(1)` ⇔ `BddAbove` rung: a *proof that the normalized
worst-frequency value is bounded above* is *exactly* a proof of the prize-shaped existence statement
`∃ C, M ≤ C·√(n L)` uniformly. -/
theorem exists_rawPrizeFamilyBound_iff_bddAbove_shawRange {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    (∃ C, rawPrizeFamilyBound M n L C) ↔ BddAbove (Set.range (shawFamily M n L)) := by
  rw [← exists_shawValueFamilyBound_iff_bddAbove_range]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, (rawPrizeFamilyBound_iff_shawValueFamilyBound hs).1 hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, (rawPrizeFamilyBound_iff_shawValueFamilyBound hs).2 hC⟩

/-- Pointwise-positive wrapper for `exists_rawPrizeFamilyBound_iff_bddAbove_shawRange`. -/
theorem exists_rawPrizeFamilyBound_iff_bddAbove_shawRange_of_pos {ι : Type*} {M n L : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    (∃ C, rawPrizeFamilyBound M n L C) ↔ BddAbove (Set.range (shawFamily M n L)) :=
  exists_rawPrizeFamilyBound_iff_bddAbove_shawRange
    (fun i => prizeScale_pos (hn i) (hL i))

/-- **Saturation (flat tail) ⟹ bounded range**, over a `ℕ`-indexed tower.  If the Shaw values are
bounded by `B` for every index `i ≥ N` (an eventually-flat band, as the Lane-1 prize-ratio probe
measures), then the range of the Shaw-value family is bounded above: the finite head `i < N` is
always bounded.  Together with `exists_rawPrizeFamilyBound_iff_bddAbove_shawRange`, this is the exact
logical content of "measured saturation ⟹ a uniform prize constant exists". -/
theorem bddAbove_shawRange_of_eventually_le {M n L : ℕ → ℝ} {N : ℕ} {B : ℝ}
    (htail : ∀ i, N ≤ i → shawFamily M n L i ≤ B) :
    BddAbove (Set.range (shawFamily M n L)) := by
  -- Split the range into the finite head `i < N` and the bounded tail `i ≥ N`.
  have hsplit : Set.range (shawFamily M n L) ⊆
      (shawFamily M n L) '' {i | i < N} ∪ Set.Iic B := by
    rintro y ⟨i, rfl⟩
    rcases lt_or_ge i N with hi | hi
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr (htail i hi)
  -- The head image is finite (finite domain), hence bounded above; `Iic B` is bounded above.
  have hheadFin : ((shawFamily M n L) '' {i | i < N}).Finite :=
    (Set.finite_Iio N).image _ |>.subset (by
      rintro y ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩)
  have hhead : BddAbove ((shawFamily M n L) '' {i | i < N}) := hheadFin.bddAbove
  have htailB : BddAbove (Set.Iic B) := bddAbove_Iic
  exact (hhead.union htailB).mono hsplit

end ArkLib.ProximityGap.Frontier.ShawValueSaturationBdd

#print axioms ArkLib.ProximityGap.Frontier.ShawValueSaturationBdd.exists_shawValueFamilyBound_iff_bddAbove_range
#print axioms ArkLib.ProximityGap.Frontier.ShawValueSaturationBdd.exists_rawPrizeFamilyBound_iff_bddAbove_shawRange
#print axioms ArkLib.ProximityGap.Frontier.ShawValueSaturationBdd.exists_rawPrizeFamilyBound_iff_bddAbove_shawRange_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueSaturationBdd.bddAbove_shawRange_of_eventually_le
