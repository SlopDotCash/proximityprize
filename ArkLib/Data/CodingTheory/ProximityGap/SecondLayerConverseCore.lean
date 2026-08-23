/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ChordConverseCore

/-!
# The second-layer converse: the no-antipodal branch of the wide-circuit classification

Campaign #357, exactness-converse lane, increment 3. Companion to
`ChordConverseCore.lean`: in the generic branch with **no** antipodal pair, the
canonical matching of a balanced multiplicity-free `Distinct6` stack is forced into one
of the **eight second-layer seed systems** — the supply systems of
`SecondLayerSeedFamily.lean` (shapes I/II and their orientation images).

The proof is the canonical-matching case tree, **machine-generated** from the exact
certificate data of `probe_noantipodal_branch_tree.py` (10395 pairings, 10387 killed,
8 survivors) by `gen_noantipodal_lean.py`, in the verified syntax patterns of
`ChordConverseCore.lean`. Every kill is one `linear_combination` onto a
`Distinct6`/genericity/no-antipodal/injectivity hypothesis (with doubling-kernel
branches), and each surviving branch concludes as soon as its three system congruences
are derivable.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option linter.style.longFile 1700

namespace ArkLib.ProximityGap.SecondLayerConverseCore

open ArkLib.ProximityGap.ChordConverseCore

variable {R : Type*} [CommRing R]

/-- **The no-antipodal-branch classification.** Over any commutative ring with a
half-period `h`: a `Distinct6` stack with no antipodal pair, pairwise-distinct
products, injective (multiplicity-free) and `+h`-closed (balanced) shifted 12-stack
satisfies one of the eight second-layer seed systems. -/
theorem secondLayer_of_no_antipodal {A₁ B₁ A₂ B₂ A₃ B₃ h : R}
    (hh2 : h + h = 0) (hh0 : h ≠ 0)
    (hker : ∀ u : R, u + u = 0 → u = 0 ∨ u = h)
    (hA1B1 : A₁ ≠ B₁) (hA2B2 : A₂ ≠ B₂) (hA3B3 : A₃ ≠ B₃)
    (hA1A2 : A₁ ≠ A₂) (hA1B2 : A₁ ≠ B₂) (hB1A2 : B₁ ≠ A₂) (hB1B2 : B₁ ≠ B₂)
    (hA1A3 : A₁ ≠ A₃) (hA1B3 : A₁ ≠ B₃) (hB1A3 : B₁ ≠ A₃) (hB1B3 : B₁ ≠ B₃)
    (hA2A3 : A₂ ≠ A₃) (hA2B3 : A₂ ≠ B₃) (hB2A3 : B₂ ≠ A₃) (hB2B3 : B₂ ≠ B₃)
    (hg12 : A₁ + B₁ ≠ A₂ + B₂) (hg13 : A₁ + B₁ ≠ A₃ + B₃)
    (hg23 : A₂ + B₂ ≠ A₃ + B₃)
    (hna1 : B₁ ≠ A₁ + h) (hna2 : B₂ ≠ A₂ + h) (hna3 : B₃ ≠ A₃ + h)
    (hinj : Function.Injective (chordStack A₁ B₁ A₂ B₂ A₃ B₃ h))
    (hclosed : ∀ x : Fin 12, ∃ y : Fin 12,
      chordStack A₁ B₁ A₂ B₂ A₃ B₃ h y = chordStack A₁ B₁ A₂ B₂ A₃ B₃ h x + h) :
    (B₂ + B₃ = A₁ + B₁ + h ∧ A₃ + B₃ = A₁ + B₂ + h ∧ A₂ + B₂ = A₁ + B₃ + h)
    ∨ (B₂ + A₃ = A₁ + B₁ + h ∧ A₃ + B₃ = A₁ + B₂ + h ∧ A₂ + B₂ = A₁ + A₃ + h)
    ∨ (B₂ + B₃ = A₁ + B₁ + h ∧ A₃ + B₃ = B₁ + B₂ + h ∧ A₂ + B₂ = B₁ + B₃ + h)
    ∨ (B₂ + A₃ = A₁ + B₁ + h ∧ A₃ + B₃ = B₁ + B₂ + h ∧ A₂ + B₂ = B₁ + A₃ + h)
    ∨ (A₂ + B₃ = A₁ + B₁ + h ∧ A₃ + B₃ = A₁ + A₂ + h ∧ A₂ + B₂ = A₁ + B₃ + h)
    ∨ (A₂ + B₃ = A₁ + B₁ + h ∧ A₃ + B₃ = B₁ + A₂ + h ∧ A₂ + B₂ = B₁ + B₃ + h)
    ∨ (A₂ + A₃ = A₁ + B₁ + h ∧ A₃ + B₃ = A₁ + A₂ + h ∧ A₂ + B₂ = A₁ + A₃ + h)
    ∨ (A₂ + A₃ = A₁ + B₁ + h ∧ A₃ + B₃ = B₁ + A₂ + h ∧ A₂ + B₂ = B₁ + A₃ + h) := by
  obtain ⟨y0, hp0⟩ := hclosed 0
  fin_cases y0 <;> simp only [chordStack] at hp0
  · exact absurd (by linear_combination -hp0 : h = (0 : R)) hh0
  · exact absurd (by linear_combination hp0 : B₂ = A₂ + h) hna2
  · exact absurd (by linear_combination hp0 : A₁ + B₁ = A₃ + B₃) hg13
  · -- continue: partner of 0 is 3
    obtain ⟨y1, hp1⟩ := hclosed 1
    fin_cases y1 <;> simp only [chordStack] at hp1
    · exact absurd (by linear_combination -hp1 - hh2 : B₂ = A₂ + h) hna2
    · exact absurd (by linear_combination -hp1 : h = (0 : R)) hh0
    · have hd : (A₂ - B₂) + (A₂ - B₂) = 0 := by linear_combination -hp0 + hp1
      rcases hker _ hd with h0 | hh
      · exact absurd (by linear_combination h0 : A₂ = B₂) hA2B2
      · exact absurd (by linear_combination hp0 - hp1 + hh : B₂ = A₂ + h) hna2
    · exact absurd (by linear_combination -hp0 + hp1 : A₂ = B₂) hA2B2
    · exact absurd (by linear_combination hp1 : A₁ = B₂) hA1B2
    · exact absurd (by linear_combination hp1 : B₁ = B₂) hB1B2
    · exact absurd (by linear_combination hp1 : A₂ = B₃) hA2B3
    · exact absurd (by linear_combination hp1 : A₂ = A₃) hA2A3
    · -- continue: partner of 1 is 8
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₂ = B₂) hA2B2
      · refine absurd (hinj (a₁ := 1) (a₂ := 5) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp0 - hp1 - hp2 - hh2 : B₁ = A₂) hB1A2
      · exact absurd (by linear_combination hp1 + hp2 + hh2 : A₁ = B₁) hA1B1
      · -- continue: partner of 2 is 5
        obtain ⟨y3, hp3⟩ := hclosed 4
        fin_cases y3 <;> simp only [chordStack] at hp3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = B₂) hA1B2
        · exact absurd (by linear_combination -hp1 - 2 * hp2 - hp3 - 2 * hh2 : A₁ = B₁) hA1B1
        · refine absurd (hinj (a₁ := 0) (a₂ := 4) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 + hp3 - 2 * hh2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - 2 * hh2 : B₁ = A₁ + h) hna1
        · -- continue: partner of 4 is 6
          obtain ⟨y4, hp4⟩ := hclosed 7
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : B₂ = A₃) hB2A3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : A₂ = A₃) hA2A3
          · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp1 - hp2 + hp4 - hh2
          · refine absurd (hinj (a₁ := 0) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 + hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 + hp4 - hh2 : A₃ = B₃) hA3B3
          · refine absurd (hinj (a₁ := 1) (a₂ := 10) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp1 - hp2 - hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : B₃ = A₃ + h) hna3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 2 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : A₁ = B₃) hA1B3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : B₁ = B₃) hB1B3
          · have hd : (B₂ - A₃) + (B₂ - A₃) = 0 := by linear_combination hp0 - 2 * hp1 - 2 * hp2 - hp4 - 3 * hh2
            rcases hker _ hd with h0 | hh
            · exact absurd (by linear_combination h0 : B₂ = A₃) hB2A3
            · refine absurd (hinj (a₁ := 0) (a₂ := 7) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp1 - 2 * hp2 - hh - 3 * hh2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : A₁ + B₁ = A₂ + B₂) hg12
        · -- continue: partner of 4 is 7
          obtain ⟨y4, hp4⟩ := hclosed 6
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : B₂ = B₃) hB2B3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : A₂ = B₃) hA2B3
          · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp1 - hp2 + hp4 - hh2
          · refine absurd (hinj (a₁ := 0) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 + hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - hp4 - 3 * hh2 : A₃ = B₃) hA3B3
          · refine absurd (hinj (a₁ := 1) (a₂ := 11) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp1 - hp2 - hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 2 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - 2 * hh2 : B₃ = A₃ + h) hna3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : A₁ = A₃) hA1A3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : B₁ = A₃) hB1A3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : A₁ + B₁ = A₂ + B₂) hg12
          · have hd : (B₂ - B₃) + (B₂ - B₃) = 0 := by linear_combination hp0 - 2 * hp1 - 2 * hp2 - hp4 - 3 * hh2
            rcases hker _ hd with h0 | hh
            · exact absurd (by linear_combination h0 : B₂ = B₃) hB2B3
            · refine absurd (hinj (a₁ := 0) (a₂ := 6) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp1 - 2 * hp2 - hh - 3 * hh2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - hh2 : A₂ + B₂ = A₃ + B₃) hg23
        · have hd : (A₁ - A₂) + (A₁ - A₂) = 0 := by linear_combination hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2
          rcases hker _ hd with h0 | hh
          · exact absurd (by linear_combination h0 : A₁ = A₂) hA1A2
          · refine absurd (hinj (a₁ := 0) (a₂ := 4) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp1 - 2 * hp2 - hh - 3 * hh2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - hh2 : B₁ = B₃) hB1B3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - hh2 : B₁ = A₃) hB1A3
      · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp1 - hp2 - hh2
      · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp1 - hp2 - hh2
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = B₃) hA2B3
    · -- continue: partner of 1 is 9
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₂ = B₂) hA2B2
      · refine absurd (hinj (a₁ := 1) (a₂ := 4) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp0 - hp1 - hp2 - hh2 : A₁ = A₂) hA1A2
      · -- continue: partner of 2 is 4
        obtain ⟨y3, hp3⟩ := hclosed 5
        fin_cases y3 <;> simp only [chordStack] at hp3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₂) hB1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = B₂) hB1B2
        · exact absurd (by linear_combination -2 * hp1 - hp2 + hp3 - hh2 : A₁ = B₁) hA1B1
        · refine absurd (hinj (a₁ := 0) (a₂ := 5) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 + hp3 - 2 * hh2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₁ + h) hna1
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · -- continue: partner of 5 is 6
          obtain ⟨y4, hp4⟩ := hclosed 7
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : B₂ = A₃) hB2A3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : A₂ = A₃) hA2A3
          · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp1 - hp2 + hp4 - hh2
          · refine absurd (hinj (a₁ := 0) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 + hp4 - 2 * hh2
          · refine absurd (hinj (a₁ := 1) (a₂ := 10) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp1 - hp2 - hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 + hp4 - hh2 : A₃ = B₃) hA3B3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : B₃ = A₃ + h) hna3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 2 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : A₁ = B₃) hA1B3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : B₁ = B₃) hB1B3
          · have hd : (B₂ - A₃) + (B₂ - A₃) = 0 := by linear_combination hp0 - 2 * hp1 - 2 * hp2 - hp4 - 3 * hh2
            rcases hker _ hd with h0 | hh
            · exact absurd (by linear_combination h0 : B₂ = A₃) hB2A3
            · refine absurd (hinj (a₁ := 0) (a₂ := 7) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp1 - 2 * hp2 - hh - 3 * hh2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : A₁ + B₁ = A₂ + B₂) hg12
        · -- continue: partner of 5 is 7
          obtain ⟨y4, hp4⟩ := hclosed 6
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : B₂ = B₃) hB2B3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : A₂ = B₃) hA2B3
          · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp1 - hp2 + hp4 - hh2
          · refine absurd (hinj (a₁ := 0) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 + hp4 - 2 * hh2
          · refine absurd (hinj (a₁ := 1) (a₂ := 11) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp1 - hp2 - hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - hp4 - 3 * hh2 : A₃ = B₃) hA3B3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 2 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - 2 * hh2 : B₃ = A₃ + h) hna3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : A₁ = A₃) hA1A3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : B₁ = A₃) hB1A3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : A₁ + B₁ = A₂ + B₂) hg12
          · have hd : (B₂ - B₃) + (B₂ - B₃) = 0 := by linear_combination hp0 - 2 * hp1 - 2 * hp2 - hp4 - 3 * hh2
            rcases hker _ hd with h0 | hh
            · exact absurd (by linear_combination h0 : B₂ = B₃) hB2B3
            · refine absurd (hinj (a₁ := 0) (a₂ := 6) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp1 - 2 * hp2 - hh - 3 * hh2
        · have hd : (B₁ - A₂) + (B₁ - A₂) = 0 := by linear_combination hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2
          rcases hker _ hd with h0 | hh
          · exact absurd (by linear_combination h0 : B₁ = A₂) hB1A2
          · refine absurd (hinj (a₁ := 0) (a₂ := 5) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp1 - 2 * hp2 - hh - 3 * hh2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - hh2 : A₂ + B₂ = A₃ + B₃) hg23
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - hh2 : A₁ = B₃) hA1B3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - hh2 : A₁ = A₃) hA1A3
      · exact absurd (by linear_combination -hp1 - hp2 - hh2 : A₁ = B₁) hA1B1
      · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp1 - hp2 - hh2
      · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp1 - hp2 - hh2
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = B₃) hA2B3
    · -- continue: partner of 1 is 10
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₂ = B₂) hA2B2
      · refine absurd (hinj (a₁ := 1) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp0 - hp1 - hp2 - hh2 : B₂ = A₃) hB2A3
      · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination hp1 + hp2 + hh2 : A₃ = B₃) hA3B3
      · -- continue: partner of 2 is 7
        obtain ⟨y3, hp3⟩ := hclosed 4
        fin_cases y3 <;> simp only [chordStack] at hp3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = B₂) hA1B2
        · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp1 - 2 * hp2 - hp3 - 2 * hh2
        · refine absurd (hinj (a₁ := 0) (a₂ := 4) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 + hp3 - 2 * hh2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - 2 * hh2 : B₁ = A₁ + h) hna1
        · -- continue: partner of 4 is 6
          obtain ⟨y4, hp4⟩ := hclosed 5
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : B₁ = A₂) hB1A2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : B₁ = B₂) hB1B2
          · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp1 - 2 * hp2 - hp4 - 2 * hh2
          · refine absurd (hinj (a₁ := 0) (a₂ := 5) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 + hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : B₁ = A₁ + h) hna1
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 2 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 + hp4 - 2 * hh2 : A₁ = B₁) hA1B1
          · refine absurd (hinj (a₁ := 1) (a₂ := 8) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp1 - hp2 - hp4 - 2 * hh2
          · have hd : (B₁ - A₂) + (B₁ - A₂) = 0 := by linear_combination hp0 - 2 * hp1 - 2 * hp2 - hp4 - 3 * hh2
            rcases hker _ hd with h0 | hh
            · exact absurd (by linear_combination h0 : B₁ = A₂) hB1A2
            · refine absurd (hinj (a₁ := 0) (a₂ := 5) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp1 - 2 * hp2 - hh - 3 * hh2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : A₂ + B₂ = A₃ + B₃) hg23
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : A₁ = B₃) hA1B3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : A₁ = A₃) hA1A3
        · refine absurd (hinj (a₁ := 1) (a₂ := 9) ?_) (by decide)
          simp only [chordStack]; linear_combination -2 * hp1 - hp2 - hp3 - 2 * hh2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - hh2 : A₂ + B₂ = A₃ + B₃) hg23
        · have hd : (A₁ - A₂) + (A₁ - A₂) = 0 := by linear_combination hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2
          rcases hker _ hd with h0 | hh
          · exact absurd (by linear_combination h0 : A₁ = A₂) hA1A2
          · refine absurd (hinj (a₁ := 0) (a₂ := 4) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp1 - 2 * hp2 - hh - 3 * hh2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - hh2 : B₁ = B₃) hB1B3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - hh2 : B₁ = A₃) hB1A3
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = B₃) hA2B3
    · -- continue: partner of 1 is 11
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₂ = B₂) hA2B2
      · refine absurd (hinj (a₁ := 1) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp0 - hp1 - hp2 - hh2 : B₂ = B₃) hB2B3
      · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · -- continue: partner of 2 is 6
        obtain ⟨y3, hp3⟩ := hclosed 4
        fin_cases y3 <;> simp only [chordStack] at hp3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = B₂) hA1B2
        · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp1 - 2 * hp2 - hp3 - 2 * hh2
        · refine absurd (hinj (a₁ := 0) (a₂ := 4) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 + hp3 - 2 * hh2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - 2 * hh2 : B₁ = A₁ + h) hna1
        · refine absurd (hinj (a₁ := 1) (a₂ := 9) ?_) (by decide)
          simp only [chordStack]; linear_combination -2 * hp1 - hp2 - hp3 - 2 * hh2
        · -- continue: partner of 4 is 7
          obtain ⟨y4, hp4⟩ := hclosed 5
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : B₁ = A₂) hB1A2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : B₁ = B₂) hB1B2
          · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp1 - 2 * hp2 - hp4 - 2 * hh2
          · refine absurd (hinj (a₁ := 0) (a₂ := 5) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 + hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 3 * hh2 : B₁ = A₁ + h) hna1
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp4 - 2 * hh2 : h = (0 : R)) hh0
          · refine absurd (hinj (a₁ := 1) (a₂ := 8) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp1 - hp2 - hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 + hp4 - 2 * hh2 : A₁ = B₁) hA1B1
          · have hd : (B₁ - A₂) + (B₁ - A₂) = 0 := by linear_combination hp0 - 2 * hp1 - 2 * hp2 - hp4 - 3 * hh2
            rcases hker _ hd with h0 | hh
            · exact absurd (by linear_combination h0 : B₁ = A₂) hB1A2
            · refine absurd (hinj (a₁ := 0) (a₂ := 5) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp1 - 2 * hp2 - hh - 3 * hh2
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : A₂ + B₂ = A₃ + B₃) hg23
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : A₁ = B₃) hA1B3
          · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp4 - hh2 : A₁ = A₃) hA1A3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - hh2 : A₂ + B₂ = A₃ + B₃) hg23
        · have hd : (A₁ - A₂) + (A₁ - A₂) = 0 := by linear_combination hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2
          rcases hker _ hd with h0 | hh
          · exact absurd (by linear_combination h0 : A₁ = A₂) hA1A2
          · refine absurd (hinj (a₁ := 0) (a₂ := 4) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp1 - 2 * hp2 - hh - 3 * hh2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - hh2 : B₁ = B₃) hB1B3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 + hp3 - hh2 : B₁ = A₃) hB1A3
      · exact absurd (by linear_combination -hp1 - hp2 - hh2 : A₃ = B₃) hA3B3
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = B₃) hA2B3
  · exact absurd (by linear_combination hp0 : A₁ = A₂) hA1A2
  · exact absurd (by linear_combination hp0 : B₁ = A₂) hB1A2
  · exact absurd (by linear_combination hp0 : B₂ = B₃) hB2B3
  · exact absurd (by linear_combination hp0 : B₂ = A₃) hB2A3
  · -- continue: partner of 0 is 8
    obtain ⟨y1, hp1⟩ := hclosed 1
    fin_cases y1 <;> simp only [chordStack] at hp1
    · exact absurd (by linear_combination -hp1 - hh2 : B₂ = A₂ + h) hna2
    · exact absurd (by linear_combination -hp1 : h = (0 : R)) hh0
    · -- continue: partner of 1 is 2
      obtain ⟨y2, hp2⟩ := hclosed 3
      fin_cases y2 <;> simp only [chordStack] at hp2
      · refine absurd (hinj (a₁ := 0) (a₂ := 5) ?_) (by decide)
        simp only [chordStack]; linear_combination hp0 + hp2 + hh2
      · exact absurd (by linear_combination hp1 + hp2 + hh2 : A₂ = B₂) hA2B2
      · exact absurd (by linear_combination -hp0 + hp1 - hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp0 + hp2 + hh2 : A₁ = B₁) hA1B1
      · -- continue: partner of 3 is 5
        obtain ⟨y3, hp3⟩ := hclosed 4
        fin_cases y3 <;> simp only [chordStack] at hp3
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = B₂) hA1B2
        · refine absurd (hinj (a₁ := 1) (a₂ := 4) ?_) (by decide)
          simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 + hp3 - 2 * hh2
        · exact absurd (by linear_combination -hp0 - 2 * hp2 - hp3 - 2 * hh2 : A₁ = B₁) hA1B1
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - 2 * hh2 : B₁ = A₁ + h) hna1
        · -- continue: partner of 4 is 6
          obtain ⟨y4, hp4⟩ := hclosed 7
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : B₂ = A₃) hB2A3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : A₂ = A₃) hA2A3
          · refine absurd (hinj (a₁ := 1) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 + hp4 - 2 * hh2
          · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp2 + hp4 - hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 + hp4 - hh2 : A₃ = B₃) hA3B3
          · refine absurd (hinj (a₁ := 0) (a₂ := 10) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp2 - hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : B₃ = A₃ + h) hna3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 2 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : A₁ = B₃) hA1B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : B₁ = B₃) hB1B3
          · have hd : (A₂ - A₃) + (A₂ - A₃) = 0 := by linear_combination -2 * hp0 + hp1 - 2 * hp2 - hp4 - 3 * hh2
            rcases hker _ hd with h0 | hh
            · exact absurd (by linear_combination h0 : A₂ = A₃) hA2A3
            · refine absurd (hinj (a₁ := 1) (a₂ := 7) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp2 - hh - 3 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : A₁ + B₁ = A₂ + B₂) hg12
        · -- continue: partner of 4 is 7
          obtain ⟨y4, hp4⟩ := hclosed 6
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : B₂ = B₃) hB2B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : A₂ = B₃) hA2B3
          · refine absurd (hinj (a₁ := 1) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 + hp4 - 2 * hh2
          · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp2 + hp4 - hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - hp4 - 3 * hh2 : A₃ = B₃) hA3B3
          · refine absurd (hinj (a₁ := 0) (a₂ := 11) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp2 - hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 2 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - 2 * hh2 : B₃ = A₃ + h) hna3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : A₁ = A₃) hA1A3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : B₁ = A₃) hB1A3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : A₁ + B₁ = A₂ + B₂) hg12
          · have hd : (A₂ - B₃) + (A₂ - B₃) = 0 := by linear_combination -2 * hp0 + hp1 - 2 * hp2 - hp4 - 3 * hh2
            rcases hker _ hd with h0 | hh
            · exact absurd (by linear_combination h0 : A₂ = B₃) hA2B3
            · refine absurd (hinj (a₁ := 1) (a₂ := 6) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp2 - hh - 3 * hh2
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - hh2 : A₂ + B₂ = A₃ + B₃) hg23
        · have hd : (A₁ - B₂) + (A₁ - B₂) = 0 := by linear_combination -2 * hp0 + hp1 - 2 * hp2 - hp3 - 3 * hh2
          rcases hker _ hd with h0 | hh
          · exact absurd (by linear_combination h0 : A₁ = B₂) hA1B2
          · refine absurd (hinj (a₁ := 1) (a₂ := 4) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp2 - hh - 3 * hh2
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - hh2 : B₁ = B₃) hB1B3
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - hh2 : B₁ = A₃) hB1A3
      · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp0 - hp2 - hh2
      · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp0 - hp2 - hh2
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = A₂) hB1A2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = A₂) hA1A2
      · exact absurd (by linear_combination -hp2 - hh2 : B₂ = A₃) hB2A3
      · exact absurd (by linear_combination -hp2 - hh2 : B₂ = B₃) hB2B3
    · exact absurd (by linear_combination hp1 : A₁ + B₁ = A₃ + B₃) hg13
    · exact absurd (by linear_combination hp1 : A₁ = B₂) hA1B2
    · exact absurd (by linear_combination hp1 : B₁ = B₂) hB1B2
    · exact absurd (by linear_combination hp1 : A₂ = B₃) hA2B3
    · exact absurd (by linear_combination hp1 : A₂ = A₃) hA2A3
    · exact absurd (by linear_combination -hp0 + hp1 : A₂ = B₂) hA2B2
    · -- continue: partner of 1 is 9
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination -hp0 - hp1 - 2 * hp2 - 3 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
      · refine absurd (hinj (a₁ := 1) (a₂ := 4) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination -hp0 + hp1 + hp2 : B₁ = A₁ + h) hna1
      · -- continue: partner of 2 is 4
        obtain ⟨y3, hp3⟩ := hclosed 3
        fin_cases y3 <;> simp only [chordStack] at hp3
        · refine absurd (hinj (a₁ := 0) (a₂ := 5) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination -hp0 - 2 * hp1 - hp2 - 2 * hp3 - 4 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
        · exact absurd (by linear_combination -hp0 - hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₁ + h) hna1
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · exact absurd (by linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2 : A₁ = B₁) hA1B1
        · -- continue: partner of 3 is 5
          obtain ⟨y4, hp4⟩ := hclosed 6
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : B₂ = B₃) hB2B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : A₂ = B₃) hA2B3
          · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 + hp4 - 3 * hh2
          · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 + hp4 - 3 * hh2
          · refine absurd (hinj (a₁ := 1) (a₂ := 11) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp4 - 4 * hh2
          · refine absurd (hinj (a₁ := 0) (a₂ := 11) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2 : B₃ = A₃ + h) hna3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₁ = A₃) hA1A3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : B₁ = A₃) hB1A3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
          · -- continue: partner of 6 is 11
            obtain ⟨y5, hp5⟩ := hclosed 7
            fin_cases y5 <;> simp only [chordStack] at hp5
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₂ = A₃) hB2A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : A₂ = A₃) hA2A3
            · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 + hp5 - 3 * hh2
            · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 + hp5 - 3 * hh2
            · refine absurd (hinj (a₁ := 1) (a₂ := 10) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp5 - 4 * hh2
            · refine absurd (hinj (a₁ := 0) (a₂ := 10) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp5 - 4 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₃ = A₃ + h) hna3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : h = (0 : R)) hh0
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ = B₃) hA1B3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : B₁ = B₃) hB1B3
            · have hd : (A₃ - B₃) + (A₃ - B₃) = 0 := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 + hp5 - 4 * hh2
              rcases hker _ hd with h0 | hh
              · exact absurd (by linear_combination h0 : A₃ = B₃) hA3B3
              · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hh - 5 * hh2 : B₃ = A₃ + h) hna3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 + hp5 - 4 * hh2 : A₃ = B₃) hA3B3
        · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2
        · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₂) hB1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₃) hB2A3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = B₃) hB2B3
      · exact absurd (by linear_combination -hp1 - hp2 - hh2 : A₁ = B₁) hA1B1
      · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp1 - hp2 - hh2
      · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp1 - hp2 - hh2
      · exact absurd (by linear_combination hp0 - hp1 - hp2 - hh2 : A₁ = A₂) hA1A2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = B₃) hA2B3
    · -- continue: partner of 1 is 10
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination hp0 + hp1 + hp2 + 2 * hh2 : A₁ = B₃) hA1B3
      · refine absurd (hinj (a₁ := 1) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp2 : B₂ = A₂ + h) hna2
      · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₂ = B₂) hA2B2
      · exact absurd (by linear_combination hp1 + hp2 + hh2 : A₃ = B₃) hA3B3
      · -- continue: partner of 2 is 7
        obtain ⟨y3, hp3⟩ := hclosed 3
        fin_cases y3 <;> simp only [chordStack] at hp3
        · refine absurd (hinj (a₁ := 0) (a₂ := 5) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination hp0 - hp1 - 2 * hp2 + hp3 : A₁ = B₃) hA1B3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₂ + h) hna2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · exact absurd (by linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2 : A₁ = B₁) hA1B1
        · -- continue: partner of 3 is 5
          obtain ⟨y4, hp4⟩ := hclosed 4
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : A₁ = A₂) hA1A2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : A₁ = B₂) hA1B2
          · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : A₁ = B₁) hA1B1
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2 : B₁ = A₁ + h) hna1
          · have s1 : B₂ + B₃ = A₁ + B₁ + h := by linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - 4 * hh2
            have s2 : A₃ + B₃ = A₁ + B₂ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - 4 * hh2
            have s3 : A₂ + B₂ = A₁ + B₃ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2
            exact Or.inl ⟨s1, s2, s3⟩
          · refine absurd (hinj (a₁ := 1) (a₂ := 9) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₂ + B₂ = A₃ + B₃) hg23
          · -- continue: partner of 4 is 9
            obtain ⟨y5, hp5⟩ := hclosed 6
            fin_cases y5 <;> simp only [chordStack] at hp5
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₂ = B₃) hB2B3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : A₂ = B₃) hA2B3
            · exact absurd (by linear_combination -2 * hp0 - hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : A₃ = B₃) hA3B3
            · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 + hp5 - 3 * hh2
            · refine absurd (hinj (a₁ := 4) (a₂ := 11) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 - 5 * hh2
            · refine absurd (hinj (a₁ := 0) (a₂ := 11) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp5 - 4 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : h = (0 : R)) hh0
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 4 * hh2 : B₃ = A₃ + h) hna3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ = A₃) hA1A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : B₁ = A₃) hB1A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
            · have hd : (B₁ - A₃) + (B₁ - A₃) = 0 := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 + hp5 - 2 * hh2
              rcases hker _ hd with h0 | hh
              · exact absurd (by linear_combination h0 : B₁ = A₃) hB1A3
              · refine absurd (hinj (a₁ := 4) (a₂ := 11) ?_) (by decide)
                simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 + hh - 5 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : B₁ = B₃) hB1B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : B₁ = A₃) hB1A3
        · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2
        · exact absurd (by linear_combination -hp1 - 2 * hp2 + hp3 - hh2 : A₂ = B₂) hA2B2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₂) hB1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -hp0 - hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = B₂) hB1B2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = B₃) hB2B3
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = B₃) hA2B3
    · -- continue: partner of 1 is 11
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination hp0 + hp1 + hp2 + 2 * hh2 : A₁ = A₃) hA1A3
      · refine absurd (hinj (a₁ := 1) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp2 : B₂ = A₂ + h) hna2
      · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₂ = B₂) hA2B2
      · -- continue: partner of 2 is 6
        obtain ⟨y3, hp3⟩ := hclosed 3
        fin_cases y3 <;> simp only [chordStack] at hp3
        · refine absurd (hinj (a₁ := 0) (a₂ := 5) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination hp0 - hp1 - 2 * hp2 + hp3 : A₁ = A₃) hA1A3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₂ + h) hna2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · exact absurd (by linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2 : A₁ = B₁) hA1B1
        · -- continue: partner of 3 is 5
          obtain ⟨y4, hp4⟩ := hclosed 4
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : A₁ = A₂) hA1A2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : A₁ = B₂) hA1B2
          · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : A₁ = B₁) hA1B1
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2 : B₁ = A₁ + h) hna1
          · refine absurd (hinj (a₁ := 1) (a₂ := 9) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp4 - 4 * hh2
          · have s1 : B₂ + A₃ = A₁ + B₁ + h := by linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - 4 * hh2
            have s2 : A₃ + B₃ = A₁ + B₂ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - 4 * hh2
            have s3 : A₂ + B₂ = A₁ + A₃ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2
            exact Or.inr (Or.inl ⟨s1, s2, s3⟩)
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₂ + B₂ = A₃ + B₃) hg23
          · -- continue: partner of 4 is 9
            obtain ⟨y5, hp5⟩ := hclosed 7
            fin_cases y5 <;> simp only [chordStack] at hp5
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₂ = A₃) hB2A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : A₂ = A₃) hA2A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₃ = B₃) hA3B3
            · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 + hp5 - 3 * hh2
            · refine absurd (hinj (a₁ := 4) (a₂ := 10) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 - 5 * hh2
            · refine absurd (hinj (a₁ := 0) (a₂ := 10) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp5 - 4 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₃ = A₃ + h) hna3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : h = (0 : R)) hh0
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ = B₃) hA1B3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : B₁ = B₃) hB1B3
            · have hd : (B₁ - B₃) + (B₁ - B₃) = 0 := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 + hp5 - 2 * hh2
              rcases hker _ hd with h0 | hh
              · exact absurd (by linear_combination h0 : B₁ = B₃) hB1B3
              · refine absurd (hinj (a₁ := 4) (a₂ := 10) ?_) (by decide)
                simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 + hh - 5 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : B₁ = B₃) hB1B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : B₁ = A₃) hB1A3
        · exact absurd (by linear_combination -hp1 - 2 * hp2 + hp3 - hh2 : A₂ = B₂) hA2B2
        · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₂) hB1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₃) hB2A3
        · exact absurd (by linear_combination -hp0 - hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp1 - hp2 - hh2 : A₃ = B₃) hA3B3
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = B₃) hA2B3
  · -- continue: partner of 0 is 9
    obtain ⟨y1, hp1⟩ := hclosed 1
    fin_cases y1 <;> simp only [chordStack] at hp1
    · exact absurd (by linear_combination -hp1 - hh2 : B₂ = A₂ + h) hna2
    · exact absurd (by linear_combination -hp1 : h = (0 : R)) hh0
    · -- continue: partner of 1 is 2
      obtain ⟨y2, hp2⟩ := hclosed 3
      fin_cases y2 <;> simp only [chordStack] at hp2
      · refine absurd (hinj (a₁ := 0) (a₂ := 4) ?_) (by decide)
        simp only [chordStack]; linear_combination hp0 + hp2 + hh2
      · exact absurd (by linear_combination hp1 + hp2 + hh2 : A₂ = B₂) hA2B2
      · exact absurd (by linear_combination -hp0 + hp1 - hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · -- continue: partner of 3 is 4
        obtain ⟨y3, hp3⟩ := hclosed 5
        fin_cases y3 <;> simp only [chordStack] at hp3
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₂) hB1A2
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = B₂) hB1B2
        · refine absurd (hinj (a₁ := 1) (a₂ := 5) ?_) (by decide)
          simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 + hp3 - 2 * hh2
        · exact absurd (by linear_combination -2 * hp0 - hp2 + hp3 - hh2 : A₁ = B₁) hA1B1
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₁ + h) hna1
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · -- continue: partner of 5 is 6
          obtain ⟨y4, hp4⟩ := hclosed 7
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : B₂ = A₃) hB2A3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : A₂ = A₃) hA2A3
          · refine absurd (hinj (a₁ := 1) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 + hp4 - 2 * hh2
          · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp2 + hp4 - hh2
          · refine absurd (hinj (a₁ := 0) (a₂ := 10) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp2 - hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 + hp4 - hh2 : A₃ = B₃) hA3B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : B₃ = A₃ + h) hna3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 2 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : A₁ = B₃) hA1B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : B₁ = B₃) hB1B3
          · have hd : (A₂ - A₃) + (A₂ - A₃) = 0 := by linear_combination -2 * hp0 + hp1 - 2 * hp2 - hp4 - 3 * hh2
            rcases hker _ hd with h0 | hh
            · exact absurd (by linear_combination h0 : A₂ = A₃) hA2A3
            · refine absurd (hinj (a₁ := 1) (a₂ := 7) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp2 - hh - 3 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : A₁ + B₁ = A₂ + B₂) hg12
        · -- continue: partner of 5 is 7
          obtain ⟨y4, hp4⟩ := hclosed 6
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : B₂ = B₃) hB2B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : A₂ = B₃) hA2B3
          · refine absurd (hinj (a₁ := 1) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 + hp4 - 2 * hh2
          · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp2 + hp4 - hh2
          · refine absurd (hinj (a₁ := 0) (a₂ := 11) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp2 - hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - hp4 - 3 * hh2 : A₃ = B₃) hA3B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 2 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - 2 * hh2 : B₃ = A₃ + h) hna3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : A₁ = A₃) hA1A3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : B₁ = A₃) hB1A3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : A₁ + B₁ = A₂ + B₂) hg12
          · have hd : (A₂ - B₃) + (A₂ - B₃) = 0 := by linear_combination -2 * hp0 + hp1 - 2 * hp2 - hp4 - 3 * hh2
            rcases hker _ hd with h0 | hh
            · exact absurd (by linear_combination h0 : A₂ = B₃) hA2B3
            · refine absurd (hinj (a₁ := 1) (a₂ := 6) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp2 - hh - 3 * hh2
        · have hd : (B₁ - B₂) + (B₁ - B₂) = 0 := by linear_combination -2 * hp0 + hp1 - 2 * hp2 - hp3 - 3 * hh2
          rcases hker _ hd with h0 | hh
          · exact absurd (by linear_combination h0 : B₁ = B₂) hB1B2
          · refine absurd (hinj (a₁ := 1) (a₂ := 5) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp2 - hh - 3 * hh2
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - hh2 : A₂ + B₂ = A₃ + B₃) hg23
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - hh2 : A₁ = B₃) hA1B3
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - hh2 : A₁ = A₃) hA1A3
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₁ = B₁) hA1B1
      · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp0 - hp2 - hh2
      · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp0 - hp2 - hh2
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = A₂) hB1A2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = A₂) hA1A2
      · exact absurd (by linear_combination -hp2 - hh2 : B₂ = A₃) hB2A3
      · exact absurd (by linear_combination -hp2 - hh2 : B₂ = B₃) hB2B3
    · exact absurd (by linear_combination hp1 : A₁ + B₁ = A₃ + B₃) hg13
    · exact absurd (by linear_combination hp1 : A₁ = B₂) hA1B2
    · exact absurd (by linear_combination hp1 : B₁ = B₂) hB1B2
    · exact absurd (by linear_combination hp1 : A₂ = B₃) hA2B3
    · exact absurd (by linear_combination hp1 : A₂ = A₃) hA2A3
    · -- continue: partner of 1 is 8
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination -hp0 - hp1 - 2 * hp2 - 3 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
      · refine absurd (hinj (a₁ := 1) (a₂ := 5) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp0 - hp1 - hp2 - hh2 : B₁ = A₁ + h) hna1
      · exact absurd (by linear_combination hp1 + hp2 + hh2 : A₁ = B₁) hA1B1
      · -- continue: partner of 2 is 5
        obtain ⟨y3, hp3⟩ := hclosed 3
        fin_cases y3 <;> simp only [chordStack] at hp3
        · refine absurd (hinj (a₁ := 0) (a₂ := 4) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination -hp0 - 2 * hp1 - hp2 - 2 * hp3 - 4 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
        · exact absurd (by linear_combination hp0 - 2 * hp1 - hp2 + hp3 - hh2 : B₁ = A₁ + h) hna1
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · -- continue: partner of 3 is 4
          obtain ⟨y4, hp4⟩ := hclosed 6
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : B₂ = B₃) hB2B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : A₂ = B₃) hA2B3
          · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 + hp4 - 3 * hh2
          · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 + hp4 - 3 * hh2
          · refine absurd (hinj (a₁ := 0) (a₂ := 11) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp4 - 4 * hh2
          · refine absurd (hinj (a₁ := 1) (a₂ := 11) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2 : B₃ = A₃ + h) hna3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₁ = A₃) hA1A3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : B₁ = A₃) hB1A3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
          · -- continue: partner of 6 is 11
            obtain ⟨y5, hp5⟩ := hclosed 7
            fin_cases y5 <;> simp only [chordStack] at hp5
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₂ = A₃) hB2A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : A₂ = A₃) hA2A3
            · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 + hp5 - 3 * hh2
            · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 + hp5 - 3 * hh2
            · refine absurd (hinj (a₁ := 0) (a₂ := 10) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp5 - 4 * hh2
            · refine absurd (hinj (a₁ := 1) (a₂ := 10) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp5 - 4 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₃ = A₃ + h) hna3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : h = (0 : R)) hh0
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ = B₃) hA1B3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : B₁ = B₃) hB1B3
            · have hd : (A₃ - B₃) + (A₃ - B₃) = 0 := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 + hp5 - 4 * hh2
              rcases hker _ hd with h0 | hh
              · exact absurd (by linear_combination h0 : A₃ = B₃) hA3B3
              · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hh - 5 * hh2 : B₃ = A₃ + h) hna3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 + hp5 - 4 * hh2 : A₃ = B₃) hA3B3
        · exact absurd (by linear_combination -hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = B₁) hA1B1
        · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2
        · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2
        · exact absurd (by linear_combination -hp0 - hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = B₂) hA1B2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₃) hB2A3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = B₃) hB2B3
      · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp1 - hp2 - hh2
      · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp1 - hp2 - hh2
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = B₃) hA2B3
    · exact absurd (by linear_combination -hp0 + hp1 : A₂ = B₂) hA2B2
    · -- continue: partner of 1 is 10
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination -hp0 - hp1 - 2 * hp2 - 3 * hh2 : A₁ = A₃) hA1A3
      · refine absurd (hinj (a₁ := 1) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp2 : B₂ = A₂ + h) hna2
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₂ = B₂) hA2B2
      · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination hp1 + hp2 + hh2 : A₃ = B₃) hA3B3
      · -- continue: partner of 2 is 7
        obtain ⟨y3, hp3⟩ := hclosed 3
        fin_cases y3 <;> simp only [chordStack] at hp3
        · refine absurd (hinj (a₁ := 0) (a₂ := 4) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination -hp0 - 2 * hp1 - hp2 - 2 * hp3 - 4 * hh2 : A₁ = A₃) hA1A3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₂ + h) hna2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · -- continue: partner of 3 is 4
          obtain ⟨y4, hp4⟩ := hclosed 5
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : B₁ = A₂) hB1A2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : B₁ = B₂) hB1B2
          · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 + hp4 - 3 * hh2 : A₁ = B₁) hA1B1
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : B₁ = A₁ + h) hna1
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : h = (0 : R)) hh0
          · have s1 : B₂ + B₃ = A₁ + B₁ + h := by linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - 4 * hh2
            have s2 : A₃ + B₃ = B₁ + B₂ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - 4 * hh2
            have s3 : A₂ + B₂ = B₁ + B₃ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2
            exact Or.inr (Or.inr (Or.inl ⟨s1, s2, s3⟩))
          · refine absurd (hinj (a₁ := 1) (a₂ := 8) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp4 - 4 * hh2
          · -- continue: partner of 5 is 8
            obtain ⟨y5, hp5⟩ := hclosed 6
            fin_cases y5 <;> simp only [chordStack] at hp5
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₂ = B₃) hB2B3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : A₂ = B₃) hA2B3
            · exact absurd (by linear_combination -2 * hp0 - hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : A₃ = B₃) hA3B3
            · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 + hp5 - 3 * hh2
            · refine absurd (hinj (a₁ := 0) (a₂ := 11) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp5 - 4 * hh2
            · refine absurd (hinj (a₁ := 5) (a₂ := 11) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 - 5 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : h = (0 : R)) hh0
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 4 * hh2 : B₃ = A₃ + h) hna3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ = A₃) hA1A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : B₁ = A₃) hB1A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
            · have hd : (A₁ - A₃) + (A₁ - A₃) = 0 := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 + hp5 - 2 * hh2
              rcases hker _ hd with h0 | hh
              · exact absurd (by linear_combination h0 : A₁ = A₃) hA1A3
              · refine absurd (hinj (a₁ := 5) (a₂ := 11) ?_) (by decide)
                simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 + hh - 5 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₂ + B₂ = A₃ + B₃) hg23
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₁ = B₃) hA1B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₁ = A₃) hA1A3
        · exact absurd (by linear_combination -hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = B₁) hA1B1
        · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2
        · exact absurd (by linear_combination -hp1 - 2 * hp2 + hp3 - hh2 : A₂ = B₂) hA2B2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₂) hB1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -hp0 - hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = B₂) hA1B2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = B₃) hB2B3
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = B₃) hA2B3
    · -- continue: partner of 1 is 11
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination -hp0 - hp1 - 2 * hp2 - 3 * hh2 : A₁ = B₃) hA1B3
      · refine absurd (hinj (a₁ := 1) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp2 : B₂ = A₂ + h) hna2
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₂ = B₂) hA2B2
      · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · -- continue: partner of 2 is 6
        obtain ⟨y3, hp3⟩ := hclosed 3
        fin_cases y3 <;> simp only [chordStack] at hp3
        · refine absurd (hinj (a₁ := 0) (a₂ := 4) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination -hp0 - 2 * hp1 - hp2 - 2 * hp3 - 4 * hh2 : A₁ = B₃) hA1B3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₂ + h) hna2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · -- continue: partner of 3 is 4
          obtain ⟨y4, hp4⟩ := hclosed 5
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : B₁ = A₂) hB1A2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : B₁ = B₂) hB1B2
          · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 + hp4 - 3 * hh2 : A₁ = B₁) hA1B1
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : B₁ = A₁ + h) hna1
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : h = (0 : R)) hh0
          · refine absurd (hinj (a₁ := 1) (a₂ := 8) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp4 - 4 * hh2
          · have s1 : B₂ + A₃ = A₁ + B₁ + h := by linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - 4 * hh2
            have s2 : A₃ + B₃ = B₁ + B₂ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - 4 * hh2
            have s3 : A₂ + B₂ = B₁ + A₃ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s1, s2, s3⟩)))
          · -- continue: partner of 5 is 8
            obtain ⟨y5, hp5⟩ := hclosed 7
            fin_cases y5 <;> simp only [chordStack] at hp5
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₂ = A₃) hB2A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : A₂ = A₃) hA2A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₃ = B₃) hA3B3
            · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 + hp5 - 3 * hh2
            · refine absurd (hinj (a₁ := 0) (a₂ := 10) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp5 - 4 * hh2
            · refine absurd (hinj (a₁ := 5) (a₂ := 10) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 - 5 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₃ = A₃ + h) hna3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : h = (0 : R)) hh0
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ = B₃) hA1B3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : B₁ = B₃) hB1B3
            · have hd : (A₁ - B₃) + (A₁ - B₃) = 0 := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 + hp5 - 2 * hh2
              rcases hker _ hd with h0 | hh
              · exact absurd (by linear_combination h0 : A₁ = B₃) hA1B3
              · refine absurd (hinj (a₁ := 5) (a₂ := 10) ?_) (by decide)
                simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 + hh - 5 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₂ + B₂ = A₃ + B₃) hg23
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₁ = B₃) hA1B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₁ = A₃) hA1A3
        · exact absurd (by linear_combination -hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = B₁) hA1B1
        · exact absurd (by linear_combination -hp1 - 2 * hp2 + hp3 - hh2 : A₂ = B₂) hA2B2
        · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₂) hB1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₃) hB2A3
        · exact absurd (by linear_combination -hp0 - hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp1 - hp2 - hh2 : A₃ = B₃) hA3B3
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = B₃) hA2B3
  · -- continue: partner of 0 is 10
    obtain ⟨y1, hp1⟩ := hclosed 1
    fin_cases y1 <;> simp only [chordStack] at hp1
    · exact absurd (by linear_combination -hp1 - hh2 : B₂ = A₂ + h) hna2
    · exact absurd (by linear_combination -hp1 : h = (0 : R)) hh0
    · -- continue: partner of 1 is 2
      obtain ⟨y2, hp2⟩ := hclosed 3
      fin_cases y2 <;> simp only [chordStack] at hp2
      · refine absurd (hinj (a₁ := 0) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hp0 + hp2 + hh2
      · exact absurd (by linear_combination hp1 + hp2 + hh2 : A₂ = B₂) hA2B2
      · exact absurd (by linear_combination -hp0 + hp1 - hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hp0 + hp2 + hh2
      · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hp0 + hp2 + hh2
      · exact absurd (by linear_combination hp0 + hp2 + hh2 : A₃ = B₃) hA3B3
      · -- continue: partner of 3 is 7
        obtain ⟨y3, hp3⟩ := hclosed 4
        fin_cases y3 <;> simp only [chordStack] at hp3
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = B₂) hA1B2
        · refine absurd (hinj (a₁ := 1) (a₂ := 4) ?_) (by decide)
          simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 + hp3 - 2 * hh2
        · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp0 - 2 * hp2 - hp3 - 2 * hh2
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - 2 * hh2 : B₁ = A₁ + h) hna1
        · -- continue: partner of 4 is 6
          obtain ⟨y4, hp4⟩ := hclosed 5
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : B₁ = A₂) hB1A2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : B₁ = B₂) hB1B2
          · refine absurd (hinj (a₁ := 1) (a₂ := 5) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 + hp4 - 2 * hh2
          · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp0 - 2 * hp2 - hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : B₁ = A₁ + h) hna1
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 2 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 + hp4 - 2 * hh2 : A₁ = B₁) hA1B1
          · refine absurd (hinj (a₁ := 0) (a₂ := 8) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp2 - hp4 - 2 * hh2
          · have hd : (B₁ - B₂) + (B₁ - B₂) = 0 := by linear_combination -2 * hp0 + hp1 - 2 * hp2 - hp4 - 3 * hh2
            rcases hker _ hd with h0 | hh
            · exact absurd (by linear_combination h0 : B₁ = B₂) hB1B2
            · refine absurd (hinj (a₁ := 1) (a₂ := 5) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp2 - hh - 3 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : A₂ + B₂ = A₃ + B₃) hg23
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : A₁ = B₃) hA1B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : A₁ = A₃) hA1A3
        · refine absurd (hinj (a₁ := 0) (a₂ := 9) ?_) (by decide)
          simp only [chordStack]; linear_combination -2 * hp0 - hp2 - hp3 - 2 * hh2
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - hh2 : A₂ + B₂ = A₃ + B₃) hg23
        · have hd : (A₁ - B₂) + (A₁ - B₂) = 0 := by linear_combination -2 * hp0 + hp1 - 2 * hp2 - hp3 - 3 * hh2
          rcases hker _ hd with h0 | hh
          · exact absurd (by linear_combination h0 : A₁ = B₂) hA1B2
          · refine absurd (hinj (a₁ := 1) (a₂ := 4) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp2 - hh - 3 * hh2
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - hh2 : B₁ = B₃) hB1B3
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - hh2 : B₁ = A₃) hB1A3
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = A₂) hB1A2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = A₂) hA1A2
      · exact absurd (by linear_combination -hp2 - hh2 : B₂ = A₃) hB2A3
      · exact absurd (by linear_combination -hp2 - hh2 : B₂ = B₃) hB2B3
    · exact absurd (by linear_combination hp1 : A₁ + B₁ = A₃ + B₃) hg13
    · exact absurd (by linear_combination hp1 : A₁ = B₂) hA1B2
    · exact absurd (by linear_combination hp1 : B₁ = B₂) hB1B2
    · exact absurd (by linear_combination hp1 : A₂ = B₃) hA2B3
    · exact absurd (by linear_combination hp1 : A₂ = A₃) hA2A3
    · -- continue: partner of 1 is 8
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination hp0 + hp1 + hp2 + 2 * hh2 : A₁ = B₃) hA1B3
      · refine absurd (hinj (a₁ := 1) (a₂ := 5) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp2 : B₂ = A₂ + h) hna2
      · exact absurd (by linear_combination hp1 + hp2 + hh2 : A₁ = B₁) hA1B1
      · -- continue: partner of 2 is 5
        obtain ⟨y3, hp3⟩ := hclosed 3
        fin_cases y3 <;> simp only [chordStack] at hp3
        · refine absurd (hinj (a₁ := 0) (a₂ := 7) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination hp0 - hp1 - 2 * hp2 + hp3 : A₁ = B₃) hA1B3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₂ + h) hna2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination -hp1 - 2 * hp2 + hp3 - hh2 : A₂ = B₂) hA2B2
        · exact absurd (by linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2 : A₃ = B₃) hA3B3
        · -- continue: partner of 3 is 7
          obtain ⟨y4, hp4⟩ := hclosed 4
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : A₁ = A₂) hA1A2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : A₁ = B₂) hA1B2
          · exact absurd (by linear_combination -2 * hp0 - hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : A₁ = B₁) hA1B1
          · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2 : B₁ = A₁ + h) hna1
          · have s1 : A₂ + B₃ = A₁ + B₁ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - 4 * hh2
            have s2 : A₃ + B₃ = A₁ + A₂ + h := by linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - 4 * hh2
            have s3 : A₂ + B₂ = A₁ + B₃ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s1, s2, s3⟩))))
          · refine absurd (hinj (a₁ := 0) (a₂ := 9) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₂ + B₂ = A₃ + B₃) hg23
          · -- continue: partner of 4 is 9
            obtain ⟨y5, hp5⟩ := hclosed 6
            fin_cases y5 <;> simp only [chordStack] at hp5
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₂ = B₃) hB2B3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : A₂ = B₃) hA2B3
            · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 + hp5 - 3 * hh2
            · exact absurd (by linear_combination -hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : A₃ = B₃) hA3B3
            · refine absurd (hinj (a₁ := 4) (a₂ := 11) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 - 5 * hh2
            · refine absurd (hinj (a₁ := 1) (a₂ := 11) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp5 - 4 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : h = (0 : R)) hh0
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 4 * hh2 : B₃ = A₃ + h) hna3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ = A₃) hA1A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : B₁ = A₃) hB1A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
            · have hd : (B₁ - A₃) + (B₁ - A₃) = 0 := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 + hp5 - 2 * hh2
              rcases hker _ hd with h0 | hh
              · exact absurd (by linear_combination h0 : B₁ = A₃) hB1A3
              · refine absurd (hinj (a₁ := 4) (a₂ := 11) ?_) (by decide)
                simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 + hh - 5 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : B₁ = B₃) hB1B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : B₁ = A₃) hB1A3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₂) hB1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₃) hB2A3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = B₃) hB2B3
      · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp1 - hp2 - hh2
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₂ = B₂) hA2B2
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination hp0 - hp1 - hp2 - hh2 : B₁ = A₂) hB1A2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = B₃) hA2B3
    · -- continue: partner of 1 is 9
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination -hp0 - hp1 - 2 * hp2 - 3 * hh2 : A₁ = A₃) hA1A3
      · refine absurd (hinj (a₁ := 1) (a₂ := 4) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp2 : B₂ = A₂ + h) hna2
      · -- continue: partner of 2 is 4
        obtain ⟨y3, hp3⟩ := hclosed 3
        fin_cases y3 <;> simp only [chordStack] at hp3
        · refine absurd (hinj (a₁ := 0) (a₂ := 7) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination -hp0 - 2 * hp1 - hp2 - 2 * hp3 - 4 * hh2 : A₁ = A₃) hA1A3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₂ + h) hna2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · exact absurd (by linear_combination -hp1 - 2 * hp2 + hp3 - hh2 : A₂ = B₂) hA2B2
        · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2 : A₃ = B₃) hA3B3
        · -- continue: partner of 3 is 7
          obtain ⟨y4, hp4⟩ := hclosed 5
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : B₁ = A₂) hB1A2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : B₁ = B₂) hB1B2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₁ = B₁) hA1B1
          · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : B₁ = A₁ + h) hna1
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : h = (0 : R)) hh0
          · have s1 : A₂ + B₃ = A₁ + B₁ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - 4 * hh2
            have s2 : A₃ + B₃ = B₁ + A₂ + h := by linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - 4 * hh2
            have s3 : A₂ + B₂ = B₁ + B₃ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s1, s2, s3⟩)))))
          · refine absurd (hinj (a₁ := 0) (a₂ := 8) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp4 - 4 * hh2
          · -- continue: partner of 5 is 8
            obtain ⟨y5, hp5⟩ := hclosed 6
            fin_cases y5 <;> simp only [chordStack] at hp5
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₂ = B₃) hB2B3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : A₂ = B₃) hA2B3
            · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 + hp5 - 3 * hh2
            · exact absurd (by linear_combination -hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : A₃ = B₃) hA3B3
            · refine absurd (hinj (a₁ := 1) (a₂ := 11) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp5 - 4 * hh2
            · refine absurd (hinj (a₁ := 5) (a₂ := 11) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 - 5 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : h = (0 : R)) hh0
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 4 * hh2 : B₃ = A₃ + h) hna3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ = A₃) hA1A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : B₁ = A₃) hB1A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
            · have hd : (A₁ - A₃) + (A₁ - A₃) = 0 := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 + hp5 - 2 * hh2
              rcases hker _ hd with h0 | hh
              · exact absurd (by linear_combination h0 : A₁ = A₃) hA1A3
              · refine absurd (hinj (a₁ := 5) (a₂ := 11) ?_) (by decide)
                simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 + hh - 5 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₂ + B₂ = A₃ + B₃) hg23
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₁ = B₃) hA1B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₁ = A₃) hA1A3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₂) hB1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₃) hB2A3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = B₃) hB2B3
      · exact absurd (by linear_combination -hp1 - hp2 - hh2 : A₁ = B₁) hA1B1
      · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp1 - hp2 - hh2
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₂ = B₂) hA2B2
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination hp0 - hp1 - hp2 - hh2 : A₁ = A₂) hA1A2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = B₃) hA2B3
    · exact absurd (by linear_combination -hp0 + hp1 : A₂ = B₂) hA2B2
    · -- continue: partner of 1 is 11
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination hp0 + hp1 + hp2 + 2 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
      · refine absurd (hinj (a₁ := 1) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp2 : B₂ = A₂ + h) hna2
      · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · -- continue: partner of 2 is 6
        obtain ⟨y3, hp3⟩ := hclosed 3
        fin_cases y3 <;> simp only [chordStack] at hp3
        · refine absurd (hinj (a₁ := 0) (a₂ := 7) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination hp0 - hp1 - 2 * hp2 + hp3 : A₁ + B₁ = A₂ + B₂) hg12
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₂ + h) hna2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination -hp1 - 2 * hp2 + hp3 - hh2 : A₂ = B₂) hA2B2
        · -- continue: partner of 3 is 7
          obtain ⟨y4, hp4⟩ := hclosed 4
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : A₁ = A₂) hA1A2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : A₁ = B₂) hA1B2
          · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2
          · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2 : B₁ = A₁ + h) hna1
          · refine absurd (hinj (a₁ := 1) (a₂ := 9) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp4 - 4 * hh2
          · refine absurd (hinj (a₁ := 0) (a₂ := 9) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₂ + B₂ = A₃ + B₃) hg23
          · -- continue: partner of 4 is 9
            obtain ⟨y5, hp5⟩ := hclosed 5
            fin_cases y5 <;> simp only [chordStack] at hp5
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₁ = A₂) hB1A2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₁ = B₂) hB1B2
            · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2
            · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
              simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₁ = A₁ + h) hna1
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : h = (0 : R)) hh0
            · refine absurd (hinj (a₁ := 1) (a₂ := 8) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp5 - 4 * hh2
            · refine absurd (hinj (a₁ := 0) (a₂ := 8) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp5 - 4 * hh2
            · have hd : (A₁ - B₁) + (A₁ - B₁) = 0 := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 + hp5 - 4 * hh2
              rcases hker _ hd with h0 | hh
              · exact absurd (by linear_combination h0 : A₁ = B₁) hA1B1
              · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hh - 5 * hh2 : B₁ = A₁ + h) hna1
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 + hp5 - 4 * hh2 : A₁ = B₁) hA1B1
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ = B₃) hA1B3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ = A₃) hA1A3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : B₁ = B₃) hB1B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : B₁ = A₃) hB1A3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₂) hB1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₃) hB2A3
        · exact absurd (by linear_combination -hp0 - hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₂ = B₂) hA2B2
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = B₃) hA2B3
  · -- continue: partner of 0 is 11
    obtain ⟨y1, hp1⟩ := hclosed 1
    fin_cases y1 <;> simp only [chordStack] at hp1
    · exact absurd (by linear_combination -hp1 - hh2 : B₂ = A₂ + h) hna2
    · exact absurd (by linear_combination -hp1 : h = (0 : R)) hh0
    · -- continue: partner of 1 is 2
      obtain ⟨y2, hp2⟩ := hclosed 3
      fin_cases y2 <;> simp only [chordStack] at hp2
      · refine absurd (hinj (a₁ := 0) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hp0 + hp2 + hh2
      · exact absurd (by linear_combination hp1 + hp2 + hh2 : A₂ = B₂) hA2B2
      · exact absurd (by linear_combination -hp0 + hp1 - hp2 - hh2 : A₂ = B₃) hA2B3
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hp0 + hp2 + hh2
      · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hp0 + hp2 + hh2
      · -- continue: partner of 3 is 6
        obtain ⟨y3, hp3⟩ := hclosed 4
        fin_cases y3 <;> simp only [chordStack] at hp3
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = B₂) hA1B2
        · refine absurd (hinj (a₁ := 1) (a₂ := 4) ?_) (by decide)
          simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 + hp3 - 2 * hh2
        · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
          simp only [chordStack]; linear_combination -hp0 - 2 * hp2 - hp3 - 2 * hh2
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - 2 * hh2 : B₁ = A₁ + h) hna1
        · refine absurd (hinj (a₁ := 0) (a₂ := 9) ?_) (by decide)
          simp only [chordStack]; linear_combination -2 * hp0 - hp2 - hp3 - 2 * hh2
        · -- continue: partner of 4 is 7
          obtain ⟨y4, hp4⟩ := hclosed 5
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : B₁ = A₂) hB1A2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : B₁ = B₂) hB1B2
          · refine absurd (hinj (a₁ := 1) (a₂ := 5) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 + hp4 - 2 * hh2
          · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp0 - 2 * hp2 - hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 3 * hh2 : B₁ = A₁ + h) hna1
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp4 - 2 * hh2 : h = (0 : R)) hh0
          · refine absurd (hinj (a₁ := 0) (a₂ := 8) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp2 - hp4 - 2 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 - hp3 + hp4 - 2 * hh2 : A₁ = B₁) hA1B1
          · have hd : (B₁ - B₂) + (B₁ - B₂) = 0 := by linear_combination -2 * hp0 + hp1 - 2 * hp2 - hp4 - 3 * hh2
            rcases hker _ hd with h0 | hh
            · exact absurd (by linear_combination h0 : B₁ = B₂) hB1B2
            · refine absurd (hinj (a₁ := 1) (a₂ := 5) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp2 - hh - 3 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : A₂ + B₂ = A₃ + B₃) hg23
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : A₁ = B₃) hA1B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp4 - hh2 : A₁ = A₃) hA1A3
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - hh2 : A₂ + B₂ = A₃ + B₃) hg23
        · have hd : (A₁ - B₂) + (A₁ - B₂) = 0 := by linear_combination -2 * hp0 + hp1 - 2 * hp2 - hp3 - 3 * hh2
          rcases hker _ hd with h0 | hh
          · exact absurd (by linear_combination h0 : A₁ = B₂) hA1B2
          · refine absurd (hinj (a₁ := 1) (a₂ := 4) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp2 - hh - 3 * hh2
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - hh2 : B₁ = B₃) hB1B3
        · exact absurd (by linear_combination -2 * hp0 - 2 * hp2 + hp3 - hh2 : B₁ = A₃) hB1A3
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₃ = B₃) hA3B3
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = A₂) hB1A2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = A₂) hA1A2
      · exact absurd (by linear_combination -hp2 - hh2 : B₂ = A₃) hB2A3
      · exact absurd (by linear_combination -hp2 - hh2 : B₂ = B₃) hB2B3
    · exact absurd (by linear_combination hp1 : A₁ + B₁ = A₃ + B₃) hg13
    · exact absurd (by linear_combination hp1 : A₁ = B₂) hA1B2
    · exact absurd (by linear_combination hp1 : B₁ = B₂) hB1B2
    · exact absurd (by linear_combination hp1 : A₂ = B₃) hA2B3
    · exact absurd (by linear_combination hp1 : A₂ = A₃) hA2A3
    · -- continue: partner of 1 is 8
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination hp0 + hp1 + hp2 + 2 * hh2 : A₁ = A₃) hA1A3
      · refine absurd (hinj (a₁ := 1) (a₂ := 5) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp2 : B₂ = A₂ + h) hna2
      · exact absurd (by linear_combination hp1 + hp2 + hh2 : A₁ = B₁) hA1B1
      · -- continue: partner of 2 is 5
        obtain ⟨y3, hp3⟩ := hclosed 3
        fin_cases y3 <;> simp only [chordStack] at hp3
        · refine absurd (hinj (a₁ := 0) (a₂ := 6) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination hp0 - hp1 - 2 * hp2 + hp3 : A₁ = A₃) hA1A3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₂ + h) hna2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination -hp1 - 2 * hp2 + hp3 - hh2 : A₂ = B₂) hA2B2
        · -- continue: partner of 3 is 6
          obtain ⟨y4, hp4⟩ := hclosed 4
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : A₁ = A₂) hA1A2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : A₁ = B₂) hA1B2
          · exact absurd (by linear_combination -2 * hp0 - hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : A₁ = B₁) hA1B1
          · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2 : B₁ = A₁ + h) hna1
          · refine absurd (hinj (a₁ := 0) (a₂ := 9) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp4 - 4 * hh2
          · have s1 : A₂ + A₃ = A₁ + B₁ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - 4 * hh2
            have s2 : A₃ + B₃ = A₁ + A₂ + h := by linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - 4 * hh2
            have s3 : A₂ + B₂ = A₁ + A₃ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s1, s2, s3⟩))))))
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₂ + B₂ = A₃ + B₃) hg23
          · -- continue: partner of 4 is 9
            obtain ⟨y5, hp5⟩ := hclosed 7
            fin_cases y5 <;> simp only [chordStack] at hp5
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₂ = A₃) hB2A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : A₂ = A₃) hA2A3
            · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 + hp5 - 3 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 + hp5 - 3 * hh2 : A₃ = B₃) hA3B3
            · refine absurd (hinj (a₁ := 4) (a₂ := 10) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 - 5 * hh2
            · refine absurd (hinj (a₁ := 1) (a₂ := 10) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp5 - 4 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₃ = A₃ + h) hna3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : h = (0 : R)) hh0
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ = B₃) hA1B3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : B₁ = B₃) hB1B3
            · have hd : (B₁ - B₃) + (B₁ - B₃) = 0 := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 + hp5 - 2 * hh2
              rcases hker _ hd with h0 | hh
              · exact absurd (by linear_combination h0 : B₁ = B₃) hB1B3
              · refine absurd (hinj (a₁ := 4) (a₂ := 10) ?_) (by decide)
                simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 + hh - 5 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : B₁ = B₃) hB1B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : B₁ = A₃) hB1A3
        · exact absurd (by linear_combination -hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₃ = B₃) hA3B3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₂) hB1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₃) hB2A3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = B₃) hB2B3
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₂ = B₂) hA2B2
      · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp1 - hp2 - hh2
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination hp0 - hp1 - hp2 - hh2 : B₁ = A₂) hB1A2
    · -- continue: partner of 1 is 9
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination -hp0 - hp1 - 2 * hp2 - 3 * hh2 : A₁ = B₃) hA1B3
      · refine absurd (hinj (a₁ := 1) (a₂ := 4) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp2 : B₂ = A₂ + h) hna2
      · -- continue: partner of 2 is 4
        obtain ⟨y3, hp3⟩ := hclosed 3
        fin_cases y3 <;> simp only [chordStack] at hp3
        · refine absurd (hinj (a₁ := 0) (a₂ := 6) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination -hp0 - 2 * hp1 - hp2 - 2 * hp3 - 4 * hh2 : A₁ = B₃) hA1B3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₂ + h) hna2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · exact absurd (by linear_combination -hp1 - 2 * hp2 + hp3 - hh2 : A₂ = B₂) hA2B2
        · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · -- continue: partner of 3 is 6
          obtain ⟨y4, hp4⟩ := hclosed 5
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : B₁ = A₂) hB1A2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : B₁ = B₂) hB1B2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₁ = B₁) hA1B1
          · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : B₁ = A₁ + h) hna1
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : h = (0 : R)) hh0
          · refine absurd (hinj (a₁ := 0) (a₂ := 8) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp4 - 4 * hh2
          · have s1 : A₂ + A₃ = A₁ + B₁ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - 4 * hh2
            have s2 : A₃ + B₃ = B₁ + A₂ + h := by linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - 4 * hh2
            have s3 : A₂ + B₂ = B₁ + A₃ + h := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨s1, s2, s3⟩)))))))
          · -- continue: partner of 5 is 8
            obtain ⟨y5, hp5⟩ := hclosed 7
            fin_cases y5 <;> simp only [chordStack] at hp5
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₂ = A₃) hB2A3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : A₂ = A₃) hA2A3
            · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 + hp5 - 3 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 + hp5 - 3 * hh2 : A₃ = B₃) hA3B3
            · refine absurd (hinj (a₁ := 1) (a₂ := 10) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp5 - 4 * hh2
            · refine absurd (hinj (a₁ := 5) (a₂ := 10) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 - 5 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₃ = A₃ + h) hna3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : h = (0 : R)) hh0
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ = B₃) hA1B3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : B₁ = B₃) hB1B3
            · have hd : (A₁ - B₃) + (A₁ - B₃) = 0 := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 + hp5 - 2 * hh2
              rcases hker _ hd with h0 | hh
              · exact absurd (by linear_combination h0 : A₁ = B₃) hA1B3
              · refine absurd (hinj (a₁ := 5) (a₂ := 10) ?_) (by decide)
                simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - hp5 + hh - 5 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₂ + B₂ = A₃ + B₃) hg23
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₁ = B₃) hA1B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₁ = A₃) hA1A3
        · exact absurd (by linear_combination -hp0 - 2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₃ = B₃) hA3B3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₂) hB1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₃) hB2A3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = B₃) hB2B3
      · exact absurd (by linear_combination -hp1 - hp2 - hh2 : A₁ = B₁) hA1B1
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₂ = B₂) hA2B2
      · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination -hp1 - hp2 - hh2
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination hp0 - hp1 - hp2 - hh2 : A₁ = A₂) hA1A2
    · -- continue: partner of 1 is 10
      obtain ⟨y2, hp2⟩ := hclosed 2
      fin_cases y2 <;> simp only [chordStack] at hp2
      · exact absurd (by linear_combination hp0 + hp1 + hp2 + 2 * hh2 : A₁ + B₁ = A₂ + B₂) hg12
      · refine absurd (hinj (a₁ := 1) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp2 : h = (0 : R)) hh0
      · exact absurd (by linear_combination hp2 : B₂ = A₂ + h) hna2
      · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hp1 + hp2 + hh2
      · exact absurd (by linear_combination -hp0 - hp2 - hh2 : A₂ = B₂) hA2B2
      · -- continue: partner of 2 is 7
        obtain ⟨y3, hp3⟩ := hclosed 3
        fin_cases y3 <;> simp only [chordStack] at hp3
        · refine absurd (hinj (a₁ := 0) (a₂ := 6) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · exact absurd (by linear_combination hp0 - hp1 - 2 * hp2 + hp3 : A₁ + B₁ = A₂ + B₂) hg12
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = A₂ + h) hna2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 2 * hh2 : h = (0 : R)) hh0
        · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
          simp only [chordStack]; linear_combination hp0 - 2 * hp1 - 2 * hp2 + hp3 - hh2
        · -- continue: partner of 3 is 6
          obtain ⟨y4, hp4⟩ := hclosed 4
          fin_cases y4 <;> simp only [chordStack] at hp4
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : A₁ = A₂) hA1A2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 5 * hh2 : A₁ = B₂) hA1B2
          · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2
          · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
            simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 - 4 * hh2 : h = (0 : R)) hh0
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 4 * hh2 : B₁ = A₁ + h) hna1
          · refine absurd (hinj (a₁ := 0) (a₂ := 9) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp4 - 4 * hh2
          · refine absurd (hinj (a₁ := 1) (a₂ := 9) ?_) (by decide)
            simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp4 - 4 * hh2
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : A₂ + B₂ = A₃ + B₃) hg23
          · -- continue: partner of 4 is 9
            obtain ⟨y5, hp5⟩ := hclosed 5
            fin_cases y5 <;> simp only [chordStack] at hp5
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₁ = A₂) hB1A2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₁ = B₂) hB1B2
            · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2
            · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
              simp only [chordStack]; linear_combination -hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 5 * hh2 : B₁ = A₁ + h) hna1
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp5 - 4 * hh2 : h = (0 : R)) hh0
            · refine absurd (hinj (a₁ := 0) (a₂ := 8) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - hp3 - hp5 - 4 * hh2
            · refine absurd (hinj (a₁ := 1) (a₂ := 8) ?_) (by decide)
              simp only [chordStack]; linear_combination -2 * hp0 - 2 * hp1 - hp2 - 2 * hp3 - hp5 - 4 * hh2
            · have hd : (A₁ - B₁) + (A₁ - B₁) = 0 := by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 + hp5 - 4 * hh2
              rcases hker _ hd with h0 | hh
              · exact absurd (by linear_combination h0 : A₁ = B₁) hA1B1
              · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hh - 5 * hh2 : B₁ = A₁ + h) hna1
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 - hp4 + hp5 - 4 * hh2 : A₁ = B₁) hA1B1
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ = B₃) hA1B3
            · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp5 - 3 * hh2 : A₁ = A₃) hA1A3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : B₁ = B₃) hB1B3
          · exact absurd (by linear_combination -2 * hp0 - 2 * hp1 - 2 * hp2 - 2 * hp3 + hp4 - 3 * hh2 : B₁ = A₃) hB1A3
        · exact absurd (by linear_combination -hp1 - 2 * hp2 + hp3 - hh2 : A₂ = B₂) hA2B2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₁ = A₂) hB1A2
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₁ = A₂) hA1A2
        · exact absurd (by linear_combination -hp0 - hp1 - 2 * hp2 - hp3 - 3 * hh2 : A₂ = B₃) hA2B3
        · exact absurd (by linear_combination -2 * hp1 - 2 * hp2 - hp3 - 3 * hh2 : B₂ = B₃) hB2B3
      · exact absurd (by linear_combination -hp2 - hh2 : B₁ = B₂) hB1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₁ = B₂) hA1B2
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = A₃) hA2A3
      · exact absurd (by linear_combination -hp2 - hh2 : A₂ = B₃) hA2B3
    · exact absurd (by linear_combination -hp0 + hp1 : A₂ = B₂) hA2B2

/-! ## Source audit -/

#print axioms secondLayer_of_no_antipodal

end ArkLib.ProximityGap.SecondLayerConverseCore
