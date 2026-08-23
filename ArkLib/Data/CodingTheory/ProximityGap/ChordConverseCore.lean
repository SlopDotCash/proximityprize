/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The chord converse, core: the antipodal branch of the wide-circuit classification

Campaign #357, exactness-converse lane, increment 2. By the trichotomy
(`WideCircuitTrichotomy.lean`) the converse reduces to the generic branch; this file
classifies its **antipodal stratum**: a generic wide circuit whose (say) second pair is
antipodal is forced into the two-plus-antipodal **chord-law form** — the pairs `1` and
`3` share a difference class and the chord congruence `2·A₂ = A₁ + B₃` (or the mirror
orientation) holds.

The theorem is stated abstractly over a commutative ring `R` with a distinguished
element `h` satisfying `h + h = 0`, `h ≠ 0`, and the **doubling-kernel hypothesis**
`u + u = 0 → u = 0 ∨ u = h` (instantiated by `ZMod (2^m)` with `h = 2^(m−1)` via
`double_eq_zero_iff`). The wide-circuit data enters through the shifted 12-exponent
stack `chordStack` (the `signedExp` family of the matching frame, in ring form):

* `hinj` — multiplicity-freeness: the stack is injective;
* `hclosed` — balance: the stack's value set is closed under `+ h` (every element has
  an antipodal partner);
* `Distinct6`/genericity/single-antipodal hypotheses as in the trichotomy's generic
  branch.

**`chord_of_antipodal_partner`** walks the canonical-matching case tree: the partner of
index `4` must be `6`, `7` or `9` (eight branches die on `Distinct6`/genericity/
injectivity); partner `9` dies in a sub-tree (the `2(B₁−A₁) = 0` node kill and two
doubling-branch kills landing on injectivity); partners `6`/`7` force the two chord
orientations after one more partner choice. The tree was charted exhaustively by
`probe_antipodal_branch_tree.py`: 105 leaves, 103 killed, the 2 survivors = the chord
systems — this file is its transcription with every kill verified by hand.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Issue #357 (the matching-pattern census; the exactness-converse lane);
  `CollinearityMatchingFrame.lean`, `WideCircuitTrichotomy.lean`,
  `TwoPlusAntipodalChordLaw.lean` (the supply side this converse completes).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.ChordConverseCore

variable {R : Type*} [CommRing R]

/-- The shifted 12-exponent stack of the collinearity determinant, in ring form: the
six positive product-terms bare, the six negative ones shifted by the half-period `h`
(the `signedExp` family of the matching frame). -/
def chordStack (A₁ B₁ A₂ B₂ A₃ B₃ h : R) : Fin 12 → R := fun x =>
  match x with
  | 0 => A₂ + (A₃ + B₃)
  | 1 => B₂ + (A₃ + B₃)
  | 2 => A₂ + (A₁ + B₁) + h
  | 3 => B₂ + (A₁ + B₁) + h
  | 4 => A₁ + (A₃ + B₃) + h
  | 5 => B₁ + (A₃ + B₃) + h
  | 6 => A₃ + (A₂ + B₂) + h
  | 7 => B₃ + (A₂ + B₂) + h
  | 8 => A₁ + (A₂ + B₂)
  | 9 => B₁ + (A₂ + B₂)
  | 10 => A₃ + (A₁ + B₁)
  | 11 => B₃ + (A₁ + B₁)

/-- **The antipodal-branch classification.** Over any commutative ring with a
half-period `h` (`h + h = 0`, `h ≠ 0`, doubling kernel `{0, h}`): if the shifted
12-stack of a `Distinct6` triple with pair `2` antipodal (and pairs `1`, `3` not
antipodal, products pairwise distinct) is injective and closed under `+ h`, then the
configuration is a **chord-law triple**: pairs `1` and `3` share a difference class and
the chord congruence holds, in one of the two orientations. -/
theorem chord_of_antipodal_partner {A₁ B₁ A₂ B₂ A₃ B₃ h : R}
    (hh2 : h + h = 0) (hh0 : h ≠ 0)
    (hker : ∀ u : R, u + u = 0 → u = 0 ∨ u = h)
    (hA1B1 : A₁ ≠ B₁)
    (hA1A2 : A₁ ≠ A₂) (hA1B2 : A₁ ≠ B₂) (hB1A2 : B₁ ≠ A₂) (hB1B2 : B₁ ≠ B₂)
    (hA1A3 : A₁ ≠ A₃) (hA1B3 : A₁ ≠ B₃) (hB1A3 : B₁ ≠ A₃) (hB1B3 : B₁ ≠ B₃)
    (hg12 : A₁ + B₁ ≠ A₂ + B₂) (hg23 : A₂ + B₂ ≠ A₃ + B₃)
    (hant₂ : B₂ = A₂ + h) (hna₁ : B₁ ≠ A₁ + h) (hna₃ : B₃ ≠ A₃ + h)
    (hinj : Function.Injective (chordStack A₁ B₁ A₂ B₂ A₃ B₃ h))
    (hclosed : ∀ x : Fin 12, ∃ y : Fin 12,
      chordStack A₁ B₁ A₂ B₂ A₃ B₃ h y = chordStack A₁ B₁ A₂ B₂ A₃ B₃ h x + h) :
    (A₁ - B₁ = A₃ - B₃ ∧ 2 * A₂ = A₁ + B₃)
      ∨ (A₁ - B₁ = B₃ - A₃ ∧ 2 * A₂ = A₁ + A₃) := by
  -- the forced within-pair facts of the antipodal point (raw form)
  have e01 : B₂ + (A₃ + B₃) = A₂ + (A₃ + B₃) + h := by linear_combination hant₂
  have e23 : B₂ + (A₁ + B₁) + h = A₂ + (A₁ + B₁) + h + h := by linear_combination hant₂
  -- NODE A: the partner of index 4
  obtain ⟨y, hy⟩ := hclosed 4
  fin_cases y <;> simp only [chordStack] at hy
  -- y = 0 : A₂ = A₁
  · exact absurd (by linear_combination hy + hh2 : A₂ = A₁).symm hA1A2
  -- y = 1 : B₂ = A₁
  · exact absurd (by linear_combination hy + hh2 : B₂ = A₁).symm hA1B2
  -- y = 2 : index 3 collides with 4
  · refine absurd (hinj (a₁ := 3) (a₂ := 4) ?_) (by decide)
    simp only [chordStack]; linear_combination hy + hant₂ + hh2
  -- y = 3 : index 2 collides with 4
  · refine absurd (hinj (a₁ := 2) (a₂ := 4) ?_) (by decide)
    simp only [chordStack]; linear_combination hy - hant₂
  -- y = 4 : h = 0
  · exact absurd (by linear_combination -hy : h = (0 : R)) hh0
  -- y = 5 : pair 1 antipodal
  · exact absurd (by linear_combination hy : B₁ = A₁ + h) hna₁
  -- y = 6 : NODE B
  · obtain ⟨z, hz⟩ := hclosed 5
    fin_cases z <;> simp only [chordStack] at hz
    · exact absurd (by linear_combination hz + hh2 : A₂ = B₁).symm hB1A2
    · exact absurd (by linear_combination hz + hh2 : B₂ = B₁).symm hB1B2
    · refine absurd (hinj (a₁ := 3) (a₂ := 5) ?_) (by decide)
      simp only [chordStack]; linear_combination hz + hant₂ + hh2
    · refine absurd (hinj (a₁ := 2) (a₂ := 5) ?_) (by decide)
      simp only [chordStack]; linear_combination hz - hant₂
    · exact absurd (by linear_combination -hz - hh2 : B₁ = A₁ + h) hna₁
    · exact absurd (by linear_combination -hz : h = (0 : R)) hh0
    · refine absurd (hinj (a₁ := 5) (a₂ := 4) ?_) (by decide)
      simp only [chordStack]; linear_combination hy - hz
    -- z = 7 : CONCLUDE LEFT
    · have c2 : 2 * A₂ = A₁ + B₃ := by linear_combination hy - hant₂
      have c2' : 2 * A₂ = B₁ + A₃ := by linear_combination hz - hant₂
      exact Or.inl ⟨by linear_combination c2' - c2, c2⟩
    -- z = 8 : NODE B8 — walk index 7, all twelve die
    · obtain ⟨w, hw⟩ := hclosed 7
      fin_cases w <;> simp only [chordStack] at hw
      · refine absurd (hinj (a₁ := 1) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + e01 + hh2
      · refine absurd (hinj (a₁ := 0) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw - e01
      · refine absurd (hinj (a₁ := 3) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + e23 + hh2
      · refine absurd (hinj (a₁ := 2) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw - e23
      · refine absurd (hinj (a₁ := 6) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + hy + hh2
      · refine absurd (hinj (a₁ := 8) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + hz + hh2
      · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw - hy
      · exact absurd (by linear_combination -hw : h = (0 : R)) hh0
      · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw - hz
      · exact absurd (by linear_combination hw + hh2 : B₁ = B₃) hB1B3
      -- w = 10 : the doubling branch
      · have hd : (A₁ - B₃) + (A₁ - B₃) = 0 := by linear_combination hz + hw + 2 * hh2
        rcases hker _ hd with h0 | hh
        · exact absurd (by linear_combination h0 : A₁ = B₃) hA1B3
        · refine absurd (hinj (a₁ := 5) (a₂ := 10) ?_) (by decide)
          simp only [chordStack]; linear_combination -hh
      · exact absurd (by linear_combination hw + hh2 : A₁ + B₁ = A₂ + B₂) hg12
    · exact absurd (by linear_combination hz + hh2 : A₂ + B₂ = A₃ + B₃) hg23
    · exact absurd (by linear_combination hz + hh2 : A₁ = B₃) hA1B3
    · exact absurd (by linear_combination hz + hh2 : A₁ = A₃) hA1A3
  -- y = 7 : NODE B′
  · obtain ⟨z, hz⟩ := hclosed 5
    fin_cases z <;> simp only [chordStack] at hz
    · exact absurd (by linear_combination hz + hh2 : A₂ = B₁).symm hB1A2
    · exact absurd (by linear_combination hz + hh2 : B₂ = B₁).symm hB1B2
    · refine absurd (hinj (a₁ := 3) (a₂ := 5) ?_) (by decide)
      simp only [chordStack]; linear_combination hz + hant₂ + hh2
    · refine absurd (hinj (a₁ := 2) (a₂ := 5) ?_) (by decide)
      simp only [chordStack]; linear_combination hz - hant₂
    · exact absurd (by linear_combination -hz - hh2 : B₁ = A₁ + h) hna₁
    · exact absurd (by linear_combination -hz : h = (0 : R)) hh0
    -- z = 6 : CONCLUDE RIGHT
    · have c2R : 2 * A₂ = A₁ + A₃ := by linear_combination hy - hant₂
      have c2R' : 2 * A₂ = B₁ + B₃ := by linear_combination hz - hant₂
      exact Or.inr ⟨by linear_combination c2R' - c2R, c2R⟩
    · refine absurd (hinj (a₁ := 5) (a₂ := 4) ?_) (by decide)
      simp only [chordStack]; linear_combination hy - hz
    -- z = 8 : NODE B′8 — walk index 6, all twelve die
    · obtain ⟨w, hw⟩ := hclosed 6
      fin_cases w <;> simp only [chordStack] at hw
      · refine absurd (hinj (a₁ := 1) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + e01 + hh2
      · refine absurd (hinj (a₁ := 0) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hw - e01
      · refine absurd (hinj (a₁ := 3) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + e23 + hh2
      · refine absurd (hinj (a₁ := 2) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hw - e23
      · refine absurd (hinj (a₁ := 7) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + hy + hh2
      · refine absurd (hinj (a₁ := 8) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + hz + hh2
      · exact absurd (by linear_combination -hw : h = (0 : R)) hh0
      · exact absurd (by linear_combination hw : B₃ = A₃ + h) hna₃
      · refine absurd (hinj (a₁ := 6) (a₂ := 5) ?_) (by decide)
        simp only [chordStack]; linear_combination hz - hw
      · exact absurd (by linear_combination hw + hh2 : B₁ = A₃) hB1A3
      · exact absurd (by linear_combination hw + hh2 : A₁ + B₁ = A₂ + B₂) hg12
      -- w = 11 : the doubling branch
      · have hd : (A₁ - A₃) + (A₁ - A₃) = 0 := by linear_combination hz + hw + 2 * hh2
        rcases hker _ hd with h0 | hh
        · exact absurd (by linear_combination h0 : A₁ = A₃) hA1A3
        · refine absurd (hinj (a₁ := 5) (a₂ := 11) ?_) (by decide)
          simp only [chordStack]; linear_combination -hh
    · exact absurd (by linear_combination hz + hh2 : A₂ + B₂ = A₃ + B₃) hg23
    · exact absurd (by linear_combination hz + hh2 : A₁ = B₃) hA1B3
    · exact absurd (by linear_combination hz + hh2 : A₁ = A₃) hA1A3
  -- y = 8 : product collision s₂ = s₃
  · exact absurd (by linear_combination hy + hh2 : A₂ + B₂ = A₃ + B₃) hg23
  -- y = 9 : NODE C — all sub-branches die
  · obtain ⟨z, hz⟩ := hclosed 5
    fin_cases z <;> simp only [chordStack] at hz
    · exact absurd (by linear_combination hz + hh2 : A₂ = B₁).symm hB1A2
    · exact absurd (by linear_combination hz + hh2 : B₂ = B₁).symm hB1B2
    · refine absurd (hinj (a₁ := 3) (a₂ := 5) ?_) (by decide)
      simp only [chordStack]; linear_combination hz + hant₂ + hh2
    · refine absurd (hinj (a₁ := 2) (a₂ := 5) ?_) (by decide)
      simp only [chordStack]; linear_combination hz - hant₂
    · exact absurd (by linear_combination -hz - hh2 : B₁ = A₁ + h) hna₁
    · exact absurd (by linear_combination -hz : h = (0 : R)) hh0
    -- z = 6 : walk index 7, all twelve die
    · obtain ⟨w, hw⟩ := hclosed 7
      fin_cases w <;> simp only [chordStack] at hw
      · refine absurd (hinj (a₁ := 1) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + e01 + hh2
      · refine absurd (hinj (a₁ := 0) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw - e01
      · refine absurd (hinj (a₁ := 3) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + e23 + hh2
      · refine absurd (hinj (a₁ := 2) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw - e23
      · refine absurd (hinj (a₁ := 9) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + hy + hh2
      · refine absurd (hinj (a₁ := 6) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + hz + hh2
      · refine absurd (hinj (a₁ := 5) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw - hz
      · exact absurd (by linear_combination -hw : h = (0 : R)) hh0
      · exact absurd (by linear_combination hw + hh2 : A₁ = B₃) hA1B3
      · refine absurd (hinj (a₁ := 4) (a₂ := 7) ?_) (by decide)
        simp only [chordStack]; linear_combination hw - hy
      -- w = 10 : the doubling branch
      · have hd : (B₁ - B₃) + (B₁ - B₃) = 0 := by linear_combination hy + hw + 2 * hh2
        rcases hker _ hd with h0 | hh
        · exact absurd (by linear_combination h0 : B₁ = B₃) hB1B3
        · refine absurd (hinj (a₁ := 4) (a₂ := 10) ?_) (by decide)
          simp only [chordStack]; linear_combination -hh
      · exact absurd (by linear_combination hw + hh2 : A₁ + B₁ = A₂ + B₂) hg12
    -- z = 7 : walk index 6, all twelve die
    · obtain ⟨w, hw⟩ := hclosed 6
      fin_cases w <;> simp only [chordStack] at hw
      · refine absurd (hinj (a₁ := 1) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + e01 + hh2
      · refine absurd (hinj (a₁ := 0) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hw - e01
      · refine absurd (hinj (a₁ := 3) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + e23 + hh2
      · refine absurd (hinj (a₁ := 2) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hw - e23
      · refine absurd (hinj (a₁ := 9) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + hy + hh2
      · refine absurd (hinj (a₁ := 7) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hw + hz + hh2
      · exact absurd (by linear_combination -hw : h = (0 : R)) hh0
      · refine absurd (hinj (a₁ := 5) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hw - hz
      · exact absurd (by linear_combination hw + hh2 : A₁ = A₃) hA1A3
      · refine absurd (hinj (a₁ := 4) (a₂ := 6) ?_) (by decide)
        simp only [chordStack]; linear_combination hw - hy
      · exact absurd (by linear_combination hw + hh2 : A₁ + B₁ = A₂ + B₂) hg12
      -- w = 11 : the doubling branch
      · have hd : (B₁ - A₃) + (B₁ - A₃) = 0 := by linear_combination hy + hw + 2 * hh2
        rcases hker _ hd with h0 | hh
        · exact absurd (by linear_combination h0 : B₁ = A₃) hB1A3
        · refine absurd (hinj (a₁ := 4) (a₂ := 11) ?_) (by decide)
          simp only [chordStack]; linear_combination -hh
    -- z = 8 : the node kill 2(B₁ − A₁) = 0
    · have hd : (B₁ - A₁) + (B₁ - A₁) = 0 := by linear_combination hy - hz
      rcases hker _ hd with h0 | hh
      · exact absurd (by linear_combination -h0 : A₁ = B₁) hA1B1
      · exact absurd (by linear_combination hh : B₁ = A₁ + h) hna₁
    · refine absurd (hinj (a₁ := 4) (a₂ := 5) ?_) (by decide)
      simp only [chordStack]; linear_combination hz - hy
    · exact absurd (by linear_combination hz + hh2 : A₁ = B₃) hA1B3
    · exact absurd (by linear_combination hz + hh2 : A₁ = A₃) hA1A3
  -- y = 10 : B₁ = B₃
  · exact absurd (by linear_combination hy + hh2 : B₁ = B₃) hB1B3
  -- y = 11 : B₁ = A₃
  · exact absurd (by linear_combination hy + hh2 : B₁ = A₃) hB1A3

/-! ## Source audit -/

#print axioms chord_of_antipodal_partner

end ArkLib.ProximityGap.ChordConverseCore
