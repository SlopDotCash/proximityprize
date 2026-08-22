/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage

/-!
# The two-anchor bootstrap cannot start without a deep triple overlap

An elimination proof of the gauged divided-difference kernel begins with two zero components.  At
the first positive rank, every lower-rank parent is one of those two anchors.  Consequently the
first new component can be killed by coordinatewise two-parent root forcing only if it shares at
least `degree` coordinates with both anchors.

This is an exact obstruction to treating the coordinate-bootstrap criterion as a consequence of
Hall budgets.  Generic support families may have every distinct triple overlap below the decoded
degree even while their global divided-difference matrix has full rank.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.TwoAnchorBootstrapFirstStepNoGo

/-- Coordinates containing a fixed triple of labels. -/
def tripleCoords {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X → Finset J) (a b j : J) : Finset X :=
  Finset.univ.filter fun x => a ∈ support x ∧ b ∈ support x ∧ j ∈ support x

/-- Coordinates where `j` occurs with two distinct strictly lower-rank labels. -/
noncomputable def lowerPairCoords {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X → Finset J) (rank : J → Nat) (j : J) : Finset X := by
  classical
  exact Finset.univ.filter fun x =>
    j ∈ support x ∧ ∃ p r, rank p < rank j ∧ rank r < rank j ∧ p ≠ r ∧
      p ∈ support x ∧ r ∈ support x

/-- At a minimal positive rank, coordinate-dependent lower-parent coverage reduces to the fixed
two-anchor triple intersection. -/
theorem lowerPairCoords_subset_tripleCoords_of_minimal_positive
    {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X → Finset J) (rank : J → Nat) {a b j : J}
    (hzero : ∀ p, rank p = 0 → p = a ∨ p = b)
    (hminimal : ∀ p, rank p < rank j → rank p = 0) :
    lowerPairCoords support rank j ⊆ tripleCoords support a b j := by
  classical
  intro x hx
  simp only [lowerPairCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨hj, p, r, hpRank, hrRank, hpr, hp, hr⟩ := hx
  have hpAnchor := hzero p (hminimal p hpRank)
  have hrAnchor := hzero r (hminimal r hrRank)
  have habMem : a ∈ support x ∧ b ∈ support x := by
    rcases hpAnchor with rfl | rfl <;> rcases hrAnchor with rfl | rfl
    · exact (hpr rfl).elim
    · exact ⟨hp, hr⟩
    · exact ⟨hr, hp⟩
    · exact (hpr rfl).elim
  simp only [tripleCoords, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨habMem.1, habMem.2, hj⟩

/-- **First-step no-go.**  If the anchor triple overlap of a minimal positive-rank component is
smaller than the polynomial degree, the two-parent coordinate bootstrap coverage is impossible. -/
theorem not_degree_le_lowerPairCoords_of_triple_lt
    {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X → Finset J) (rank : J → Nat) {degree : Nat} {a b j : J}
    (hzero : ∀ p, rank p = 0 → p = a ∨ p = b)
    (hminimal : ∀ p, rank p < rank j → rank p = 0)
    (htriple : (tripleCoords support a b j).card < degree) :
    ¬ degree ≤ (lowerPairCoords support rank j).card := by
  classical
  intro hcoverage
  have hsubset := lowerPairCoords_subset_tripleCoords_of_minimal_positive
    support rank hzero hminimal
  have hcard := Finset.card_le_card hsubset
  omega

end ArkLib.ProximityGap.Frontier.TwoAnchorBootstrapFirstStepNoGo

#print axioms ArkLib.ProximityGap.Frontier.TwoAnchorBootstrapFirstStepNoGo.lowerPairCoords_subset_tripleCoords_of_minimal_positive
#print axioms ArkLib.ProximityGap.Frontier.TwoAnchorBootstrapFirstStepNoGo.not_degree_le_lowerPairCoords_of_triple_lt
