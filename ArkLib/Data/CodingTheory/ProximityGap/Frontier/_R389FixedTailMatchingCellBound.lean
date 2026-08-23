/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R388FixedTailMatchingRigidity

/-!
# R389: a fixed-tail nonzero matching cell has at most `|G|` elements

This file converts R388's rigidity into the cardinality estimate needed by the four-sum fiber
bound.  Concatenate a variable four-tuple `a` with the negation of a fixed reference tuple `z`.
For a matching with at most one internal variable edge, the matching cell maps injectively to `G`
by reading the canonical free coordinate.  Hence each cell has cardinality at most `|G|`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.NegationClosedWalk

namespace ArkLib.ProximityGap.Frontier.R389FixedTailMatchingCellBound

open ArkLib.ProximityGap.Frontier.R387NonzeroFourFiberMatchingTopology
open ArkLib.ProximityGap.Frontier.R388FixedTailMatchingRigidity

/-- Concatenate the variable tuple with the negation of the fixed reference tuple. -/
def relationTuple {F : Type*} [Neg F] (a z : Fin 4 → F) : Fin (2 * 4) → F := fun i =>
  if h : (i : ℕ) < 4 then a ⟨i, h⟩ else -z ⟨(i : ℕ) - 4, by have := i.isLt; omega⟩

/-- The canonical free coordinate viewed as an index of the variable four-tuple. -/
def freeIndex (σ : Equiv.Perm (Fin (2 * 4))) : Fin 4 :=
  ⟨freeCoord σ, by
    have h := freeCoord_mem_leftFour σ
    simpa [leftFour] using (Finset.mem_filter.mp h).2⟩

@[simp] theorem relationTuple_left
    {F : Type*} [Neg F] (a z : Fin 4 → F) (j : Fin 4) :
    relationTuple a z ⟨j, by omega⟩ = a j := by
  simp [relationTuple]

@[simp] theorem relationTuple_freeCoord
    {F : Type*} [Neg F] (a z : Fin 4 → F) (σ : Equiv.Perm (Fin (2 * 4))) :
    relationTuple a z (freeCoord σ) = a (freeIndex σ) := by
  unfold relationTuple freeIndex
  have h := freeCoord_mem_leftFour σ
  have hlt : ((freeCoord σ : Fin (2 * 4)) : ℕ) < 4 :=
    (Finset.mem_filter.mp h).2
  rw [dif_pos hlt]

/-- Variable four-tuples in `G` whose concatenated relation is paired by `sigma`. -/
noncomputable def matchingCell
    {F : Type*} [Field F] [DecidableEq F]
    (G : Finset F) (z : Fin 4 → F) (σ : Equiv.Perm (Fin (2 * 4))) : Finset (Fin 4 → F) :=
  (Fintype.piFinset fun _ : Fin 4 => G).filter
    (fun a => ∀ i, relationTuple a z (σ i) = -relationTuple a z i)

/-- Two relation tuples with the same fixed right tail agree there automatically. -/
theorem relationTuple_eq_on_right
    {F : Type*} [Field F] [DecidableEq F]
    (a b z : Fin 4 → F) :
    ∀ i, i ∉ leftFour → relationTuple a z i = relationTuple b z i := by
  intro i hi
  unfold relationTuple
  have hge : ¬ (i : ℕ) < 4 := by
    intro hlt
    apply hi
    simp [leftFour, hlt]
  rw [dif_neg hge, dif_neg hge]

/-- **Fixed-cell cardinality bound.** One free subgroup value parametrizes the whole cell. -/
theorem card_matchingCell_le
    {F : Type*} [Field F] [DecidableEq F]
    (G : Finset F) (z : Fin 4 → F) (σ : Equiv.Perm (Fin (2 * 4))) (hσ : IsPairing σ)
    (hcard : (internalLeftEdges σ).card ≤ 1) :
    (matchingCell G z σ).card ≤ G.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun a => a (freeIndex σ))
  · intro a ha
    rw [Finset.mem_coe, matchingCell, Finset.mem_filter] at ha
    exact (Fintype.mem_piFinset.mp ha.1) (freeIndex σ)
  · intro a ha b hb hab
    rw [Finset.mem_coe, matchingCell, Finset.mem_filter] at ha hb
    apply funext
    intro j
    let i : Fin (2 * 4) := ⟨j, by omega⟩
    have hi : i ∈ leftFour := by simp [i, leftFour]
    have hleft := eq_on_leftFour_of_eq_freeCoord_of_eq_on_right
      (relationTuple a z) (relationTuple b z) σ hσ hcard ha.2 hb.2
      (relationTuple_eq_on_right a b z) (by simpa using hab) i hi
    simpa [i] using hleft

end ArkLib.ProximityGap.Frontier.R389FixedTailMatchingCellBound

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R389FixedTailMatchingCellBound.card_matchingCell_le
