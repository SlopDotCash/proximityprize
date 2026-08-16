/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Per-line bounds do not give a union-count floor without overlap

`_ThreadD_UnionCountFloor` reduces the prize-facing floor input to a per-stack bad-scalar union
bound.  The tempting shortcut is to use a proven per-line/fixed-target count bound and treat it as a
bound for the union over all lines.

This file records the finite obstruction.  If each line contributes at most `S` bad scalars, the
automatic conclusion is only

`#(union over lines) <= (#lines) * S`.

To reach a budget of size `S`, one must prove an additional collapse/overlap theorem.  The disjoint
fiber model shows the obstruction is sharp: many line fibers can each have size `S` while their union
has size `#lines * S`.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.PerLineUnionCountBarrier

variable {ι γ : Type} [DecidableEq γ]

/-- The bad-scalar union over a finite set of lines/targets. -/
def lineBadUnion (I : Finset ι) (lineBad : ι -> Finset γ) : Finset γ :=
  I.biUnion lineBad

/-- The only automatic set-theoretic bound: the union is at most the sum of line sizes. -/
theorem card_lineBadUnion_le_sum_card
    (I : Finset ι) (lineBad : ι -> Finset γ) :
    (lineBadUnion I lineBad).card <= ∑ i ∈ I, (lineBad i).card := by
  unfold lineBadUnion
  exact Finset.card_biUnion_le

/-- A uniform per-line bound gives only `#lines * S`, not `S`. -/
theorem card_lineBadUnion_le_card_mul_of_each_le
    (I : Finset ι) (lineBad : ι -> Finset γ) {S : ℕ}
    (hline : ∀ i ∈ I, (lineBad i).card <= S) :
    (lineBadUnion I lineBad).card <= I.card * S := by
  calc
    (lineBadUnion I lineBad).card <= ∑ i ∈ I, (lineBad i).card :=
      card_lineBadUnion_le_sum_card I lineBad
    _ <= ∑ _i ∈ I, S := by
      exact Finset.sum_le_sum hline
    _ = I.card * S := by
      simp [mul_comm]

/-- Consumer form: per-line bounds close a budget only when the line-count factor also fits. -/
theorem lineBadUnion_budget_of_each_le_and_card_mul_le
    (I : Finset ι) (lineBad : ι -> Finset γ) {S B : ℕ}
    (hline : ∀ i ∈ I, (lineBad i).card <= S)
    (hbudget : I.card * S <= B) :
    (lineBadUnion I lineBad).card <= B :=
  le_trans (card_lineBadUnion_le_card_mul_of_each_le I lineBad hline) hbudget

/-- With pairwise-disjoint line fibers, the union size is exactly the sum of line sizes. -/
theorem card_lineBadUnion_eq_sum_card_of_pairwiseDisjoint
    (I : Finset ι) (lineBad : ι -> Finset γ)
    (hdisj : (I : Set ι).PairwiseDisjoint lineBad) :
    (lineBadUnion I lineBad).card = ∑ i ∈ I, (lineBad i).card := by
  unfold lineBadUnion
  exact Finset.card_biUnion hdisj

/-- If the line fibers are disjoint and each has size `S`, the union has size `#lines * S`. -/
theorem card_lineBadUnion_eq_card_mul_of_disjoint_each_eq
    (I : Finset ι) (lineBad : ι -> Finset γ) {S : ℕ}
    (hdisj : (I : Set ι).PairwiseDisjoint lineBad)
    (hcard : ∀ i ∈ I, (lineBad i).card = S) :
    (lineBadUnion I lineBad).card = I.card * S := by
  calc
    (lineBadUnion I lineBad).card = ∑ i ∈ I, (lineBad i).card :=
      card_lineBadUnion_eq_sum_card_of_pairwiseDisjoint I lineBad hdisj
    _ = ∑ _i ∈ I, S := by
      exact Finset.sum_congr rfl hcard
    _ = I.card * S := by
      simp [mul_comm]

section FiberModel

variable [DecidableEq ι]

/-- The canonical disjoint fiber over a line index. -/
def fiberEmbedding (S : ℕ) (i : ι) : Fin S ↪ ι × Fin S where
  toFun j := (i, j)
  inj' := by
    intro a b h
    exact congrArg Prod.snd h

/-- A size-`S` fiber tagged by its line index. -/
def lineFiber (S : ℕ) (i : ι) : Finset (ι × Fin S) :=
  (Finset.univ : Finset (Fin S)).map (fiberEmbedding S i)

omit [DecidableEq ι] in
@[simp] theorem card_lineFiber (S : ℕ) (i : ι) :
    (lineFiber S i).card = S := by
  simp [lineFiber]

omit [DecidableEq ι] in
@[simp] theorem mem_lineFiber_iff {S : ℕ} {i : ι} {x : ι × Fin S} :
    x ∈ lineFiber S i ↔ x.1 = i := by
  constructor
  · intro hx
    rw [lineFiber] at hx
    rcases Finset.mem_map.mp hx with ⟨j, _hj, h⟩
    exact (congrArg Prod.fst h).symm
  · intro hx
    rw [lineFiber]
    cases x with
    | mk x1 x2 =>
      dsimp at hx
      subst hx
      exact Finset.mem_map.mpr ⟨x2, Finset.mem_univ _, rfl⟩

omit [DecidableEq ι] in
/-- The canonical tagged fibers are pairwise disjoint. -/
theorem pairwiseDisjoint_lineFiber (I : Finset ι) (S : ℕ) :
    (I : Set ι).PairwiseDisjoint (lineFiber S) := by
  intro i _hi j _hj hij
  refine Finset.disjoint_left.mpr ?_
  intro x hxi hxj
  have hi : x.1 = i := mem_lineFiber_iff.mp hxi
  have hj : x.1 = j := mem_lineFiber_iff.mp hxj
  exact hij (hi.symm.trans hj)

omit [DecidableEq ι] in
/-- In the disjoint-fiber model, each line is within the `S` bound. -/
theorem lineFiber_each_le (I : Finset ι) (S : ℕ) :
    ∀ i ∈ I, (lineFiber S i).card <= S := by
  intro i _hi
  simp

/-- In the disjoint-fiber model, the union reaches the full line-count factor. -/
theorem card_lineBadUnion_lineFiber (I : Finset ι) (S : ℕ) :
    (lineBadUnion I (lineFiber S)).card = I.card * S :=
  card_lineBadUnion_eq_card_mul_of_disjoint_each_eq
    I (lineFiber S) (pairwiseDisjoint_lineFiber I S) (by intro i _hi; simp)

/-- Per-line size `S` does not imply union size `<= S`: disjoint fibers with at least two nonempty
lines exceed `S`. -/
theorem lineFiber_union_exceeds_single_line_budget
    (I : Finset ι) {S : ℕ}
    (hI : 1 < I.card) (hS : 0 < S) :
    S < (lineBadUnion I (lineFiber S)).card := by
  rw [card_lineBadUnion_lineFiber I S]
  have hfactor : 1 * S < I.card * S :=
    Nat.mul_lt_mul_of_pos_right hI hS
  simpa using hfactor

/-- Sharp refutation package for the Thread-D shortcut: all line fibers obey the per-line budget
`S`, but the union violates that same budget when at least two nonempty fibers are present. -/
theorem perLineBound_not_unionBound_countermodel
    (I : Finset ι) {S : ℕ}
    (hI : 1 < I.card) (hS : 0 < S) :
    (∀ i ∈ I, (lineFiber S i).card <= S)
      ∧ S < (lineBadUnion I (lineFiber S)).card :=
  ⟨lineFiber_each_le I S, lineFiber_union_exceeds_single_line_budget I hI hS⟩

end FiberModel

#print axioms card_lineBadUnion_le_sum_card
#print axioms card_lineBadUnion_le_card_mul_of_each_le
#print axioms lineBadUnion_budget_of_each_le_and_card_mul_le
#print axioms card_lineBadUnion_eq_sum_card_of_pairwiseDisjoint
#print axioms card_lineBadUnion_eq_card_mul_of_disjoint_each_eq
#print axioms card_lineFiber
#print axioms mem_lineFiber_iff
#print axioms pairwiseDisjoint_lineFiber
#print axioms card_lineBadUnion_lineFiber
#print axioms lineFiber_union_exceeds_single_line_budget
#print axioms perLineBound_not_unionBound_countermodel

end ArkLib.ProximityGap.Frontier.PerLineUnionCountBarrier
