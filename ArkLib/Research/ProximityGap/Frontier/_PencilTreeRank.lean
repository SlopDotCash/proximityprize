/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Rank of an ordered tree of meeting affine pencils

Starting with the two coefficients at the root, each meeting edge requires only
one new generator, its slope jump. The ordered parent condition permits a direct
induction and also allows shortening through any submodule of supported words.
-/

namespace ProximityGap.PencilTreeRank

/-- A submodule containing both root coefficients and every parent-edge slope
jump contains both coefficients of every pencil. -/
theorem coefficients_mem_of_parent_jumps {F M : Type*} [Field F]
    [AddCommGroup M] [Module F M] {m : ℕ}
    (U V : Fin (m + 1) → M) (parent : Fin m → Fin (m + 1))
    (a : Fin m → F) (W : Submodule F M)
    (hparent : ∀ i, (parent i).val < i.succ.val)
    (hmeet : ∀ i, U i.succ + a i • V i.succ =
      U (parent i) + a i • V (parent i))
    (hrootU : U 0 ∈ W) (hrootV : V 0 ∈ W)
    (hjump : ∀ i, V i.succ - V (parent i) ∈ W) :
    ∀ i, U i ∈ W ∧ V i ∈ W := by
  have all (n : ℕ) : ∀ i : Fin (m + 1), i.val = n → U i ∈ W ∧ V i ∈ W := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      refine Fin.cases (motive := fun j ↦ j.val = n → U j ∈ W ∧ V j ∈ W) ?_ ?_ i hi
      · exact fun _ ↦ ⟨hrootU, hrootV⟩
      · intro j hj
        have smaller : (parent j).val < n := hj ▸ hparent j
        obtain ⟨hPU, hPV⟩ := ih _ smaller _ rfl
        have hU : U j.succ - U (parent j) = -(a j • (V j.succ - V (parent j))) := by
          rw [smul_sub]
          calc
            U j.succ - U (parent j) =
                (U j.succ + a j • V j.succ) - (U (parent j) + a j • V j.succ) := by abel
            _ = _ := by
              rw [hmeet j]
              abel
        constructor
        · have hdiff : U j.succ - U (parent j) ∈ W := by
            rw [hU]
            exact W.neg_mem (W.smul_mem _ (hjump j))
          simpa only [sub_add_cancel] using W.add_mem hdiff hPU
        · simpa only [sub_add_cancel] using W.add_mem (hjump j) hPV
  exact fun i ↦ all i.val i rfl

/-- The joint coefficient span for a tree of m+1 meeting pencils has rank at
most m+2. This applies to lifted coefficients as well as codeword coefficients. -/
theorem finrank_coefficients_le {F M : Type*} [Field F]
    [AddCommGroup M] [Module F M] {m : ℕ}
    (U V : Fin (m + 1) → M) (parent : Fin m → Fin (m + 1))
    (a : Fin m → F)
    (hparent : ∀ i, (parent i).val < i.succ.val)
    (hmeet : ∀ i, U i.succ + a i • V i.succ =
      U (parent i) + a i • V (parent i)) :
    Module.finrank F (Submodule.span F (Set.range U ∪ Set.range V)) ≤ m + 2 := by
  classical
  let D : Finset M := Finset.univ.image (fun i : Fin m ↦ V i.succ - V (parent i))
  let G : Finset M := insert (U 0) (insert (V 0) D)
  let W := Submodule.span F (G : Set M)
  letI : Module.Finite F W := Module.Finite.span_of_finite F G.finite_toSet
  have hmem := coefficients_mem_of_parent_jumps U V parent a W hparent hmeet
    (Submodule.subset_span (by simp [G])) (Submodule.subset_span (by simp [G]))
    (fun i ↦ Submodule.subset_span (by simp [G, D, Finset.mem_image_of_mem]))
  have hle : Submodule.span F (Set.range U ∪ Set.range V) ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact (hmem i).1
    · exact (hmem i).2
  have hD : D.card ≤ m := by
    simpa [D] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m)))
      (f := fun i ↦ V i.succ - V (parent i)))
  have hG : G.card ≤ m + 2 :=
    (Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ hD)))
  exact (Submodule.finrank_mono hle).trans ((finrank_span_finset_le_card G).trans hG)

end ProximityGap.PencilTreeRank

#print axioms ProximityGap.PencilTreeRank.coefficients_mem_of_parent_jumps
#print axioms ProximityGap.PencilTreeRank.finrank_coefficients_le
