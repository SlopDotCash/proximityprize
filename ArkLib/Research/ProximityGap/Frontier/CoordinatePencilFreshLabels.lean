/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.LinearPencilFreshLabels

/-! # Fresh-label pencils with any finite number of first-row coefficients -/

open Finset Polynomial Code ProximityGap
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.CoordinatePencilFreshLabels

variable {F I S K : Type} [Field F] [Fintype F] [Fintype I] [Nonempty I]
variable [Fintype S] [Fintype K]

/-- A single linear form separates a finite family of coordinate pencils. -/
theorem separating (key : S → K → F) (hinj : Function.Injective key)
    (hsize : (Fintype.card S).choose 2 ≤ Nat.card F) :
    ∃ l : K → F, Function.Injective (fun i => ∑ j, l j * key i j) := by
  classical
  let w (i : S) (_ : Unit) : K → F := key i
  have hw : Function.Injective w := fun _ _ he => hinj (congrFun he ())
  let W := univ.image w
  have hc : W.card = Fintype.card S := (card_image_of_injective _ hw).trans card_univ
  obtain ⟨l, hl⟩ := InterleavedListProjection.exists_separating_projection W (hc ▸ hsize)
  refine ⟨l, fun i j he => hw (hl (mem_image_of_mem w (mem_univ i))
    (mem_image_of_mem w (mem_univ j)) ?_)⟩
  funext x
  simpa [w, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he

variable [DecidableEq I]

/-- Simultaneously project all first rows and retain every core-plus-fresh certificate. -/
theorem mass (dom : I ↪ F) (k : ℕ) (δ : ℝ≥0) (core : S → Finset I) (site : S → I)
    (p : K → S → F[X]) (r : S → F[X]) (u : K → I → F) (w : I → F) (key : S → K → F)
    (hp : ∀ j i, (p j i).degree < (k : WithBot ℕ)) (hr : ∀ i, (r i).degree < (k : WithBot ℕ))
    (hcore : ∀ i x, x ∈ core i →
      (∀ j, (p j i).eval (dom x) = u j x) ∧ (r i).eval (dom x) = w x)
    (hcard : ∀ i, k ≤ (core i).card)
    (hsize : ∀ i, (1 - δ) * (Fintype.card I : ℝ≥0) ≤ (((core i).card + 1 : ℕ) : ℝ≥0))
    (hmis : ∀ i, (r i).eval (dom (site i)) ≠ w (site i))
    (hkey : ∀ i j, key i j * ((r i).eval (dom (site i)) - w (site i)) =
      u j (site i) - (p j i).eval (dom (site i)))
    (hinj : Function.Injective key) (hfield : (Fintype.card S).choose 2 ≤ Nat.card F) :
    (Fintype.card S : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  classical
  obtain ⟨l, hl⟩ := separating key hinj hfield
  let label : S ↪ F := ⟨_, hl⟩
  let row (x : I) := ∑ j, l j * u j x
  let rows : WordStack F (Fin 2) I := ![row, w]
  let first (i : S) := ∑ j, C (l j) * p j i
  have degreeC (a : F) (q : F[X]) (hq : q.degree < (k : WithBot ℕ)) :
      (C a * q).degree < (k : WithBot ℕ) := by
    by_cases hz : a = 0
    · simp [hz]
    · simpa [degree_C_mul hz] using hq
  have degFirst (i : S) : (first i).degree < (k : WithBot ℕ) := by
    have hsum (s : Finset K) : (∑ j ∈ s, C (l j) * p j i).degree < (k : WithBot ℕ) := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [sum_insert ha]
        exact (degree_add_le _ _).trans_lt (max_lt (degreeC _ _ (hp a i)) ih)
    exact hsum univ
  have event (i : S) : mcaEvent (F := F) (ReedSolomon.code dom k : Set (I → F)) δ
      (rows 0) (rows 1) (label i) := by
    apply HalfPredecessorCoreFreshDecode.mcaEvent_of_affine_core_fresh
      dom k δ rows (label i) (core i) (site i) (first i) (r i)
    · exact fun he => hmis i (hcore i _ he).2
    · exact degFirst i
    · exact hr i
    · exact (degree_add_le _ _).trans_lt (max_lt (degFirst i) (degreeC _ _ (hr i)))
    · exact hcard i
    · exact hsize i
    · intro x hx
      obtain ⟨hu, hw⟩ := hcore i x hx
      simp [rows, first, row, hu, hw, eval_finset_sum]
    · change (first i + C (∑ j, l j * key i j) * r i).eval (dom (site i)) =
        (∑ j, l j * u j (site i)) + (∑ j, l j * key i j) * w (site i)
      simp only [first, eval_add, eval_mul, eval_C, eval_finset_sum, sum_mul, ← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      linear_combination l j * hkey i j
    · exact fun he => hmis i (congrArg Prod.snd he)
  have hmass := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (ReedSolomon.code dom k : Set (I → F)) δ rows (univ.map label) (by
      intro z hz
      obtain ⟨i, _, rfl⟩ := mem_map.mp hz
      exact event i)
  simpa only [card_map, card_univ] using hmass

end ArkLib.ProximityGap.Frontier.CoordinatePencilFreshLabels

#print axioms ArkLib.ProximityGap.Frontier.CoordinatePencilFreshLabels.mass
