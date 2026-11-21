/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.InterleavedListProjection
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorCoreFreshDecode
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-! # Choosing distinct bad scalars on several polynomial heads

Two independent first-row polynomials and a fixed second row give one scalar
linear functional for each fresh coordinate. A single choice of first row
makes the scalars all distinct and gives one received pair witnessing their
joint contribution to the MCA error.
-/

open Finset Polynomial Code
open _root_.ProximityGap
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.LinearPencilFreshLabels

variable {F I S : Type} [Field F] [Fintype F] [Fintype I] [Nonempty I]
variable [Fintype S]

/-- Distinct two-coordinate functionals have distinct values at one common vector
when the number of unordered pairs is at most the field size. -/
theorem separating_pair (key : S → Fin 2 → F) (hinj : Function.Injective key)
    (hsize : (Fintype.card S).choose 2 ≤ Nat.card F) :
    ∃ a b : F, Function.Injective (fun i => a * key i 0 + b * key i 1) := by
  classical
  let w (i : S) (_ : Unit) : Fin 2 → F := key i
  have hw : Function.Injective w := fun _ _ h => hinj (congrFun h ())
  let W := univ.image w
  have hc : W.card = Fintype.card S := (card_image_of_injective _ hw).trans card_univ
  obtain ⟨l, hl⟩ := InterleavedListProjection.exists_separating_projection W (hc ▸ hsize)
  refine ⟨l 0, l 1, fun i j h => hw (hl (mem_image_of_mem w (mem_univ i))
    (mem_image_of_mem w (mem_univ j)) ?_)⟩
  funext x
  simpa [w, Fin.sum_univ_two, Pi.add_apply, smul_eq_mul] using h

variable [DecidableEq I]

/-- On each core the head polynomials give both components of the received
first-row pencil and its fixed second row. At the indicated fresh site the
corresponding normalized differences determine its scalar functional. -/
theorem mass_of_distinct_fresh_labels
    (dom : I ↪ F) (k : ℕ) (δ : ℝ≥0) (core : S → Finset I) (site : S → I)
    (p q r : S → F[X]) (u v w : I → F) (key : S → Fin 2 → F)
    (hp : ∀ i, (p i).degree < (k : WithBot ℕ))
    (hq : ∀ i, (q i).degree < (k : WithBot ℕ))
    (hr : ∀ i, (r i).degree < (k : WithBot ℕ))
    (hcore : ∀ i x, x ∈ core i → (p i).eval (dom x) = u x ∧
      (q i).eval (dom x) = v x ∧ (r i).eval (dom x) = w x)
    (hcard : ∀ i, k ≤ (core i).card)
    (hsize : ∀ i, (1-δ) * (Fintype.card I : ℝ≥0) ≤ (((core i).card+1 : ℕ) : ℝ≥0))
    (hmis : ∀ i, (r i).eval (dom (site i)) ≠ w (site i))
    (hkey : ∀ i,
      key i 0 * ((r i).eval (dom (site i)) - w (site i)) = u (site i) - (p i).eval (dom (site i)) ∧
      key i 1 * ((r i).eval (dom (site i)) - w (site i)) = v (site i) - (q i).eval (dom (site i)))
    (hinj : Function.Injective key) (hfield : (Fintype.card S).choose 2 ≤ Nat.card F) :
    (Fintype.card S : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  classical
  obtain ⟨a, b, hsep⟩ := separating_pair key hinj hfield
  let label : S ↪ F := ⟨_, hsep⟩
  let rows : WordStack F (Fin 2) I := ![fun x => a*u x+b*v x, w]
  let first (i : S) := C a * p i + C b * q i
  have degree_mul (c : F) (f : F[X]) (hf : f.degree < (k : WithBot ℕ)) :
      (C c * f).degree < (k : WithBot ℕ) := by
    by_cases hz : c = 0
    · simp [hz]
    · simpa [degree_C_mul hz] using hf
  have deg_first (i : S) : (first i).degree < (k : WithBot ℕ) :=
    (degree_add_le _ _).trans_lt (max_lt (degree_mul _ _ (hp i)) (degree_mul _ _ (hq i)))
  have event (i : S) : mcaEvent (F := F) (ReedSolomon.code dom k : Set (I → F))
      δ (rows 0) (rows 1) (label i) := by
    apply HalfPredecessorCoreFreshDecode.mcaEvent_of_affine_core_fresh
      dom k δ rows (label i) (core i) (site i) (first i) (r i)
    · exact fun he => hmis i (hcore i _ he).2.2
    · exact deg_first i
    · exact hr i
    · exact (degree_add_le _ _).trans_lt (max_lt (deg_first i) (degree_mul _ _ (hr i)))
    · exact hcard i
    · exact hsize i
    · intro x hx
      obtain ⟨heu, hev, hew⟩ := hcore i x hx
      simp [first, rows, heu, hev, hew]
    · change (first i + C (a*key i 0+b*key i 1) * r i).eval (dom (site i)) =
        a*u (site i)+b*v (site i)+(a*key i 0+b*key i 1)*w (site i)
      simp only [first, eval_add, eval_mul, eval_C]
      linear_combination a*(hkey i).1 + b*(hkey i).2
    · exact fun he => hmis i (congrArg Prod.snd he)
  have mass := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (ReedSolomon.code dom k : Set (I → F)) δ rows (univ.map label) (by
      intro z hz
      obtain ⟨i, _, rfl⟩ := mem_map.mp hz
      exact event i)
  simpa only [card_map, card_univ] using mass

#print axioms mass_of_distinct_fresh_labels

end ArkLib.ProximityGap.Frontier.LinearPencilFreshLabels
