/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier._P1RateQuarterCommonFactorOneStepNoGo

/-! # A full edge of a planar quartet forces a scalar pencil

Projection along the constant direction of a saturated edge identifies its two heads.
The three remaining projected heads are distinct and give a scalar pencil on the
unions of incident coincidence sites.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SaturatedQuartetFullEdge

open Polynomial
open P1RateQuarterCommonFactorOneStepNoGo

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Equality of the two rows at one site. -/
def meets (A B : Fin 4 → F[X]) (i j : Fin 4) (x : F) : Prop :=
  (A i).eval x = (A j).eval x ∧ (B i).eval x = (B j).eval x

/-- A full edge between heads two and three supplies a scalar pencil with prescribed roots
on the opposite edge and on the two unions joining one of the remaining heads to that edge. -/
theorem projected_pencil (A B : Fin 4 → F[X]) (d : ℕ)
    (degreeA : ∀ i, (A i).natDegree ≤ d) (degreeB : ∀ i, (B i).natDegree ≤ d)
    (E T S U : Finset F) (full : E.card = d) (enough : d < (S ∪ U).card)
    (atE : ∀ x ∈ E, meets A B 2 3 x) (atT : ∀ x ∈ T, meets A B 0 1 x)
    (atS : ∀ x ∈ S, meets A B 0 2 x ∨ meets A B 0 3 x)
    (atU : ∀ x ∈ U, meets A B 1 2 x ∨ meets A B 1 3 x)
    (triangle : ∀ i ∈ ({0, 1} : Finset (Fin 4)),
      (A i - A 2)*(B 2 - B 3) - (B i - B 2)*(A 2 - A 3) ≠ 0) :
    ∃ P Q : F[X], P ≠ 0 ∧ Q ≠ 0 ∧ Q - P ≠ 0 ∧ P.natDegree ≤ d ∧ Q.natDegree ≤ d ∧
      (∀ x ∈ T, P.eval x = 0) ∧ (∀ x ∈ S, Q.eval x = 0) ∧
      (∀ x ∈ U, (Q - P).eval x = 0) := by
  let emb := Function.Embedding.refl F
  obtain ⟨a, ha⟩ := eq_C_mul_domainRootProduct_of_saturated_roots emb
    (K0 := d+1) (by omega) (A 2 - A 3) E
    (Nat.lt_succ_of_le ((natDegree_sub_le ..).trans (max_le (degreeA _) (degreeA _))))
    (by simpa using full) (fun x hx => by simpa [emb] using sub_eq_zero.mpr (atE x hx).1)
  obtain ⟨b, hb⟩ := eq_C_mul_domainRootProduct_of_saturated_roots emb
    (K0 := d+1) (by omega) (B 2 - B 3) E
    (Nat.lt_succ_of_le ((natDegree_sub_le ..).trans (max_le (degreeB _) (degreeB _))))
    (by simpa using full) (fun x hx => by simpa [emb] using sub_eq_zero.mpr (atE x hx).2)
  let f (i : Fin 4) := C b * A i - C a * B i
  have bounds (i : Fin 4) : (f i).natDegree ≤ d :=
    (natDegree_sub_le ..).trans <| max_le ((natDegree_C_mul_le ..).trans (degreeA i))
      ((natDegree_C_mul_le ..).trans (degreeB i))
  have same : f 2 = f 3 := by
    apply sub_eq_zero.mp
    calc
      f 2 - f 3 = C b * (A 2 - A 3) - C a * (B 2 - B 3) := by dsimp [f]; ring
      _ = 0 := by rw [ha, hb]; ring
  have different (i : Fin 4) (hi : i ∈ ({0, 1} : Finset (Fin 4))) : f i ≠ f 2 := by
    intro he
    apply triangle i hi
    calc
      _ = (f i - f 2) *
          HalfPredecessorRateQuarterOverlapThreeFactorization.domainRootProduct emb E := by
        rw [ha, hb]; dsimp [f]; ring
      _ = 0 := by simp [he]
  have agree {i j : Fin 4} {x : F} (h : meets A B i j x) : (f i).eval x = (f j).eval x := by
    simp [f, h.1, h.2]
  have atSide (i : Fin 4) (V : Finset F) (h : ∀ x ∈ V, meets A B i 2 x ∨ meets A B i 3 x) :
      ∀ x ∈ V, (f 2 - f i).eval x = 0 := by
    intro x hx
    rcases h x hx with h2 | h3
    · simp [agree h2]
    · simp [same, agree h3]
  have s := atSide 0 S atS
  have u := atSide 1 U atU
  have nd (i j : Fin 4) : (f i - f j).natDegree ≤ d :=
    (natDegree_sub_le ..).trans (max_le (bounds i) (bounds j))
  have distinct : f 1 ≠ f 0 := by
    intro eq
    have eq' := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (f 2 - f 0) (S ∪ U)
      (fun x hx => (Finset.mem_union.mp hx).elim (s x) (by simpa [eq] using u x))
      ((nd 2 0).trans_lt enough)
    exact different 0 (by simp) (sub_eq_zero.mp eq').symm
  have cancel : f 2 - f 0 - (f 1 - f 0) = f 2 - f 1 := by ring
  refine ⟨f 1 - f 0, f 2 - f 0, sub_ne_zero.mpr distinct,
    sub_ne_zero.mpr (different 0 (by simp)).symm, ?_, nd .., nd .., ?_, s, ?_⟩
  · rw [cancel]
    exact sub_ne_zero.mpr (different 1 (by simp)).symm
  · intro x hx
    simp [agree (atT x hx)]
  · simpa [cancel] using u

end ArkLib.ProximityGap.Frontier.SaturatedQuartetFullEdge
