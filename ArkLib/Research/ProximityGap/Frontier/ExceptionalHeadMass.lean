/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.LinearPencilFreshLabels
import Mathlib.LinearAlgebra.Lagrange

/-! # One omitted root for each polynomial head

A common root block has one exceptional site for each head. Ordinary sites carry
the value of an actual or virtual head. Two explicit scalar coordinates recover
the fresh site and the foreign head.
-/

open Finset Polynomial ProximityGap
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.ExceptionalHeadMass

variable {F I A : Type} [Field F] [Fintype F] [Fintype I] [Nonempty I]
variable [Fintype A] [DecidableEq I] [DecidableEq F]

/-- The defining sites of the head omitting the root at `a i`. -/
def core (dom : I ↪ F) (base : Finset I) (a : A ↪ I) (owner : I → F) (i : A) : Finset I :=
  base.erase (a i) ∪ univ.filter (fun x => x ∉ base ∧ owner x = dom (a i))

/-- Every site outside each defining core contributes one distinct literal MCA-bad scalar. -/
theorem mass (dom : I ↪ F) (base : Finset I) (a : A ↪ I) (owner : I → F)
    (δ : ℝ≥0) (u k : ℕ) (ha : ∀ i, a i ∈ base) (hbase : base.card = k)
    (ho : ∀ x, dom x ≠ owner x) (hc : ∀ i, (core dom base a owner i).card = u)
    (hk : k ≤ u) (hsize : (1 - δ) * (Fintype.card I : ℝ≥0) ≤ ((u + 1 : ℕ) : ℝ≥0))
    (hfield : (Fintype.card A * (Fintype.card I - u)).choose 2 ≤ Nat.card F) :
    ((Fintype.card A * (Fintype.card I - u) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  classical
  let D := core dom base a owner
  let S := (i : A) × ↥((D i)ᶜ)
  let x (s : S) : I := s.2.val
  let z (s : S) := dom (x s)
  let v (s : S) := dom (a s.1)
  let c (s : S) := owner (x s)
  let T := Lagrange.nodal base (fun y => dom y)
  let Q (i : A) := Lagrange.nodal (base.erase (a i)) (fun y => dom y)
  let w (y : I) := if y ∈ base then 0 else T.eval (dom y) / (dom y - owner y)
  let key (s : S) : Fin 2 → F := ![-z s, -((v s + c s) * z s - v s * c s)]
  have hcard : Fintype.card S = Fintype.card A * (Fintype.card I - u) := by
    simp [S, D, Fintype.card_sigma, hc]
  have Qprod (i : A) (y : I) : (dom y - dom (a i)) * (Q i).eval (dom y) = T.eval (dom y) := by
    simpa only [T, Q, eval_mul, eval_sub, eval_X, eval_C] using
      congrArg (eval (dom y)) (Lagrange.nodal_eq_mul_nodal_erase (v := fun t => dom t) (ha i)).symm
  have wprod (y : I) : (dom y - owner y) * w y = T.eval (dom y) := by
    by_cases hy : y ∈ base
    · simp [w, hy, T, Lagrange.eval_nodal_at_node hy]
    · simpa only [w, ite_eq_right hy, mul_comm (dom y - owner y)] using
        div_mul_cancel₀ (T.eval (dom y)) (sub_ne_zero.mpr (ho y))
  have coreValues (i : A) (y : I) (hy : y ∈ D i) :
      (Q i).eval (dom y) = w y ∧ dom (a i) * w y = owner y * w y ∧
        dom (a i) ^ 2 * w y = owner y ^ 2 * w y := by
    rcases mem_union.mp hy with he | he
    · have hz : (Q i).eval (dom y) = 0 := Lagrange.eval_nodal_at_node he
      simp [w, (mem_erase.mp he).2, hz]
    · have hv := (mem_filter.mp he).2.2
      have hr := (Qprod i y).trans (wprod y).symm
      rw [← hv] at hr
      exact ⟨mul_left_cancel₀ (sub_ne_zero.mpr (ho y)) hr, hv ▸ rfl, hv ▸ rfl⟩
  have fresh (s : S) : (Q s.1).eval (z s) ≠ w (x s) := by
    have hnot : x s ∉ D s.1 := mem_compl.mp s.2.property
    have hne : (Q s.1).eval (z s) ≠ 0 := by
      apply Lagrange.eval_nodal_not_at_node
      intro j hj he
      exact hnot (dom.injective he ▸ mem_union_left _ hj)
    intro heq
    by_cases hx : x s ∈ base
    · exact hne (heq.trans (by simp [w, hx]))
    · have hrel := (Qprod s.1 (x s)).trans (wprod (x s)).symm
      change _ * (Q s.1).eval (z s) = _ * w (x s) at hrel
      rw [← heq] at hrel
      have hv := sub_right_inj.mp (mul_right_cancel₀ hne hrel)
      exact hnot (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hx, hv.symm⟩))
  have deg (i : A) : (Q i).degree < (k : WithBot ℕ) := by
    apply degree_le_natDegree.trans_lt
    have hkpos : 0 < base.card := card_pos.mpr ⟨_, ha i⟩
    change ((Lagrange.nodal (base.erase (a i)) (fun y => dom y)).natDegree : WithBot ℕ) < _
    rw [Lagrange.natDegree_nodal, card_erase_of_mem (ha i), hbase]
    exact_mod_cast (by omega : k - 1 < k)
  have degC (b : F) (i : A) : (C b * Q i).degree < (k : WithBot ℕ) := by
    by_cases hz : b = 0
    · simp [hz]
    · simpa [degree_C_mul hz] using deg i
  have hinj : Function.Injective key := by
    rintro ⟨i, y⟩ ⟨j, y'⟩ he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    simp only [key, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      neg_inj, z, v, c, x] at h0 h1
    have hxy := dom.injective h0
    rw [← hxy] at h1
    have hm : (dom (a i) - dom (a j)) * (dom y.val - owner y.val) = 0 := by
      linear_combination h1
    have hij := a.injective (dom.injective (sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right
      (sub_ne_zero.mpr (ho y.val)))))
    subst j
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hxy))
  have raw := LinearPencilFreshLabels.mass_of_distinct_fresh_labels dom k δ
    (fun s : S => D s.1) x (fun s => C (v s) * Q s.1) (fun s => C (v s ^ 2) * Q s.1)
    (fun s => Q s.1) (fun y => owner y * w y) (fun y => owner y ^ 2 * w y) w key
    (fun _ => degC _ _) (fun _ => degC _ _) (fun s => deg s.1)
    (by
      intro s y hy
      obtain ⟨hw, h1, h2⟩ := coreValues s.1 y hy
      simpa only [eval_mul, eval_C, v, hw, and_true] using And.intro h1 h2)
    (fun s => (hc s.1).symm ▸ hk)
    (fun s => by simpa only [D, hc] using hsize)
    fresh
    (by
      intro s
      have hrel := (Qprod s.1 (x s)).trans (wprod (x s)).symm
      change (z s - v s) * (Q s.1).eval (z s) = (z s - c s) * w (x s) at hrel
      simp only [key, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        eval_mul, eval_C]
      change -z s * (_ - _) = c s * _ - v s * _ ∧
        -((v s + c s) * z s - v s * c s) * (_ - _) = c s ^ 2 * _ - v s ^ 2 * _
      constructor
      · linear_combination -hrel
      · linear_combination -(v s + c s) * hrel)
    hinj (hcard.symm ▸ hfield)
  simpa only [hcard] using raw

end ArkLib.ProximityGap.Frontier.ExceptionalHeadMass

#print axioms ArkLib.ProximityGap.Frontier.ExceptionalHeadMass.mass
