/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-! # A rotation obstruction for saturated three-head equality patterns -/

set_option autoImplicit false
noncomputable section
open Polynomial Finset
namespace ArkLib.ProximityGap.Frontier.SaturatedTripleRotation
variable {F : Type*} [Field F]

/-- One of the three labelled pairs of difference columns `0, (a,b), (c,e)`
coincides both at `x` and at `y`. -/
def samePair (a b c e : F[X]) (x y : F) : Prop :=
  (a.eval x = 0 ∧ b.eval x = 0 ∧ a.eval y = 0 ∧ b.eval y = 0) ∨
  (c.eval x = 0 ∧ e.eval x = 0 ∧ c.eval y = 0 ∧ e.eval y = 0) ∨
  (a.eval x = c.eval x ∧ b.eval x = e.eval x ∧ a.eval y = c.eval y ∧ b.eval y = e.eval y)

private def drop (p : F[X]) (r : F) (D : ℕ) := p.comp (C r * X) - C (r^D) * p

private theorem drop_degree (p : F[X]) (r : F) {D : ℕ} (hD : 0 < D) (hp : p.natDegree ≤ D) :
    (drop p r D).natDegree < D := by
  apply Nat.lt_of_le_pred hD
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  simp only [Nat.pred_eq_sub_one] at hi
  change (p.comp (C r * X) - C (r^D) * p).coeff i = 0
  rw [coeff_sub, comp_C_mul_X_coeff, coeff_C_mul]
  by_cases h : i = D
  · subst i
    ring
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i)]
    ring

/-- If the three pair strata exhaust the determinant degree away from zero, every
rotation preserving their labels has order dividing the degree of a head. -/
theorem rotation_power {D : ℕ} (hD : 0 < D) (a b c e : F[X])
    (ha : a.natDegree ≤ D) (hb : b.natDegree ≤ D) (hc : c.natDegree ≤ D) (he : e.natDegree ≤ D)
    (hdet : a*e-c*b ≠ 0) (S : Finset F) (hs : S.card = 2*D) (h0 : 0 ∉ S) (r : F)
    (hmatch : ∀ x ∈ S, samePair a b c e x (r*x)) : r^D = 1 := by
  classical
  let P := a*e-c*b
  have hp : P.natDegree ≤ 2*D := (natDegree_sub_le ..).trans
    (max_le (natDegree_mul_le.trans (by omega)) (natDegree_mul_le.trans (by omega)))
  have roots (x : F) (hx : x ∈ S) : P.eval x = 0 := by
    rcases hmatch x hx with ⟨h₁,h₂,_,_⟩ | ⟨h₁,h₂,_,_⟩ | ⟨h₁,h₂,_,_⟩ <;>
      simp [P,h₁,h₂]
  have nz : P.eval 0 ≠ 0 := by
    intro hz
    apply hdet
    exact eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P (insert 0 S) (by
      intro x hx
      rcases mem_insert.mp hx with rfl|h
      · exact hz
      · exact roots x h) (by rw [card_insert_of_notMem h0]; omega)
  let Q := (drop a r D)*e - (drop c r D)*b
  have hqa := drop_degree a r hD ha
  have hqc := drop_degree c r hD hc
  have hq : Q.natDegree < 2*D := (natDegree_sub_le ..).trans_lt
    (max_lt (natDegree_mul_le.trans_lt (by omega)) (natDegree_mul_le.trans_lt (by omega)))
  have hQ : Q = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q S (by
    intro x hx
    rcases hmatch x hx with ⟨h₁,h₂,h₃,_⟩ | ⟨h₁,h₂,h₃,_⟩ | ⟨h₁,h₂,h₃,_⟩ <;>
      simp [Q,drop,eval_comp,h₁,h₂,h₃]) (hs ▸ hq)
  have atZero := congrArg (Polynomial.eval 0) hQ
  simp [Q,drop,eval_comp] at atZero
  have e0 : (1-r^D)*P.eval 0 = 0 := by
    dsimp [P]
    simp only [eval_sub,eval_mul]
    linear_combination atZero
  exact (sub_eq_zero.mp ((mul_eq_zero.mp e0).resolve_right nz)).symm

/-- A non-invariant rational pencil of degree at most `m` can agree with its
rotation on at most `2*m-2` nonzero coordinates. Its cross-product difference
loses the leading term and has a further root at zero. -/
theorem preserved_pencil_sites {m : ℕ} (hm : 0 < m) (A B : F[X]) (r : F)
    (ha : A.natDegree ≤ m) (hb : B.natDegree ≤ m) (S : Finset F) (h0 : 0 ∉ S)
    (hmoved : ∃ u : F, A.eval (r * u) * B.eval u ≠ B.eval (r * u) * A.eval u)
    (hmatch : ∀ x ∈ S, A.eval (r * x) * B.eval x = B.eval (r * x) * A.eval x) :
    S.card + 2 ≤ 2 * m := by
  let Q := drop A r m * B - drop B r m * A
  have hqa := drop_degree A r hm ha
  have hqb := drop_degree B r hm hb
  have hdeg : Q.natDegree < 2 * m := (natDegree_sub_le ..).trans_lt
    (max_lt (natDegree_mul_le.trans_lt (by omega)) (natDegree_mul_le.trans_lt (by omega)))
  have evalQ (x : F) :
      Q.eval x = A.eval (r * x) * B.eval x - B.eval (r * x) * A.eval x := by
    simp [Q, drop, eval_comp]
    ring
  classical
  by_contra! hsmall
  have hQ : Q = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q (insert 0 S) (by
    intro x hx
    rcases mem_insert.mp hx with rfl | h
    · simp [evalQ, mul_comm]
    · exact (evalQ x).trans (sub_eq_zero.mpr (hmatch x h))) (by
    rw [card_insert_of_notMem h0]
    omega)
  obtain ⟨u, hu⟩ := hmoved
  apply hu
  have he := evalQ u
  rw [hQ, eval_zero] at he
  exact sub_eq_zero.mp he.symm

/-- Three disjoint full fibers of a non-invariant rational pencil must change
at least `m+2` labels under a rotation. Each unchanged site lies in `S`. -/
theorem split_pencil_displacement {m lost : ℕ} (hm : 0 < m) (A B : F[X]) (r : F)
    (ha : A.natDegree ≤ m) (hb : B.natDegree ≤ m) (S : Finset F) (h0 : 0 ∉ S)
    (hmoved : ∃ u : F, A.eval (r * u) * B.eval u ≠ B.eval (r * u) * A.eval u)
    (hmatch : ∀ x ∈ S, A.eval (r * x) * B.eval x = B.eval (r * x) * A.eval x)
    (hcount : 3 * m ≤ S.card + lost) : m + 2 ≤ lost := by
  have := preserved_pencil_sites hm A B r ha hb S h0 hmoved hmatch
  omega

#print axioms split_pencil_displacement
#print axioms rotation_power
end ArkLib.ProximityGap.Frontier.SaturatedTripleRotation
