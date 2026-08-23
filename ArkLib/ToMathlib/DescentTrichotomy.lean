/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The descent trichotomy — value-level converse-FRI fold (issue #232)

The even/odd (FRI-fold) descent at a pair of points `±y` (research note `07-DESCENT.md`;
DISPROOF_LOG O13″): any pair of target values `(w₊, w₋)` has unique even/odd components
`w± = w_e ± y·w_o`, and for candidate components `(c_e, c_o)` evaluated at `z = y²`:

* **both-agreement** at `±y` ⟺ `c_e = w_e ∧ c_o = w_o` (a joint/correlated event);
* **exactly-one-sided agreement** at `+y` ⟺ the σ-twisted relation
  `c_e − w_e = −y·(c_o − w_o)` with `c_o ≠ w_o`.

Together with `TwistedKernel.lean` (kernel rigidity) these are the rigorous ingredients of the
descent recursion: agreement counts at level 0 equal `2·#both + #one-sided` over the descended
points, with both-agreements forcing joint constraints and one-sided agreements forcing twisted
affine relations. Stated at the value level (field algebra only) for maximal reusability.
-/

namespace ArkLib.SmoothDomain

variable {F : Type*} [Field F]

/-- Every pair of values at `±y` has unique even/odd components (`y ≠ 0`, `char ≠ 2`). -/
theorem descent_components_exist_unique (h2 : (2 : F) ≠ 0) {y : F} (hy : y ≠ 0)
    (wp wm : F) : ∃! ew : F × F, wp = ew.1 + y * ew.2 ∧ wm = ew.1 - y * ew.2 := by
  refine ⟨((wp + wm) / 2, (wp - wm) / (2 * y)), ⟨?_, ?_⟩, ?_⟩
  · field_simp; ring
  · field_simp; ring
  rintro ⟨we, wo⟩ ⟨h1, h2'⟩
  have hwe : we = (wp + wm) / 2 := by rw [h1, h2']; field_simp; ring
  have hwo : wo = (wp - wm) / (2 * y) := by rw [h1, h2']; field_simp; ring
  simp [hwe, hwo]

/-- Agreement at `+y` in descended coordinates. -/
theorem agree_plus_iff (y ce co we wo : F) :
    ce + y * co = we + y * wo ↔ ce - we = -(y * (co - wo)) := by
  constructor <;> intro h <;> linear_combination h

/-- Agreement at `−y` in descended coordinates. -/
theorem agree_minus_iff (y ce co we wo : F) :
    ce - y * co = we - y * wo ↔ ce - we = y * (co - wo) := by
  constructor <;> intro h <;> linear_combination h

/-- **Both-agreement** at `±y` holds iff the even/odd components match exactly. -/
theorem agree_both_iff (h2 : (2 : F) ≠ 0) {y : F} (hy : y ≠ 0) (ce co we wo : F) :
    (ce + y * co = we + y * wo ∧ ce - y * co = we - y * wo) ↔ (ce = we ∧ co = wo) := by
  constructor
  · rintro ⟨hp, hm⟩
    have hco : co = wo := by
      have h := sub_eq_zero.mpr hp
      have h' := sub_eq_zero.mpr hm
      have h2y : (2 : F) * y * (co - wo) = 0 := by linear_combination h - h'
      rcases mul_eq_zero.mp h2y with h0 | h0
      · rcases mul_eq_zero.mp h0 with h0' | h0'
        · exact absurd h0' h2
        · exact absurd h0' hy
      · exact sub_eq_zero.mp h0
    have hce : ce = we := by
      have := agree_plus_iff y ce co we wo |>.mp hp
      rw [hco] at this
      simp only [sub_self, neg_zero, mul_zero] at this
      exact sub_eq_zero.mp this
    exact ⟨hce, hco⟩
  · rintro ⟨h1, h2'⟩; subst h1; subst h2'; exact ⟨rfl, rfl⟩

/-- **Exactly-one-sided agreement** at `+y` iff the twisted relation holds with `co ≠ wo`. -/
theorem agree_exactly_plus_iff (h2 : (2 : F) ≠ 0) {y : F} (hy : y ≠ 0) (ce co we wo : F) :
    (ce + y * co = we + y * wo ∧ ce - y * co ≠ we - y * wo) ↔
      (ce - we = -(y * (co - wo)) ∧ co ≠ wo) := by
  rw [agree_plus_iff]
  constructor
  · rintro ⟨hp, hm⟩
    refine ⟨hp, fun hco => hm ?_⟩
    rw [hco] at hp ⊢
    simp only [sub_self, mul_zero, neg_zero] at hp
    rw [sub_eq_zero.mp hp]
  · rintro ⟨hp, hco⟩
    refine ⟨hp, fun hm => hco ?_⟩
    have h' := (agree_minus_iff y ce co we wo).mp hm
    have h2y : (2 : F) * (y * (co - wo)) = 0 := by linear_combination hp - h'
    rcases mul_eq_zero.mp h2y with h0 | h0
    · exact absurd h0 h2
    · rcases mul_eq_zero.mp h0 with h0' | h0'
      · exact absurd h0' hy
      · exact sub_eq_zero.mp h0'


/-! ## Polynomial-level form (the recomposed candidate `c_e(X²) + X·c_o(X²)`) -/

open Polynomial

/-- Level-0 evaluation of the recomposed polynomial at `±y` in terms of the components. -/
theorem eval_recompose (c_e c_o : F[X]) (y : F) :
    (c_e.comp (X ^ 2) + X * c_o.comp (X ^ 2)).eval y
      = c_e.eval (y ^ 2) + y * c_o.eval (y ^ 2) := by
  simp [eval_add, eval_mul, eval_comp, eval_pow, eval_X]

/-- **Polynomial-level descent: both-agreement.** The recomposed polynomial agrees with the word
at both `±y` iff the components hit the word's even/odd components at `z = y²`. -/
theorem poly_agree_both_iff (h2 : (2 : F) ≠ 0) {y : F} (hy : y ≠ 0)
    (c_e c_o : F[X]) (we wo : F) :
    ((c_e.comp (X ^ 2) + X * c_o.comp (X ^ 2)).eval y = we + y * wo ∧
     (c_e.comp (X ^ 2) + X * c_o.comp (X ^ 2)).eval (-y) = we - y * wo) ↔
    (c_e.eval (y ^ 2) = we ∧ c_o.eval (y ^ 2) = wo) := by
  rw [eval_recompose, eval_recompose]
  rw [show ((-y) ^ 2 : F) = y ^ 2 by ring]
  rw [show (c_e.eval (y ^ 2) + -y * c_o.eval (y ^ 2) = we - y * wo)
        ↔ (c_e.eval (y ^ 2) - y * c_o.eval (y ^ 2) = we - y * wo) by
      constructor <;> intro h <;> linear_combination h]
  exact agree_both_iff h2 hy _ _ we wo

/-- **Polynomial-level descent: exactly-one-sided agreement** at `+y`. -/
theorem poly_agree_exactly_plus_iff (h2 : (2 : F) ≠ 0) {y : F} (hy : y ≠ 0)
    (c_e c_o : F[X]) (we wo : F) :
    ((c_e.comp (X ^ 2) + X * c_o.comp (X ^ 2)).eval y = we + y * wo ∧
     (c_e.comp (X ^ 2) + X * c_o.comp (X ^ 2)).eval (-y) ≠ we - y * wo) ↔
    (c_e.eval (y ^ 2) - we = -(y * (c_o.eval (y ^ 2) - wo)) ∧ c_o.eval (y ^ 2) ≠ wo) := by
  rw [eval_recompose, eval_recompose]
  rw [show ((-y) ^ 2 : F) = y ^ 2 by ring]
  have hiff : (c_e.eval (y ^ 2) + -y * c_o.eval (y ^ 2) ≠ we - y * wo)
      ↔ (c_e.eval (y ^ 2) - y * c_o.eval (y ^ 2) ≠ we - y * wo) :=
    not_congr (by constructor <;> intro h <;> linear_combination h)
  rw [hiff]
  exact agree_exactly_plus_iff h2 hy _ _ we wo


end ArkLib.SmoothDomain

#print axioms ArkLib.SmoothDomain.descent_components_exist_unique
#print axioms ArkLib.SmoothDomain.agree_both_iff
#print axioms ArkLib.SmoothDomain.agree_exactly_plus_iff
