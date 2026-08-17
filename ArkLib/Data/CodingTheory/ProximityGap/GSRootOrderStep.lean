/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-!
Round 14 (own-token brick) — the GS/Sudan ROOT-ORDER step in general form:
agreement count + weighted-degree bound ⟹ (Y − f) ∣ Q.
Self-contained, Mathlib-only.
-/

open Polynomial

namespace GSRootOrder

variable {F : Type*} [Field F]

/-- **Weighted-degree transfer.** If every outer coefficient of `Q : Polynomial (Polynomial F)`
obeys the weighted-degree bound `deg_X(coeff_j) + j·(k−1) < D`, and `deg f ≤ k−1`, then the
univariate restriction `Q(X, f(X)) = Q.eval f` has degree `< D`. -/
theorem natDegree_eval_lt {Q : Polynomial (Polynomial F)} {f : Polynomial F} {k D : ℕ}
    (hD : 0 < D)
    (hwdeg : ∀ j, Q.coeff j ≠ 0 → (Q.coeff j).natDegree + j * (k - 1) < D)
    (hf : f.natDegree ≤ k - 1) :
    (Q.eval f).natDegree < D := by
  have hterm : ∀ j ∈ Q.support, (Q.coeff j * f ^ j).natDegree ≤ D - 1 := by
    intro j hj
    have hcj : Q.coeff j ≠ 0 := mem_support_iff.mp hj
    have h1 : (Q.coeff j * f ^ j).natDegree ≤ (Q.coeff j).natDegree + (f ^ j).natDegree :=
      natDegree_mul_le
    have h2 : (f ^ j).natDegree ≤ j * f.natDegree := natDegree_pow_le
    have h3 : j * f.natDegree ≤ j * (k - 1) := Nat.mul_le_mul_left j hf
    have h4 : (Q.coeff j).natDegree + j * (k - 1) < D := hwdeg j hcj
    omega
  calc (Q.eval f).natDegree
      = (∑ j ∈ Q.support, Q.coeff j * f ^ j).natDegree := by
        rw [eval_eq_sum]; rfl
    _ ≤ D - 1 := natDegree_sum_le_of_forall_le _ _ hterm
    _ < D := by omega

/-- **The root-order / factor step (Sudan, multiplicity 1).**  Let
`Q : Polynomial (Polynomial F)` satisfy the weighted-degree bound `< D`, and let `f` be a
polynomial of degree `≤ k−1` such that
`Q(α, f(α)) = 0` for all `α` in a set `A` of at least `D` points (the **agreement points**: at each
the received word equals `f`, and `Q` vanishes there).  Then the univariate `Q(X, f(X))` has `≥ D`
roots but degree `< D`, hence is zero — so **`(Y − f) ∣ Q`** in the outer polynomial ring.

This is the middle step of the Guruswami–Sudan pipeline, in general form: it converts an agreement
count into a polynomial factor, feeding the `Y`-degree list cap. -/
theorem factor_of_agreement {Q : Polynomial (Polynomial F)} {f : Polynomial F} {k D : ℕ}
    (hD : 0 < D)
    (hwdeg : ∀ j, Q.coeff j ≠ 0 → (Q.coeff j).natDegree + j * (k - 1) < D)
    (hf : f.natDegree ≤ k - 1)
    {A : Finset F} (hA : D ≤ A.card)
    (hroot : ∀ α ∈ A, (Q.eval f).eval α = 0) :
    (X - C f) ∣ Q := by
  classical
  rw [dvd_iff_isRoot]
  -- `IsRoot Q f` means `Q.eval f = 0`.  Suppose not; count roots.
  by_contra hne
  have hne' : Q.eval f ≠ 0 := hne
  -- every α ∈ A is a root of the nonzero univariate `Q.eval f`
  have hsub : A ⊆ (Q.eval f).roots.toFinset := by
    intro α hα
    rw [Multiset.mem_toFinset, mem_roots']
    exact ⟨hne', hroot α hα⟩
  have hcard : A.card ≤ (Q.eval f).natDegree := by
    calc A.card ≤ (Q.eval f).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (Q.eval f).roots := Multiset.toFinset_card_le _
      _ ≤ (Q.eval f).natDegree := card_roots' _
  have hlt : (Q.eval f).natDegree < D := natDegree_eval_lt hD hwdeg hf
  omega

/-! ## Non-vacuity: a concrete instance where the factor step fires. -/

/-- **Non-vacuity.**  Over `F = ℚ`, take `Q = Y` (the outer variable, a genuine nonzero bivariate),
`f = 0` (degree `0 ≤ k−1 = 1`), `D = 2`, and `A = {0, 1}` (two agreement points).  The weighted-degree
hypothesis holds (`Q`'s only nonzero coefficient is at `j = 1`, with `deg 1 + 1·1 = 1 < 2`); the
agreement hypothesis holds (`Q(X, 0) = 0` vanishes everywhere).  `factor_of_agreement` fires and
concludes `(Y − C 0) ∣ Y` — exercising every hypothesis concretely. -/
theorem nonvacuous_rat : ((X : Polynomial (Polynomial ℚ)) - C 0) ∣ X := by
  have hwdeg : ∀ j, ((X : Polynomial (Polynomial ℚ))).coeff j ≠ 0 →
      (((X : Polynomial (Polynomial ℚ))).coeff j).natDegree + j * (2 - 1) < 2 := by
    intro j hj
    rw [coeff_X] at hj ⊢
    by_cases h1 : (1 : ℕ) = j
    · rw [if_pos h1]
      subst h1
      simp
    · exact absurd (if_neg h1) hj
  have hA : ({0, 1} : Finset ℚ).card = 2 := by
    rw [Finset.card_pair (by norm_num : (0 : ℚ) ≠ 1)]
  exact factor_of_agreement (k := 2) (D := 2) (by norm_num) hwdeg
    (by simp)
    (A := ({0, 1} : Finset ℚ)) (by rw [hA])
    (fun α _ => by simp)

end GSRootOrder

#print axioms GSRootOrder.natDegree_eval_lt
#print axioms GSRootOrder.factor_of_agreement
#print axioms GSRootOrder.nonvacuous_rat
