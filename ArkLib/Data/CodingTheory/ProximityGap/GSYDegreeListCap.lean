/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
Round 14 — Angle A: the Y-DEGREE LIST CAP, the algebraic endgame of the
Guruswami–Sudan list-decoding argument (ABF26 / ArkLib #232 context).

Statement: let `F` be a field and `Q : (F[X])[Y]` (encoded as
`Polynomial (Polynomial F)`, outer variable = Y) a NONZERO bivariate polynomial.
If `S` is a finite set of univariate polynomials `f : F[X]` such that
`(Y - C f) ∣ Q` for every `f ∈ S`, then `S.card ≤ Q.natDegree` (= deg_Y Q).

This is exactly the step that converts "every close codeword's polynomial is a
Y-root of the interpolated Q" into the LIST-SIZE bound `|List| ≤ deg_Y Q` in
Guruswami–Sudan.  Proof route: push Q along the injective ring hom
`F[X] → RatFunc F` (coefficientwise); over the field `RatFunc F` each `f ∈ S`
becomes a genuine root of the (still nonzero) image of Q, distinct `f` give
distinct roots by injectivity, and a nonzero polynomial over a field has at
most `natDegree` distinct roots.

Non-vacuity: a concrete instance with `Q = (Y - C X)(Y - C (X+1))` over ℚ and
the two-element root set `S = {X, X+1}` is constructed below, with the cap
attained with equality (2 ≤ 2).

What is NOT proven here: this file does not construct the GS interpolation
polynomial Q, does not relate deg_Y Q to the agreement parameter t and the
weighted degree, and says nothing about pushing past the Johnson radius.  It is
the reusable algebraic cap only.
-/
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Roots

open Polynomial

namespace R14

variable {F : Type*} [Field F]

/-- **Y-degree list cap.**  If `Q ≠ 0` in `(F[X])[Y]` and every `f` in the
finite set `S ⊆ F[X]` gives a linear factor `Y - C f` of `Q`, then
`|S| ≤ deg_Y Q`.  (Here the outer `Polynomial.X` plays the role of `Y`.) -/
theorem card_le_natDegreeY_of_sub_C_dvd
    (Q : Polynomial (Polynomial F)) (hQ : Q ≠ 0)
    (S : Finset (Polynomial F))
    (hdvd : ∀ f ∈ S, (X - C f) ∣ Q) :
    S.card ≤ Q.natDegree := by
  classical
  -- the injective coefficient embedding F[X] ↪ F(X)
  set φ : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F) with hφdef
  have hφ : Function.Injective φ := RatFunc.algebraMap_injective F
  -- push Q into F(X)[Y]
  set Q' : Polynomial (RatFunc F) := Q.map φ with hQ'def
  have hQ'ne : Q' ≠ 0 := by
    intro h
    exact hQ (Polynomial.map_injective φ hφ (by simpa [hQ'def] using h))
  -- every f ∈ S maps to a root of Q'
  have hroot : ∀ f ∈ S, φ f ∈ Q'.roots := by
    intro f hf
    have hdvd' : (X - C (φ f)) ∣ Q' := by
      have h1 := map_dvd (Polynomial.mapRingHom φ) (hdvd f hf)
      simpa [Polynomial.coe_mapRingHom, Polynomial.map_sub] using h1
    rw [Polynomial.mem_roots hQ'ne]
    exact Polynomial.dvd_iff_isRoot.mp hdvd'
  -- distinct f give distinct roots; count them
  have hsub : S.image (fun f => φ f) ⊆ Q'.roots.toFinset := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨f, hf, rfl⟩
    exact Multiset.mem_toFinset.mpr (hroot f hf)
  calc S.card
      = (S.image (fun f => φ f)).card :=
        (Finset.card_image_of_injective S hφ).symm
    _ ≤ Q'.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card Q'.roots := Q'.roots.toFinset_card_le
    _ ≤ Q'.natDegree := Q'.card_roots'
    _ = Q.natDegree := Polynomial.natDegree_map_eq_of_injective hφ Q

/-! ### Non-vacuity witness

A concrete `Q` of Y-degree 2 over ℚ with a two-element factor set:
`Q = (Y - C X) * (Y - C (X + 1))`, `S = {X, X + 1}`.  All hypotheses of the
cap theorem are inhabited and the bound is attained with equality. -/

/-- The witness bivariate polynomial `(Y - C X)(Y - C (X+1))` over ℚ. -/
noncomputable def Qwit : Polynomial (Polynomial ℚ) :=
  (X - C Polynomial.X) * (X - C (Polynomial.X + 1))

/-- The witness root set `{X, X + 1} ⊆ ℚ[X]`. -/
noncomputable def Swit : Finset (Polynomial ℚ) :=
  {Polynomial.X, Polynomial.X + 1}

lemma X_ne_X_add_one : (Polynomial.X : Polynomial ℚ) ≠ Polynomial.X + 1 := by
  intro h
  have h0 := congrArg (Polynomial.eval (0 : ℚ)) h
  simp at h0

lemma Qwit_ne_zero : Qwit ≠ 0 :=
  mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _)

lemma Swit_card : Swit.card = 2 :=
  Finset.card_pair X_ne_X_add_one

lemma Qwit_natDegree : Qwit.natDegree = 2 := by
  rw [Qwit, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _)
    (Polynomial.X_sub_C_ne_zero _), Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_sub_C]

lemma Swit_dvd : ∀ f ∈ Swit, (X - C f) ∣ Qwit := by
  intro f hf
  rcases Finset.mem_insert.mp hf with rfl | hf
  · exact Dvd.intro _ rfl
  · rcases Finset.mem_singleton.mp hf with rfl
    exact Dvd.intro_left _ rfl

/-- The cap theorem applied to the explicit witness: the hypotheses are
inhabited and the bound `2 ≤ 2` is attained with equality, so the main theorem
is non-vacuous. -/
theorem cap_attained : Swit.card ≤ Qwit.natDegree ∧
    Swit.card = 2 ∧ Qwit.natDegree = 2 :=
  ⟨card_le_natDegreeY_of_sub_C_dvd Qwit Qwit_ne_zero Swit Swit_dvd,
   Swit_card, Qwit_natDegree⟩

end R14

#print axioms R14.card_le_natDegreeY_of_sub_C_dvd
#print axioms R14.cap_attained
