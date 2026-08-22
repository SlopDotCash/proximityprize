/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Projective injectivity of rank-one function tensors

The radix lift replaces each base defect functional `d_j` by the family

```text
d_j tensor (1,x,...,x^(m-1)).
```

This file proves the elementary but load-bearing fact that projective
distinctness of the base factors and injectivity of the normalized Vandermonde
factors imply projective distinctness of every lifted pair `(j,x)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.RankOneTensorProjectiveInjection

variable {F A B J Xidx : Type} [Field F]

/-- The coordinate realization of a rank-one tensor. -/
def outer (f : A -> F) (g : B -> F) : A × B -> F :=
  fun pair => f pair.1 * g pair.2

/-- Equality of two nonzero rank-one tensors up to scale forces the left
factors to be projectively proportional. -/
theorem left_proportional_of_outer_eq_smul
    (f f' : A -> F) (g g' : B -> F) (c : F)
    (hg : g ≠ 0)
    (heq : outer f g = c • outer f' g') :
    exists a : F, f = a • f' := by
  obtain ⟨b, hb⟩ : exists b, g b ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (funext h)
  refine ⟨c * g' b / g b, ?_⟩
  funext x
  have hx := congrFun heq (x, b)
  simp only [outer, Pi.smul_apply, smul_eq_mul] at hx ⊢
  field_simp
  linear_combination hx

/-- **Rank-one projective injection.**  If the base factors are pairwise
projectively distinct, the fiber factors are injective, and all fiber factors
share a coordinate equal to one, then `(j,x) |-> f_j tensor g_x` is itself
projectively injective. -/
theorem outer_projectively_injective
    (f : J -> A -> F) (g : Xidx -> B -> F) (anchor : B)
    (hf : forall j, f j ≠ 0)
    (hfproj : forall i j, (exists c : F, f i = c • f j) -> i = j)
    (hgAnchor : forall x, g x anchor = 1)
    (hginj : Function.Injective g) :
    forall (i j : J) (x y : Xidx) (c : F),
      outer (f i) (g x) = c • outer (f j) (g y) -> i = j ∧ x = y := by
  intro i j x y c heq
  have hgx : g x ≠ 0 := by
    intro hzero
    have := congrFun hzero anchor
    simp [hgAnchor x] at this
  have hij : i = j :=
    hfproj i j (left_proportional_of_outer_eq_smul (f i) (f j) (g x) (g y) c hgx heq)
  subst j
  have hc : c = 1 := by
    obtain ⟨a, ha⟩ : exists a, f i a ≠ 0 := by
      by_contra h
      push Not at h
      exact hf i (funext h)
    have hanchor := congrFun heq (a, anchor)
    simp only [outer, hgAnchor, mul_one, Pi.smul_apply, smul_eq_mul] at hanchor
    apply mul_right_cancel₀ ha
    simpa using hanchor.symm
  subst c
  have hgxy : g x = g y := by
    funext b
    obtain ⟨a, ha⟩ : exists a, f i a ≠ 0 := by
      by_contra h
      push Not at h
      exact hf i (funext h)
    have hb := congrFun heq (a, b)
    simp only [outer, one_smul] at hb
    exact (mul_left_cancel₀ ha) hb
  exact ⟨rfl, hginj hgxy⟩

/-- The normalized Vandermonde vector used on an `m`-point fiber. -/
def vandermonde (m : Nat) (x : F) : Fin m -> F :=
  fun b => x ^ (b : Nat)

@[simp] theorem vandermonde_zero (m : Nat) (hm : 0 < m) (x : F) :
    vandermonde m x ⟨0, hm⟩ = 1 := by
  simp [vandermonde]

/-- For `m>=2`, normalized Vandermonde vectors remember their base point in
coordinate one. -/
theorem vandermonde_injective (m : Nat) (hm : 2 ≤ m) :
    Function.Injective (vandermonde (F := F) m) := by
  intro x y hxy
  have hone := congrFun hxy ⟨1, hm⟩
  simpa [vandermonde] using hone

/-- Projective injectivity specialized to the radix Vandermonde family. -/
theorem outer_vandermonde_projectively_injective
    (m : Nat) (hm : 2 ≤ m) (f : J -> A -> F)
    (hf : forall j, f j ≠ 0)
    (hfproj : forall i j, (exists c : F, f i = c • f j) -> i = j) :
    forall (i j : J) (x y c : F),
      outer (f i) (vandermonde m x) =
        c • outer (f j) (vandermonde m y) -> i = j ∧ x = y := by
  apply outer_projectively_injective f (vandermonde m) ⟨0, lt_of_lt_of_le (by norm_num) hm⟩
    hf hfproj
  · intro x
    exact vandermonde_zero m (lt_of_lt_of_le (by norm_num) hm) x
  · exact vandermonde_injective m hm

end ArkLib.ProximityGap.Frontier.RankOneTensorProjectiveInjection

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RankOneTensorProjectiveInjection
#print axioms left_proportional_of_outer_eq_smul
#print axioms outer_projectively_injective
#print axioms outer_vandermonde_projectively_injective
