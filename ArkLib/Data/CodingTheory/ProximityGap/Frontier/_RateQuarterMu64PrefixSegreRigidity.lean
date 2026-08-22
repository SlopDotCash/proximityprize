/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Affine-line rigidity for prefix-factor coefficient tensors

The degree-fifteen locator of a disjoint `8+4+2+1` union of dyadic cosets in
`mu_64` has the form

`(X^8-a₈)(X^4-a₄)(X^2-a₂)(X-a₁)`.

Because `8,4,2,1` have unique subset sums, its coefficient vector is the
four-factor binary Segre tensor: singleton coefficient coordinates are the
four parameters and pair coordinates are their pairwise products (up to
fixed signs).

This file isolates the field-universal algebraic rigidity behind that
observation.  If three such tensors are affinely collinear with a non-endpoint
parameter, then the two endpoint parameter tuples differ in at most one
coordinate.  In the locator application they therefore share at least three
binomial factors, so they cannot have disjoint root sets.

The exact executable P1 census goes further: it allows the third locator to
be completely unstructured.  That finite census is deliberately not claimed
as a Lean theorem here.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.RateQuarterMu64PrefixSegreRigidity

attribute [local instance] Classical.propDecidable

variable {F index : Type} [Field F]

/-- A nontrivial affine combination preserving two singleton coordinates and
their product forces at least one endpoint coordinate to agree.  This is the
two-by-two quadric equation cutting out the Segre variety. -/
theorem affineSegre_two_coordinate_rigidity
    (lambda ai aj bi bj ci cj : F)
    (hlambda_zero : lambda ≠ 0) (hlambda_one : lambda ≠ 1)
    (hi : bi = lambda * ai + (1 - lambda) * ci)
    (hj : bj = lambda * aj + (1 - lambda) * cj)
    (hij : bi * bj =
      lambda * (ai * aj) + (1 - lambda) * (ci * cj)) :
    ai = ci ∨ aj = cj := by
  have hone_sub : 1 - lambda ≠ 0 := sub_ne_zero.mpr (Ne.symm hlambda_one)
  have hproduct :
      lambda * (1 - lambda) * (ai - ci) * (aj - cj) = 0 := by
    rw [hi, hj] at hij
    calc
      lambda * (1 - lambda) * (ai - ci) * (aj - cj) =
          -(lambda * ai + (1 - lambda) * ci) *
              (lambda * aj + (1 - lambda) * cj) +
            (lambda * (ai * aj) + (1 - lambda) * (ci * cj)) := by
              ring
      _ = 0 := by linear_combination -hij
  have hcoordinate : (ai - ci) * (aj - cj) = 0 := by
    have hproduct' :
        (lambda * (1 - lambda)) * ((ai - ci) * (aj - cj)) = 0 := by
      simpa only [mul_assoc] using hproduct
    exact (mul_eq_zero.mp hproduct').resolve_left
      (mul_ne_zero hlambda_zero hone_sub)
  rcases mul_eq_zero.mp hcoordinate with hi_zero | hj_zero
  · exact Or.inl (sub_eq_zero.mp hi_zero)
  · exact Or.inr (sub_eq_zero.mp hj_zero)

/-- **A line meets the binary Segre tensor in three non-endpoint points only
along one factor direction.**  Under affine compatibility of every singleton
and pair coordinate, the two endpoint tuples differ at no more than one
index. -/
theorem affineSegre_changedCoordinates_card_le_one
    [Fintype index] [DecidableEq index]
    (a b c : index → F) (lambda : F)
    (hlambda_zero : lambda ≠ 0) (hlambda_one : lambda ≠ 1)
    (hsingle : ∀ i,
      b i = lambda * a i + (1 - lambda) * c i)
    (hpair : ∀ i j, i ≠ j →
      b i * b j =
        lambda * (a i * a j) + (1 - lambda) * (c i * c j)) :
    (Finset.univ.filter fun i => a i ≠ c i).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro i j hi hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  by_contra hij
  exact (affineSegre_two_coordinate_rigidity lambda
    (a i) (a j) (b i) (b j) (c i) (c j)
    hlambda_zero hlambda_one (hsingle i) (hsingle j) (hpair i j hij)).elim hi hj

/-- Pointwise-distinct endpoints in two named factor directions already
contradict affine Segre compatibility.  This is the form used when disjoint
same-size cosets make the corresponding factor parameters unequal. -/
theorem not_affineSegre_of_two_changed_coordinates
    (a b c : index → F) (lambda : F)
    (hlambda_zero : lambda ≠ 0) (hlambda_one : lambda ≠ 1)
    (hsingle : ∀ i,
      b i = lambda * a i + (1 - lambda) * c i)
    (hpair : ∀ i j, i ≠ j →
      b i * b j =
        lambda * (a i * a j) + (1 - lambda) * (c i * c j))
    (i j : index) (hij : i ≠ j)
    (hi : a i ≠ c i) (hj : a j ≠ c j) : False := by
  exact (affineSegre_two_coordinate_rigidity lambda
    (a i) (a j) (b i) (b j) (c i) (c j)
    hlambda_zero hlambda_one (hsingle i) (hsingle j) (hpair i j hij)).elim hi hj

end ArkLib.ProximityGap.Frontier.RateQuarterMu64PrefixSegreRigidity

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateQuarterMu64PrefixSegreRigidity
#print axioms affineSegre_two_coordinate_rigidity
#print axioms affineSegre_changedCoordinates_card_le_one
#print axioms not_affineSegre_of_two_changed_coordinates
