/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Polynomial.Indicator

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/
import ProximityPrize.Extensions.Data.Polynomial.Bivariate

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombination

import CompPoly.Univariate.Lagrange
import CompPoly.Univariate.ToPoly.Impl

/-! This module is mostly needed from proving lemma 4.9
  from [ACFY24] but we thought it might be useful for
  something else as well.

## References

* [Arnon, G., Chiesa, A., Fenzi, G., Yogev, E.,
  *STIR: Reed–Solomon Proximity Testing with Fewer Queries*][ACFY24]
-/

namespace Polynomial

section

open Polynomial Polynomial.Bivariate

variable {ι F : Type*} [Field F] [DecidableEq F]

section SingletonIndicator

variable {x : F}

end SingletonIndicator

end

end Polynomial

namespace CompPoly.CPolynomial.Indicator

variable {F : Type*} [Field F] [DecidableEq F]

/-- Computable indicator polynomial: a `CPolynomial` of minimal degree that takes the value `1`
on `pos` and `0` on `neg \ pos`. Mirrors `Polynomial.indicator` but is computable via CompPoly's
Lagrange interpolation. -/
def cpolyIndicator (pos neg : Finset F) : CompPoly.CPolynomial F :=
  CompPoly.CPolynomial.CLagrange.interpolate (pos ∪ neg) id
    (fun x => if x ∈ pos then 1 else 0)

/-- Bridge lemma: pushing `cpolyIndicator` through `toPoly` recovers `Polynomial.indicator`. -/
@[simp]
lemma cpolyIndicator_toPoly (pos neg : Finset F) :
    (cpolyIndicator pos neg).toPoly = Polynomial.indicator pos neg := by
  unfold cpolyIndicator Polynomial.indicator
  exact CompPoly.CPolynomial.CLagrange.cinterpolate_eq_interpolate

@[simp]
lemma cpolyIndicator_eq_zero_of_pos_empty {neg : Finset F} :
    cpolyIndicator (∅ : Finset F) neg = 0 := by
  apply (CompPoly.CPolynomial.toPoly_eq_zero_iff _).mp
  rw [cpolyIndicator_toPoly, Polynomial.indicator_eq_0_of_pos_empty]

lemma cpolyIndicator_ne_zero_of_pos_nonempty {pos neg : Finset F} (h : pos.Nonempty) :
    cpolyIndicator pos neg ≠ 0 := by
  intro contra
  apply Polynomial.indicator_ne_zero_of_pos_nonempty h
  rw [← cpolyIndicator_toPoly, contra, CompPoly.CPolynomial.toPoly_zero]

lemma cpolyIndicator_eval_eq_one_on_pos {pos neg : Finset F} {x : F} (h : x ∈ pos) :
    (cpolyIndicator pos neg).eval x = 1 := by
  rw [CompPoly.CPolynomial.eval_toPoly, cpolyIndicator_toPoly]
  exact Polynomial.indicator_eq_1_on_pos h

lemma cpolyIndicator_eval_eq_zero_on_neg_sub_pos {pos neg : Finset F} {x : F}
    (h : x ∈ neg \ pos) :
    (cpolyIndicator pos neg).eval x = 0 := by
  rw [CompPoly.CPolynomial.eval_toPoly, cpolyIndicator_toPoly]
  exact Polynomial.indicator_eq_0_on_neg_sub_pos h

lemma cpolyIndicator_degree_lt {pos neg : Finset F} :
    (cpolyIndicator pos neg).degree < (pos ∪ neg).card := by
  rw [CompPoly.CPolynomial.degree_toPoly, cpolyIndicator_toPoly]
  exact Polynomial.indicator_degree_lt

lemma cpolyIndicator_natDegree_lt_of_pos_nonempty {pos neg : Finset F} (h : pos.Nonempty) :
    (cpolyIndicator pos neg).natDegree < (pos ∪ neg).card := by
  rw [CompPoly.CPolynomial.natDegree_toPoly, cpolyIndicator_toPoly]
  exact Polynomial.indicator_natDegree_lt_of_pos_nonempty h

lemma cpolyIndicator_natDegree_lt_of_neg_nonempty {pos neg : Finset F} (h : neg.Nonempty) :
    (cpolyIndicator pos neg).natDegree < (pos ∪ neg).card := by
  rw [CompPoly.CPolynomial.natDegree_toPoly, cpolyIndicator_toPoly]
  exact Polynomial.indicator_natDegree_lt_of_neg_nonempty h

lemma cpolyIndicator_degree_lt_of_pos_subset_neg {pos neg : Finset F} (h : pos ⊆ neg) :
    (cpolyIndicator pos neg).degree < neg.card := by
  rw [CompPoly.CPolynomial.degree_toPoly, cpolyIndicator_toPoly]
  exact Polynomial.indicator_degree_lt_of_pos_subset_neg h

lemma cpolyIndicator_natDegree_lt_of_pos_nonempty_of_pos_subset_neg
    {pos neg : Finset F} (h_nonempty : pos.Nonempty) (h : pos ⊆ neg) :
    (cpolyIndicator pos neg).natDegree < neg.card := by
  rw [CompPoly.CPolynomial.natDegree_toPoly, cpolyIndicator_toPoly]
  exact Polynomial.indicator_natDegree_lt_of_pos_nonempty_of_pos_subset_neg h_nonempty h

lemma cpolyIndicator_natDegree_lt_of_neg_nonempty_of_pos_subset_neg
    {pos neg : Finset F} (h_nonempty : neg.Nonempty) (h : pos ⊆ neg) :
    (cpolyIndicator pos neg).natDegree < neg.card := by
  rw [CompPoly.CPolynomial.natDegree_toPoly, cpolyIndicator_toPoly]
  exact Polynomial.indicator_natDegree_lt_of_neg_nonempty_of_pos_subset_neg h_nonempty h

section CpolySingletonIndicator

variable {x : F}

/-- Computable singleton indicator: `cpolyIndicator {x} S`. -/
def cpolySingletonIndicator (x : F) (S : Finset F) : CompPoly.CPolynomial F :=
  cpolyIndicator {x} S

/-- Bridge lemma for `cpolySingletonIndicator`. -/
@[simp]
lemma cpolySingletonIndicator_toPoly (x : F) (S : Finset F) :
    (cpolySingletonIndicator x S).toPoly = Polynomial.singletonIndicator x S := by
  unfold cpolySingletonIndicator Polynomial.singletonIndicator
  exact cpolyIndicator_toPoly _ _

@[simp]
lemma cpolySingletonIndicator_eval_self {S : Finset F} :
    (cpolySingletonIndicator x S).eval x = 1 := by
  rw [CompPoly.CPolynomial.eval_toPoly, cpolySingletonIndicator_toPoly]
  exact Polynomial.singleton_indicator_eval_self

lemma cpolySingletonIndicator_eval_eq_zero_of_mem_sdiff {S : Finset F} {a : F}
    (h : a ∈ S \ {x}) :
    (cpolySingletonIndicator x S).eval a = 0 := by
  rw [CompPoly.CPolynomial.eval_toPoly, cpolySingletonIndicator_toPoly]
  exact Polynomial.singleton_indicator_eval_eq_zero_of_mem_sdiff h

lemma cpolySingletonIndicator_degree_lt_of_mem {S : Finset F} (h : x ∈ S) :
    (cpolySingletonIndicator x S).degree < S.card := by
  rw [CompPoly.CPolynomial.degree_toPoly, cpolySingletonIndicator_toPoly]
  exact Polynomial.singleton_indicator_degree_lt_of_mem h

lemma cpolySingletonIndicator_natDegree_lt_of_mem {S : Finset F} (h : x ∈ S) :
    (cpolySingletonIndicator x S).natDegree < S.card := by
  rw [CompPoly.CPolynomial.natDegree_toPoly, cpolySingletonIndicator_toPoly]
  exact Polynomial.singleton_indicator_natDegree_lt_of_mem h

end CpolySingletonIndicator

end CompPoly.CPolynomial.Indicator
