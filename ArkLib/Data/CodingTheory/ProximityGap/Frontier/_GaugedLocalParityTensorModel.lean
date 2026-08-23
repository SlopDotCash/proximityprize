/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportDividedDifferenceCoefficientFactorization
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TensorRowSpanCriterion

/-!
# The gauged local-parity tensor model

The global polynomial-pencil kernel has two label degrees of freedom.  Fixing two anchor
components to zero removes them.  This file projects every concrete coordinate-local parity space
onto the remaining labels and tensors it with the length-`K` Vandermonde row.  Full span of those
rows is the exact block maximal-recoverability target for anchored rigidity.
-/

set_option autoImplicit false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.GaugedLocalParityTensorModel

open SupportDividedDifferenceOperator
open SupportDividedDifferenceCoefficientFactorization
open TensorRowSpanCriterion

variable {F X J : Type} [Field F] [Fintype J] [DecidableEq J]

/-- Labels remaining after deleting the two gauge anchors. -/
abbrev NonAnchor (a b : J) := {j : J // j ≠ a ∧ j ≠ b}

/-- Restriction of a label vector to the non-anchor coordinates. -/
def restrictNonAnchor (a b : J) : (J → F) →ₗ[F] (NonAnchor a b → F) where
  toFun ell j := ell j.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Concrete coordinate-local parity space after deleting the two anchor coordinates. -/
noncomputable def gaugedLocalParitySpace
    (label : J → F) (support : X → Finset J) (a b : J) (x : X) :
    Submodule F (NonAnchor a b → F) :=
  (localParitySpace label support x).map (restrictNonAnchor a b)

/-- Every concrete divided-difference row restricts into the gauged local parity space at its
coordinate. -/
theorem restrict_labelParityVector_mem_gaugedLocalParitySpace
    (label : J → F) {support : X → Finset J} (a b : J)
    (row : SupportRow support) :
    restrictNonAnchor a b (labelParityVector label row) ∈
      gaugedLocalParitySpace label support a b row.coordinate := by
  exact Submodule.mem_map.mpr ⟨labelParityVector label row,
    labelParityVector_mem_localParitySpace label row, rfl⟩

/-- Finite Vandermonde row at one domain coordinate. -/
def vandermondeFinRow (domain : X → F) (K : Nat) (x : X) : Fin K → F :=
  fun d => domain x ^ (d : Nat)

/-- **Exact block maximal-recoverability target.**  After deleting the two gauge anchors, the
local parity spaces tensored with the explicit Vandermonde rows span every coefficient functional.
-/
def GaugedTensorSpanFull
    (domain : X → F) (label : J → F) (support : X → Finset J)
    (a b : J) (K : Nat) : Prop :=
  Submodule.span F
    (tensorRowSet (gaugedLocalParitySpace label support a b)
      (vandermondeFinRow domain K)) = ⊤

/-- Degree-`<K` coefficient array on the non-anchor polynomial components. -/
def gaugedCoeffArray (q : J → F[X]) (a b : J) (K : Nat) :
    NonAnchor a b × Fin K → F :=
  fun jd => (q jd.1.1).coeff (jd.2 : Nat)

/-- Degree-`<K` polynomial evaluation as a sum over `Fin K`. -/
theorem eval_eq_sum_fin_coeff_mul_pow
    {K : Nat} [NeZero K] (p : F[X]) (x : F)
    (hdegree : p ∈ Polynomial.degreeLT F K) :
    p.eval x = ∑ d : Fin K, p.coeff (d : Nat) * x ^ (d : Nat) := by
  have hdeg := ReedSolomon.natDegree_lt_of_mem_degreeLT hdegree
  rw [Polynomial.eval_eq_sum_range' hdeg]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro d hd
  simp [Finset.mem_range.mp hd]

/-- Tensor measurement of the gauged coefficient array is the projected parity-weighted sum of
the non-anchor polynomial evaluations. -/
theorem tensorMeasurement_gaugedCoeffArray_eq_sum_eval
    {K : Nat} [NeZero K] (domain : X → F) (q : J → F[X]) (a b : J)
    (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F K)
    (x : X) (ell : NonAnchor a b → F) :
    tensorMeasurement ell (vandermondeFinRow domain K x) (gaugedCoeffArray q a b K) =
      ∑ j : NonAnchor a b, ell j * (q j.1).eval (domain x) := by
  simp only [tensorMeasurement, tensorRow, gaugedCoeffArray, vandermondeFinRow]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [eval_eq_sum_fin_coeff_mul_pow (q j.1) (domain x) (hdegree j.1), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  ring

/-- Sum over the non-anchor subtype as a filtered sum over all labels. -/
theorem sum_nonAnchor_eq_filter (a b : J) (f : J → F) :
    (∑ j : NonAnchor a b, f j.1) =
      ∑ j ∈ Finset.univ.filter (fun j : J => j ≠ a ∧ j ≠ b), f j := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun j : J => j ≠ a ∧ j ≠ b))
    (fun j => by simp) f]

/-- Removing two zero summands does not change a finite sum. -/
theorem sum_filter_nonAnchor_eq_sum (a b : J) (f : J → F)
    (hfa : f a = 0) (hfb : f b = 0) :
    (∑ j ∈ Finset.univ.filter (fun j : J => j ≠ a ∧ j ≠ b), f j) = ∑ j, f j := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j _hjUniv hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not] at hj
  rcases hj with rfl | rfl
  · exact hfa
  · exact hfb

/-- Under the two-anchor gauge, projected tensor measurement is exactly the original full local
parity evaluation measurement. -/
theorem tensorMeasurement_gaugedCoeffArray_eq_parityEvalMeasurement
    {K : Nat} [NeZero K] (domain : X → F) (q : J → F[X]) (a b : J)
    (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F K)
    (hqa : q a = 0) (hqb : q b = 0)
    (x : X) (ell : J → F) :
    tensorMeasurement (restrictNonAnchor a b ell) (vandermondeFinRow domain K x)
        (gaugedCoeffArray q a b K) =
      parityEvalMeasurement domain q x ell := by
  rw [tensorMeasurement_gaugedCoeffArray_eq_sum_eval domain q a b hdegree x]
  change (∑ j : NonAnchor a b, ell j.1 * (q j.1).eval (domain x)) =
    parityEvalMeasurement domain q x ell
  calc
    (∑ j : NonAnchor a b, ell j.1 * (q j.1).eval (domain x)) =
        ∑ j ∈ Finset.univ.filter (fun j : J => j ≠ a ∧ j ≠ b),
          ell j * (q j).eval (domain x) :=
      sum_nonAnchor_eq_filter a b (fun j => ell j * (q j).eval (domain x))
    _ = ∑ j, ell j * (q j).eval (domain x) :=
      sum_filter_nonAnchor_eq_sum a b (fun j => ell j * (q j).eval (domain x))
        (by simp [hqa]) (by simp [hqb])
    _ = parityEvalMeasurement domain q x ell := rfl

/-- The gauged tensor-span target kills every non-anchor coefficient array whose local tensor
measurements vanish. -/
theorem gaugedCoeffArray_eq_zero_of_spanFull
    (domain : X → F) (label : J → F) (support : X → Finset J)
    (a b : J) (K : Nat)
    (hspan : GaugedTensorSpanFull domain label support a b K)
    (q : J → F[X])
    (hzero : ∀ x ell, ell ∈ gaugedLocalParitySpace label support a b x →
      tensorMeasurement ell (vandermondeFinRow domain K x)
        (gaugedCoeffArray q a b K) = 0) :
    gaugedCoeffArray q a b K = 0 := by
  exact eq_zero_of_tensorRowSpan_eq_top
    (gaugedLocalParitySpace label support a b)
    (vandermondeFinRow domain K) hspan (gaugedCoeffArray q a b K) hzero

/-- Vanishing of the full gauged coefficient array makes every non-anchor degree-`<K` polynomial
zero. -/
theorem polynomial_eq_zero_of_gaugedCoeffArray_eq_zero
    {K : Nat} [NeZero K] (q : J → F[X]) (a b : J)
    (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F K)
    (hcoeff : gaugedCoeffArray q a b K = 0) :
    ∀ j, j ≠ a → j ≠ b → q j = 0 := by
  intro j hja hjb
  apply Polynomial.ext
  intro n
  by_cases hn : n < K
  · let j' : NonAnchor a b := ⟨j, hja, hjb⟩
    let d : Fin K := ⟨n, hn⟩
    have hz := congrFun hcoeff (j', d)
    simpa [gaugedCoeffArray, j', d] using hz
  · have hdeg := ReedSolomon.natDegree_lt_of_mem_degreeLT (hdegree j)
    rw [Polynomial.coeff_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg (Nat.le_of_not_gt hn))

/-- **Gauged tensor span gives anchored rigidity.**  Under degree bounds, global operator-kernel
membership and two zero anchors force the entire polynomial family to vanish. -/
theorem polynomial_family_eq_zero_of_gaugedTensorSpanFull
    {K : Nat} [NeZero K]
    (domain : X → F) (label : J → F) (support : X → Finset J)
    {a b : J} (hspan : GaugedTensorSpanFull domain label support a b K)
    (q : J → F[X]) (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F K)
    (hkernel : q ∈ (supportDividedDifference domain support label).ker)
    (hqa : q a = 0) (hqb : q b = 0) :
    q = 0 := by
  have hlocal := parityEvalMeasurement_eq_zero_of_mem_ker
    domain support label q hkernel
  have htensor : ∀ x ell,
      ell ∈ gaugedLocalParitySpace label support a b x →
      tensorMeasurement ell (vandermondeFinRow domain K x)
        (gaugedCoeffArray q a b K) = 0 := by
    intro x ell hell
    obtain ⟨fullEll, hfullEll, hrestrict⟩ := Submodule.mem_map.mp hell
    rw [← hrestrict]
    rw [tensorMeasurement_gaugedCoeffArray_eq_parityEvalMeasurement
      domain q a b hdegree hqa hqb x fullEll]
    exact hlocal x fullEll hfullEll
  have hcoeff := gaugedCoeffArray_eq_zero_of_spanFull
    domain label support a b K hspan q htensor
  have hnonAnchor := polynomial_eq_zero_of_gaugedCoeffArray_eq_zero
    q a b hdegree hcoeff
  funext j
  by_cases hja : j = a
  · subst j
    exact hqa
  by_cases hjb : j = b
  · subst j
    exact hqb
  exact hnonAnchor j hja hjb

end ArkLib.ProximityGap.Frontier.GaugedLocalParityTensorModel

#print axioms ArkLib.ProximityGap.Frontier.GaugedLocalParityTensorModel.restrict_labelParityVector_mem_gaugedLocalParitySpace
#print axioms ArkLib.ProximityGap.Frontier.GaugedLocalParityTensorModel.gaugedCoeffArray_eq_zero_of_spanFull
#print axioms ArkLib.ProximityGap.Frontier.GaugedLocalParityTensorModel.polynomial_eq_zero_of_gaugedCoeffArray_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.GaugedLocalParityTensorModel.tensorMeasurement_gaugedCoeffArray_eq_parityEvalMeasurement
#print axioms ArkLib.ProximityGap.Frontier.GaugedLocalParityTensorModel.polynomial_family_eq_zero_of_gaugedTensorSpanFull
