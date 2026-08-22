/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# A maximal-minor ideal certificate for universal full column rank

A single chosen block-Vandermonde minor can vanish even when the full support-dependent operator
has full column rank.  The algebraic consumer therefore allows a family of maximal minors.  If a
power of a discriminant element `delta` is a linear combination of that family, then every
specialization where `delta` stays nonzero preserves at least one nonzero maximal minor, hence full
column rank.

For the proximity-prize application, the coefficient ring is the polynomial ring in scalar
labels, `delta` is their Vandermonde product, and the minors are square row selections from the
symbolic gauged support-divided-difference operator.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.MaximalMinorIdealCertificate

/-- Vandermonde product over the canonical ordering of a finite label index type. -/
def vandermondeProduct {E J : Type} [CommRing E] [Fintype J] [LinearOrder J]
    (label : J → E) : E :=
  ∏ i : J, ∏ j ∈ (Finset.univ.filter fun j : J => i < j), (label j - label i)

/-- Pairwise-distinct labels make the Vandermonde product nonzero. -/
theorem vandermondeProduct_ne_zero
    {E J : Type} [CommRing E] [IsDomain E] [Fintype J] [LinearOrder J]
    (label : J → E) (hlabel : Function.Injective label) :
    vandermondeProduct label ≠ 0 := by
  unfold vandermondeProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro i _hi
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hij : i < j := (Finset.mem_filter.mp hj).2
  exact sub_ne_zero.mpr (hlabel.ne (ne_of_gt hij))

/-- The symbolic Vandermonde polynomial in the label variables. -/
noncomputable def symbolicVandermonde {F J : Type} [CommRing F] [Fintype J] [LinearOrder J] :
    MvPolynomial J F :=
  vandermondeProduct (fun j => MvPolynomial.X j)

/-- Evaluating the symbolic Vandermonde at concrete labels gives their Vandermonde product. -/
theorem eval₂Hom_symbolicVandermonde
    {F E J : Type} [CommRing F] [CommRing E] [Fintype J] [LinearOrder J]
    (coeff : F →+* E) (label : J → E) :
    MvPolynomial.eval₂Hom coeff label (symbolicVandermonde (F := F) (J := J)) =
      vandermondeProduct label := by
  simp [symbolicVandermonde, vandermondeProduct]

/-- A Bézout identity for a power of `delta` forces at least one generator to remain nonzero
under every specialization where `delta` remains nonzero. -/
theorem exists_map_generator_ne_zero_of_pow_mem_span
    {R E S : Type} [CommRing R] [Field E] [Fintype S]
    (phi : R →+* E) (delta : R) (exponent : Nat)
    (generator coefficient : S → R)
    (hcertificate : delta ^ exponent = ∑ s, coefficient s * generator s)
    (hdelta : phi delta ≠ 0) :
    ∃ s, phi (generator s) ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hzero : phi (delta ^ exponent) = 0 := by
    rw [hcertificate, map_sum]
    simp [hnone]
  rw [map_pow] at hzero
  exact pow_ne_zero exponent hdelta hzero

/-- A nonzero square row-selection minor makes the full rectangular matrix injective on column
vectors. -/
theorem mulVec_injective_of_submatrix_det_ne_zero
    {E Rows Cols : Type} [Field E]
    [Fintype Rows] [Fintype Cols] [DecidableEq Cols]
    (M : Matrix Rows Cols E) (select : Cols → Rows)
    (hdet : (M.submatrix select id).det ≠ 0) :
    Function.Injective M.mulVec := by
  have hunit : IsUnit (M.submatrix select id).det :=
    (isUnit_iff_ne_zero.mpr hdet)
  have hminorInjective : Function.Injective (M.submatrix select id).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((M.submatrix select id).isUnit_iff_isUnit_det.mpr hunit)
  intro v w hvw
  apply hminorInjective
  funext c
  simpa [Matrix.mulVec] using congrFun hvw (select c)

/-- **Maximal-minor ideal consumer.**  A power-of-discriminant certificate over the coefficient
ring implies full column rank after every specialization on which the discriminant is nonzero.

No single row selection is privileged: the surviving minor may depend on the specialization. -/
theorem mulVec_injective_of_maximalMinor_certificate
    {R E Rows Cols S : Type} [CommRing R] [Field E]
    [Fintype Rows] [Fintype Cols] [DecidableEq Cols] [Fintype S]
    (phi : R →+* E) (M : Matrix Rows Cols R) (select : S → Cols → Rows)
    (coefficient : S → R) (delta : R) (exponent : Nat)
    (hcertificate :
      delta ^ exponent =
        ∑ s, coefficient s * (M.submatrix (select s) id).det)
    (hdelta : phi delta ≠ 0) :
    Function.Injective (M.map phi).mulVec := by
  obtain ⟨s, hs⟩ := exists_map_generator_ne_zero_of_pow_mem_span
    phi delta exponent (fun s => (M.submatrix (select s) id).det) coefficient
      hcertificate hdelta
  apply mulVec_injective_of_submatrix_det_ne_zero (M.map phi) (select s)
  change ((M.submatrix (select s) id).map phi).det ≠ 0
  simpa only [RingHom.map_det] using hs

/-- Distinct-label specialization form of the maximal-minor consumer.  Once the symbolic
discriminant maps to the concrete Vandermonde product, injectivity of the labels discharges the
nonvanishing premise automatically. -/
theorem mulVec_injective_of_maximalMinor_certificate_of_injective_labels
    {R E Rows Cols S J : Type} [CommRing R] [Field E]
    [Fintype Rows] [Fintype Cols] [DecidableEq Cols] [Fintype S]
    [Fintype J] [LinearOrder J]
    (phi : R →+* E) (M : Matrix Rows Cols R) (select : S → Cols → Rows)
    (coefficient : S → R) (delta : R) (exponent : Nat)
    (label : J → E) (hlabel : Function.Injective label)
    (hdeltaMap : phi delta = vandermondeProduct label)
    (hcertificate :
      delta ^ exponent =
        ∑ s, coefficient s * (M.submatrix (select s) id).det) :
    Function.Injective (M.map phi).mulVec := by
  apply mulVec_injective_of_maximalMinor_certificate
    phi M select coefficient delta exponent hcertificate
  rw [hdeltaMap]
  exact vandermondeProduct_ne_zero label hlabel

/-- Fully specialized symbolic-label consumer.  A Bézout identity for a power of the symbolic
Vandermonde implies full column rank at every injective concrete label assignment. -/
theorem mulVec_injective_of_symbolicVandermonde_certificate
    {F E Rows Cols S J : Type} [CommRing F] [Field E]
    [Fintype Rows] [Fintype Cols] [DecidableEq Cols] [Fintype S]
    [Fintype J] [LinearOrder J]
    (coeffMap : F →+* E) (label : J → E) (hlabel : Function.Injective label)
    (M : Matrix Rows Cols (MvPolynomial J F))
    (select : S → Cols → Rows) (coefficient : S → MvPolynomial J F) (exponent : Nat)
    (hcertificate :
      symbolicVandermonde (F := F) (J := J) ^ exponent =
        ∑ s, coefficient s * (M.submatrix (select s) id).det) :
    Function.Injective (M.map (MvPolynomial.eval₂Hom coeffMap label)).mulVec := by
  apply mulVec_injective_of_maximalMinor_certificate_of_injective_labels
    (MvPolynomial.eval₂Hom coeffMap label) M select coefficient
      (symbolicVandermonde (F := F) (J := J)) exponent label hlabel
      (eval₂Hom_symbolicVandermonde coeffMap label) hcertificate

end ArkLib.ProximityGap.Frontier.MaximalMinorIdealCertificate

open ArkLib.ProximityGap.Frontier.MaximalMinorIdealCertificate

#print axioms exists_map_generator_ne_zero_of_pow_mem_span
#print axioms mulVec_injective_of_submatrix_det_ne_zero
#print axioms mulVec_injective_of_maximalMinor_certificate
#print axioms vandermondeProduct_ne_zero
#print axioms mulVec_injective_of_maximalMinor_certificate_of_injective_labels
#print axioms eval₂Hom_symbolicVandermonde
#print axioms mulVec_injective_of_symbolicVandermonde_certificate
