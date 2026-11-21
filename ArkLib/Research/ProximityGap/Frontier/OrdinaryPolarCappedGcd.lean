/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.OrdinaryPolarGcdBudget

/-! # Upper coordinate-degree bounds for the ordinary polar gcd

Unimodular additions over the coordinate polynomial ring raise both degrees to
the common cap, preserving the scalar heights, common divisors, and each
specialized square divisor.
-/

set_option autoImplicit false
noncomputable section
open Polynomial
namespace ArkLib.ProximityGap.Frontier.OrdinaryPolarCappedGcd
open OrdinaryPolarGcdBudget
variable {K : Type} [Field K]

private theorem degree_swap (A B : K[X][X]) : genericDegree B A = genericDegree A B := by
  classical
  simp only [genericDegree, gcd_comm (B.map _) (A.map _)]

private theorem degree_shear (A B T : K[X][X]) (hB : B ≠ 0) :
    genericDegree (A+T*B) B = genericDegree A B := by
  classical
  let φ := algebraMap K[X] (FractionRing K[X])
  let a := A.map φ
  let b := B.map φ
  let t := T.map φ
  have hb : b ≠ 0 := by simpa [b] using (map_injective φ (IsFractionRing.injective _ _)).ne hB
  change (GCDMonoid.gcd ((A+T*B).map φ) b).natDegree = (GCDMonoid.gcd a b).natDegree
  rw [Polynomial.map_add, Polynomial.map_mul]
  change (GCDMonoid.gcd (a+t*b) b).natDegree = (GCDMonoid.gcd a b).natDegree
  apply le_antisymm
  · apply natDegree_le_of_dvd _ (gcd_ne_zero_of_right hb)
    apply dvd_gcd _ (gcd_dvd_right ..)
    have hd := dvd_sub (gcd_dvd_left (a+t*b) b)
      (dvd_mul_of_dvd_right (gcd_dvd_right (a+t*b) b) t)
    simpa using hd
  · apply natDegree_le_of_dvd _ (gcd_ne_zero_of_right hb)
    exact dvd_gcd (dvd_add (gcd_dvd_left ..) (dvd_mul_of_dvd_right (gcd_dvd_right ..) _)) (gcd_dvd_right ..)

private theorem raise_left (A B : K[X][X]) (D H : ℕ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAD : A.natDegree ≤ D) (hBD : B.natDegree ≤ D)
    (hAH : Bivariate.degreeX A ≤ H) (hBH : Bivariate.degreeX B ≤ H) :
    ∃ A' : K[X][X], A' ≠ 0 ∧ A'.natDegree = D ∧ Bivariate.degreeX A' ≤ H ∧
      genericDegree A' B = genericDegree A B ∧
      ∀ z : K, ∀ q : K[X], q ∣ A.map (evalRingHom z) → q ∣ B.map (evalRingHom z) →
        q ∣ A'.map (evalRingHom z) := by
  by_cases h : A.natDegree = D
  · exact ⟨A,hA,h,hAH,rfl,fun _ _ h _ => h⟩
  let e := D-B.natDegree
  let A' := A+(Polynomial.X (R := K[X]))^e*B
  have ht : ((Polynomial.X (R := K[X]))^e*B).natDegree = D := by rw [natDegree_X_pow_mul e hB]; dsimp [e]; omega
  have hA' : A'.natDegree = D := (natDegree_add_eq_right_of_natDegree_lt (by omega)).trans ht
  have hne : A' ≠ 0 := by intro hz; rw [hz,natDegree_zero] at hA'; omega
  refine ⟨A',hne,hA',?_,degree_shear A B _ hB,?_⟩
  · unfold Bivariate.degreeX
    apply Finset.sup_le
    intro j _
    change ((A+(Polynomial.X (R := K[X]))^e*B).coeff j).natDegree ≤ H
    rw [coeff_add, coeff_X_pow_mul' B e j]
    apply natDegree_add_le_of_degree_le ((Bivariate.coeff_natDegree_le_degreeX A _).trans hAH)
    split_ifs
    · exact (Bivariate.coeff_natDegree_le_degreeX B _).trans hBH
    · simp
  · intro z q ha hb
    change q ∣ (A+(Polynomial.X (R := K[X]))^e*B).map _
    rw [Polynomial.map_add,Polynomial.map_mul]
    exact dvd_add ha (dvd_mul_of_dvd_right hb _)

/-- Both input coordinate degrees may be strictly smaller than the common cap. -/
theorem gcd_budget (A B : K[X][X]) (hA : A ≠ 0) (hB : B ≠ 0) (D H J : ℕ)
    (hAD : A.natDegree ≤ D) (hBD : B.natDegree ≤ D)
    (hAH : Bivariate.degreeX A ≤ H) (hBH : Bivariate.degreeX B ≤ H) (hD : 3*J ≤ D)
    (S : Finset K) (q : K → K[X])
    (hw : ∀ z ∈ S, q z ≠ 0 ∧ (q z).natDegree = J ∧
      q z^2 ∣ A.map (evalRingHom z) ∧ q z^2 ∣ B.map (evalRingHom z)) :
    S.card*(2*J-genericDegree A B) ≤ 2*(D-genericDegree A B)*H := by
  obtain ⟨A',ha,had,hah,hga,hqa⟩ := raise_left A B D H hA hB hAD hBD hAH hBH
  obtain ⟨B',hb,hbd,hbh,hgb,hqb⟩ := raise_left B A' D H hB ha hBD had.le hBH hah
  have hg : genericDegree B' A' = genericDegree A B := hgb.trans ((degree_swap A' B).trans hga)
  rw [← hg]
  apply OrdinaryPolarGcdBudget.gcd_budget B' A' hb ha D H J hbd had hbh hah hD
  intro z hz
  obtain ⟨hne,hd,hAz,hBz⟩ := hw z hz
  have hA'z := hqa z _ hAz hBz
  exact ⟨hne,hd,hqb z _ hBz hA'z,hA'z⟩

/-- The terminal ordinary-polar estimate uses the two upper degree bounds alone. -/
theorem production_gcd_lower (A B : K[X][X]) (hA : A ≠ 0) (hB : B ≠ 0) (w : ℕ)
    (hw : 201326589 ≤ w) (hw' : w ≤ 290805098)
    (hAD : A.natDegree ≤ 6*w-9*67108863-3) (hBD : B.natDegree ≤ 6*w-9*67108863-3)
    (hAH : Bivariate.degreeX A ≤ 195) (hBH : Bivariate.degreeX B ≤ 195)
    (S : Finset K) (hS : 1342177085 ≤ S.card) (q : K → K[X])
    (hq : ∀ z ∈ S, q z ≠ 0 ∧ (q z).natDegree = w-67108863 ∧
      q z^2 ∣ A.map (evalRingHom z) ∧ q z^2 ∣ B.map (evalRingHom z)) :
    2*(w-67108863) ≤ genericDegree A B + 201 := by
  have H := gcd_budget A B hA hB _ 195 (w-67108863) hAD hBD hAH hBH (by omega) S q hq
  have H' := (Nat.mul_le_mul_right (2*(w-67108863)-genericDegree A B) hS).trans H
  omega

#print axioms gcd_budget
#print axioms production_gcd_lower
end ArkLib.ProximityGap.Frontier.OrdinaryPolarCappedGcd
