/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarChartCancellation
import ArkLib.Research.ProximityGap.Frontier.ApolarReciprocalCharts

/-! # Descending a reciprocal identity and exchanging the two variables -/

set_option autoImplicit false
open Polynomial
namespace ProximityGap.ApolarChartDescent
open ArkLib.ProximityGap.Frontier.ApolarReciprocalCharts
open ApolarChartCancellation

variable {K L : Type*} [Field K]

/-- Reversing the coordinate and then interchanging the two variables
reverses each coordinate coefficient polynomial. -/
theorem swap_reflect (m : ℕ) (p : K[X][X]) :
    Bivariate.swap (reflect m p) = reverseCoeffs m (Bivariate.swap p) := by
  ext j k
  simp only [swap_coeff,coeff_reflect,coeff_reverseCoeffs]

/-- The coordinate degree of an interpolation remainder falls below the locator
degree, for either sign of the difference between the two reciprocal powers. -/
theorem small_degree_from_cleared (f B B' : K[X][X]) {n a : ℕ} (hpos : 0 < f.natDegree)
    (htwist : n < a + f.natDegree)
    (hb : (Bivariate.swap B).natDegree < (Bivariate.swap f).natDegree)
    (hb' : (Bivariate.swap B').natDegree < (Bivariate.swap f).natDegree)
    (h : ∀ b c, b + a = n + c →
      Bivariate.swap f ∣ C (X^b) * reverseCoeffs B'.natDegree (Bivariate.swap B') -
        C (X^(B'.natDegree+c)) * Bivariate.swap B) :
    B.natDegree < f.natDegree := by
  have hm (j : ℕ) : ((Bivariate.swap B').coeff j).natDegree ≤ B'.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [swap_coeff,coeff_eq_zero_of_natDegree_lt hk,coeff_zero]
  by_cases he : a ≤ n
  · have hc := h (n-a) 0 (by omega)
    simp only [Nat.add_zero] at hc
    have hdeg := swapped_degree hb hb' hm hc
    rw [Bivariate.swap_swap_apply] at hdeg
    omega
  · have hc := h 0 (a-n) (by omega)
    rw [pow_zero] at hc
    obtain ⟨hzero,_⟩ := negative_twist (by omega : 0<a-n) hb hb' hm hc
    have hz : B=0 := Bivariate.swap.injective (by simpa using hzero)
    simpa only [hz,natDegree_zero] using hpos

variable [IsAlgClosed K] [Field L] [Algebra K[X] L] [IsFractionRing K[X] L]

/-- Evaluate the two cleared remainders at the universal generic root.
Their equality there is sufficient for the divisibility in the parameter chart. -/
theorem descend_compare (f B B' : K[X][X]) (m a b : ℕ)
    (hf : ∀ t : K, f.map (evalRingHom t) ≠ 0)
    (he : let φ := algebraMap K[X] L
          let F := f.map φ
          (AdjoinRoot.root F)^a * AdjoinRoot.mk F ((reflect m B').map φ) =
            (AdjoinRoot.root F)^b * AdjoinRoot.mk F (B.map φ)) :
    Bivariate.swap f ∣ C (X^a)*reverseCoeffs m (Bivariate.swap B') - C (X^b)*Bivariate.swap B := by
  have hh : f ∣ X^a*reflect m B'-X^b*B := by
    apply descend_root_identity (L := L) _ _ hf
    simpa only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_pow,map_X,
      map_sub,map_mul,map_pow,AdjoinRoot.mk_X,sub_eq_zero] using he
  obtain ⟨q,hq⟩ := hh
  refine ⟨Bivariate.swap q,?_⟩
  have h := congrArg Bivariate.swap hq
  simpa only [map_sub,map_mul,map_pow,Bivariate.swap_Y,swap_reflect,C_pow] using h

#print axioms small_degree_from_cleared
#print axioms descend_compare
end ProximityGap.ApolarChartDescent
