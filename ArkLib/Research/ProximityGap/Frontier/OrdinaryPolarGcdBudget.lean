/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.OrdinaryPolarRankLoss
import ArkLib.Research.ProximityGap.Frontier.IntegralCommonPolar
import ArkLib.Research.ProximityGap.Frontier.CanonicalQuarticSiteOrder

/-! # A persistent coordinate divisor from many selected polynomial sections

Remove the actual primitive generic gcd of the two polars, then compare the
residual resultant's scalar degree with its zeros at the selected labels.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace ArkLib.ProximityGap.Frontier.OrdinaryPolarGcdBudget

variable {K : Type} [Field K]

/-- Degree of the actual gcd in the generic scalar fiber. -/
def genericDegree (A B : K[X][X]) : ℕ := by
  classical
  let φ := algebraMap K[X] (FractionRing K[X])
  exact (GCDMonoid.gcd (A.map φ) (B.map φ)).natDegree

/-- Selected fibers whose common divisor is a square force a large generic
coordinate gcd when the two original scalar heights are small. -/
theorem gcd_budget (A B : K[X][X]) (hA : A ≠ 0) (hB : B ≠ 0) (D H J : ℕ)
    (hAD : A.natDegree = D) (hBD : B.natDegree = D)
    (hAH : Bivariate.degreeX A ≤ H) (hBH : Bivariate.degreeX B ≤ H) (hD : 3*J ≤ D)
    (S : Finset K) (q : K → K[X])
    (hw : ∀ z ∈ S, q z ≠ 0 ∧ (q z).natDegree = J ∧
      q z^2 ∣ A.map (evalRingHom z) ∧ q z^2 ∣ B.map (evalRingHom z)) :
    S.card*(2*J-genericDegree A B) ≤ 2*(D-genericDegree A B)*H := by
  classical
  let φ := algebraMap K[X] (FractionRing K[X])
  have hφ := IsFractionRing.injective K[X] (FractionRing K[X])
  obtain ⟨E,F,G,hE,hAF,hBG,hd,hco⟩ := IntegralCommonPolar.remove_generic_gcd
    (L := FractionRing K[X]) A B hA
  change E.natDegree = genericDegree A B at hd
  have hf : F ≠ 0 := fun h => hA (by simp [hAF,h])
  have hg : G ≠ 0 := fun h => hB (by simp [hBG,h])
  let u := D-E.natDegree
  have hfu : F.natDegree = u := by
    rw [hAF,natDegree_mul hE.ne_zero hf] at hAD
    dsimp [u]; omega
  have hgu : G.natDegree = u := by
    rw [hBG,natDegree_mul hE.ne_zero hg] at hBD
    dsimp [u]; omega
  have hres : F.resultant G u u ≠ 0 := by
    have hn := resultant_ne_zero (F.map φ) (G.map φ) hco
    have hfφ : (F.map φ).natDegree = u := (natDegree_map_eq_of_injective hφ F).trans hfu
    have hgφ : (G.map φ).natDegree = u := (natDegree_map_eq_of_injective hφ G).trans hgu
    rw [hfφ,hgφ,resultant_map_map] at hn
    exact fun h => hn (by simp [h])
  have hdeg : (F.resultant G u u).natDegree ≤ 2*u*H := by
    rw [hAF,Bivariate.degreeX_mul E F hE.ne_zero hf] at hAH
    rw [hBG,Bivariate.degreeX_mul E G hE.ne_zero hg] at hBH
    have hh := WeightedHessianResultant.weighted_resultant_le F G u u 0 H H
      (fun j _ => by have := Bivariate.coeff_natDegree_le_degreeX F j; omega)
      (fun j _ => by have := Bivariate.coeff_natDegree_le_degreeX G j; omega)
    simpa [two_mul,add_mul] using hh
  rw [← hd]
  by_cases hl : 2*J ≤ E.natDegree
  · simp [Nat.sub_eq_zero_of_le hl]
  have ha : ∀ z ∈ S, q z^2 ∣ E.map (evalRingHom z)*F.map (evalRingHom z) := by
    intro z hz
    simpa [hAF] using (hw z hz).2.2.1
  have hb : ∀ z ∈ S, q z^2 ∣ E.map (evalRingHom z)*G.map (evalRingHom z) := by
    intro z hz
    simpa [hBG] using (hw z hz).2.2.2
  exact (OrdinaryPolarRankLoss.residual_degree_budget F G S (fun z => E.map (evalRingHom z)) q
    u J E.natDegree hfu.le hgu.le hres
    (fun z hz => ⟨(hw z hz).2.1,natDegree_map_le⟩)
    (fun z hz => ⟨CanonicalQuarticSiteOrder.primitive_fiber_ne_zero E hE z,(hw z hz).1⟩)
    (fun _ _ => by dsimp [u]; omega) ha hb).trans hdeg

/-- The ordinary first-polar divisor misses at most 201 orders at the least
terminal population. This is uniform through the full cubic weight range. -/
theorem production_gcd_lower (A B : K[X][X]) (hA : A ≠ 0) (hB : B ≠ 0) (w : ℕ)
    (hw : 201326589 ≤ w) (hw' : w ≤ 290805098)
    (hAD : A.natDegree = 6*w-9*67108863-3) (hBD : B.natDegree = 6*w-9*67108863-3)
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

end ArkLib.ProximityGap.Frontier.OrdinaryPolarGcdBudget
