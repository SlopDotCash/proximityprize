/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeParametricQuadratic
import ArkLib.Research.ProximityGap.Frontier.SquareSpecialization
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeNonlinearObstruction
import ArkLib.Data.Polynomial.BivariateFactorDegrees
import ArkLib.Research.ProximityGap.Frontier.SquarefreeCoordinateResultant

/-! # The quadratic alternative at the second-prime predecessor -/

open Finset Polynomial Code
open ProximityGap.SecondPrimeLinearFactor ProximityGap.SecondPrimeParametricQuadratic
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open scoped NNReal

namespace ProximityGap.SecondPrimeQuadraticFactor

variable {K : Type} [Field K]

/-- If the odd part of a discriminant varies with the coordinate, the scalar
specializations of the whole discriminant that are squares occupy at most five
times its parameter degree, including all degree-dropping specializations. -/
theorem square_specialization_bound (D E H : Polynomial K[X]) (S : Finset K)
    (hD : D ≠ 0) (heq : D = E^2*H) (hr : 0 < H.natDegree)
    (hRes : resultant H H.derivative H.natDegree (H.natDegree-1) ≠ 0)
    (hS : ∀ z ∈ S, ∃ W : K[X], D.map (evalRingHom z) = W^2) :
    S.card ≤ 5*Bivariate.degreeX D := by
  classical
  let good := S.filter fun z => D.leadingCoeff.eval z ≠ 0
  let bad := S \ good
  have hem : E^2*H ≠ 0 := heq ▸ hD
  have hE := left_ne_zero_of_mul hem
  have hH := right_ne_zero_of_mul hem
  have hdegree : D.natDegree = 2*E.natDegree + H.natDegree := by
    rw [heq,natDegree_mul hE hH,natDegree_pow]
  have hg := SquareSpecialization.card_regular_squares_le H good hr hRes (by
    intro z hz
    obtain ⟨hzS,hzlc⟩ := mem_filter.mp hz
    let φ := evalRingHom z
    have hdz : (D.map φ).natDegree = D.natDegree := natDegree_map_eq_iff.mpr (Or.inl hzlc)
    have hmap : D.map φ = (E.map φ)^2 * H.map φ := by rw [heq]; simp
    have hmap0 : D.map φ ≠ 0 := by
      intro he; rw [he,natDegree_zero] at hdz; omega
    have hm0 : (E.map φ)^2*H.map φ ≠ 0 := hmap ▸ hmap0
    have hE0 := left_ne_zero_of_mul hm0
    have hH0 := right_ne_zero_of_mul hm0
    have hsum := hdz
    rw [hmap,natDegree_mul hE0 hH0,natDegree_pow] at hsum
    have h1 : (E.map φ).natDegree ≤ E.natDegree := natDegree_map_le
    have h2 : (H.map φ).natDegree ≤ H.natDegree := natDegree_map_le
    refine ⟨?_,?_⟩
    · change (H.map φ).natDegree = H.natDegree; omega
    obtain ⟨W,hW⟩ := hS z hzS
    have hv : (E.map φ)^2 ∣ W^2 := ⟨_,hW.symm.trans hmap⟩
    obtain ⟨q,hq⟩ := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hv
    refine ⟨1,q,?_⟩
    have h := hmap.symm.trans hW
    rw [hq,mul_pow] at h
    simpa using mul_left_cancel₀ hE0 h)
  have hb : bad.card ≤ D.leadingCoeff.natDegree := by
    by_contra! hlarge
    apply (leadingCoeff_ne_zero.mpr hD)
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ bad _ hlarge
    intro z hz
    obtain ⟨hzS,hzg⟩ := mem_sdiff.mp hz
    by_contra hh
    exact hzg (mem_filter.mpr ⟨hzS,hh⟩)
  have hc := card_sdiff_add_card_eq_card (show good ⊆ S from filter_subset _ _)
  change bad.card+good.card = S.card at hc
  have hlead : D.leadingCoeff.natDegree ≤ Bivariate.degreeX D :=
    Bivariate.coeff_natDegree_le_degreeX D D.natDegree
  have hHd : H ∣ D := heq ▸ dvd_mul_left _ _
  have hh := Bivariate.degreeX_le_of_dvd hHd hD
  omega

private theorem discriminant_height {R : Type*} [CommRing R] (A B D : R[X])
    {a b d h : ℕ} (ha : A.natDegree ≤ a) (hb : B.natDegree ≤ b) (hd : D.natDegree ≤ d)
    (h1 : 2*b ≤ h) (h2 : a+d ≤ h) : (B^2-4*A*D).natDegree ≤ h := by
  apply (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact natDegree_pow_le.trans (by omega)
  · have hC : (4 : R[X]).natDegree = 0 := natDegree_ofNat 4
    have hmul : ((4 : R[X])*A).natDegree ≤ (4 : R[X]).natDegree+A.natDegree := natDegree_mul_le
    exact natDegree_mul_le.trans (by omega)

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
open ArkLib.ProximityGap.Frontier.SecondPrimeActualPopulations
open ArkLib.ProximityGap.Frontier.SecondPrimeCoordinateWeight

/-- The scalar and coordinate degrees of the transposed discriminant follow
from the support of the parent interpolant, including after factorization. -/
private theorem actual_discriminant_degrees (Q f : Factor K) (hQ : Q ≠ 0) (hdiv : f ∣ Q)
    (hshape : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
      i+j ≤ 34 ∧ a < 357913943) :
    let P := (f.coeff 1)^2-4*f.coeff 2*f.coeff 0
    Bivariate.degreeX (Bivariate.swap P) ≤ 66 ∧ (Bivariate.swap P).natDegree ≤ 715827884 := by
  classical
  let P := (f.coeff 1)^2-4*f.coeff 2*f.coeff 0
  have ht := factor_totalDegree_le hQ hdiv (fun j i a h => (hshape j i a h).1)
  have coeffd (j : ℕ) (hj : j ≤ 34) : (f.coeff j).natDegree ≤ 34-j := by
    rcases Bivariate.coeff_totalDegree_le' f j with h | h
    · omega
    · simp [h]
  have hWQ : weight 0 Q ≤ 357913942 := by
    apply weight_le_of_coeff
    intro j i a h
    have := (hshape j i a h).2
    omega
  have hW : weight 0 f ≤ 357913942 := by
    obtain ⟨g,hg⟩ := hdiv
    rw [hg] at hQ hWQ
    rw [weight_mul 0 f g (left_ne_zero_of_mul hQ) (right_ne_zero_of_mul hQ)] at hWQ
    omega
  have degcoord (j : ℕ) : (Bivariate.swap (f.coeff j)).natDegree ≤ 357913942 := by
    rw [show (Bivariate.swap (f.coeff j)).natDegree = Bivariate.degreeX (f.coeff j) from
      Bivariate.natDegreeY_swap _]
    by_cases hj : f.coeff j = 0
    · simp [hj,Bivariate.degreeX]
    obtain ⟨i,hi,heq,_⟩ := Bivariate.exists_max_index_degreeX (f.coeff j) hj
    have h := coeff_weight_le 0 f (j := j) (i := i)
      (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hi))
    omega
  constructor
  · rw [Bivariate.degreeX_swap]
    exact discriminant_height _ _ _ (coeffd 2 (by decide)) (coeffd 1 (by decide))
      (coeffd 0 (by decide)) (by decide) (by decide)
  · simp only [map_sub,map_pow,map_mul,map_ofNat]
    exact discriminant_height _ _ _ (degcoord 2) (degcoord 1) (degcoord 0) (by decide) (by decide)

/-- An actual irreducible quadratic factor at the second-prime predecessor
carries at most 330 distinct bad labels. The discriminant cases are exhaustive. -/
theorem quadratic_population_le (fam : Family dom δ u) (φ : F →+* K)
    (Q f : Factor K) (hQ : Q ≠ 0) (hdiv : f ∣ Q) (hf : Irreducible f) (hd : f.natDegree = 2)
    (hshape : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i+j ≤ 34 ∧ a < 357913943)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 715827884 → (i : K) ≠ 0)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊) :
    (population fam φ f).card ≤ 330 := by
  classical
  let P := (f.coeff 1)^2 - 4*f.coeff 2*f.coeff 0
  let D := Bivariate.swap P
  have hheight := actual_discriminant_degrees Q f hQ hdiv hshape
  change Bivariate.degreeX D ≤ 66 ∧ D.natDegree ≤ 715827884 at hheight
  have back : P = Bivariate.swap D := (Bivariate.swap_swap_apply P).symm
  have param (s : K[X]) (V : Polynomial K[X]) (h : P = s.map C * V^2) :
      (population fam φ f).card ≤ 330 := by
    have hw := factor_totalDegree_le hQ hdiv (fun j i a h => (hshape j i a h).1)
    have hc : (2 : K) ≠ 0 := hchar 2 (by decide) (by decide)
    exact (parametric_discriminant_population_le fam φ f hf hd hw hc s V h hn ht).trans (by decide)
  by_cases hD : D = 0
  · apply param 0 0
    simpa [hD] using back
  obtain ⟨E,H,hEH,hsq⟩ := exists_sq_mul_squarefree D
  by_cases hHz : H.natDegree = 0
  · apply param (H.coeff 0) (Bivariate.swap E)
    have hEH' : D = E^2*C (H.coeff 0) := hEH.symm.trans
      (congrArg (fun g => E^2*g) (eq_C_of_natDegree_eq_zero hHz))
    rw [back,hEH',map_mul,map_pow,Bivariate.swap_C,mul_comm]
  have hHd : H ∣ D := hEH ▸ dvd_mul_left _ _
  have hbound := (natDegree_le_of_dvd hHd hD).trans hheight.2
  have hres := SquarefreeCoordinateResultant.squarefree_resultant_ne_zero H hsq
    (Nat.pos_of_ne_zero hHz) (fun i hi hj => hchar i hi (hj.trans hbound))
  let T := (population fam φ f).image φ
  have hT : T.card = (population fam φ f).card := card_image_of_injective _ φ.injective
  have hcap := square_specialization_bound D E H T hD hEH.symm (Nat.pos_of_ne_zero hHz) hres (by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
    have he := (mem_filter.mp ha).2
    let y := (fam.q a).map φ
    let c (j : ℕ) := (f.coeff j).eval (C (φ a))
    have hroot : c 2*y^2+c 1*y+c 0 = 0 := by
      rw [eval₂_eq_sum_range' _ (by omega : f.natDegree < 3)] at he
      simpa [sum_range_succ,c,y,add_assoc,add_comm,add_left_comm] using he
    refine ⟨2*c 2*y+c 1,?_⟩
    have hs : D.map (evalRingHom (φ a)) = P.eval (C (φ a)) := by
      simpa only [D,Bivariate.evalX_eq_map,Bivariate.evalY] using
        (Bivariate.evalY_eq_evalX_swap (φ a) P).symm
    rw [hs]
    simp only [P,eval_sub,eval_pow,eval_mul,eval_ofNat]
    dsimp only [c] at *
    linear_combination -(4*(f.coeff 2).eval (C (φ a)))*hroot)
  omega

/-- An overbudget pair at the second-prime predecessor must produce a populous
irreducible cubic or quartic. Both populations and coordinate weights are
bounds on the actual factor of the actual interpolant. -/
theorem actual_cubic_or_quartic (fam : Family dom δ u) (φ : F →+* K)
    {p : ℕ} [CharP K p] (hp : 715827884 < p) (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 357913943)
    (hbig : 2147483648 < fam.G.card) :
    ∃ Q : Factor K, Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 4 ∧ i+j ≤ 34 ∧ a+j*67108863 < 357913943) ∧
      ∃ f : Factor K, Irreducible f ∧ f ∣ Q ∧
        ((f.natDegree = 4 ∧ 2147483615 ≤ (population fam φ f).card ∧
          weight 67108863 f ≤ 302954072) ∨
         (f.natDegree = 3 ∧ 1431655733 ≤ (population fam φ f).card ∧
          weight 67108863 f ≤ 290805098)) := by
  classical
  obtain ⟨Q,hQ,hs,f,hf,hd,h4 | h3 | ⟨h2,hpop⟩⟩ :=
    ArkLib.ProximityGap.Frontier.SecondPrimeNonlinearObstruction.actual_factor fam φ hn ht hbig
  · exact ⟨Q,hQ,hs,f,hf,hd,Or.inl h4⟩
  · exact ⟨Q,hQ,hs,f,hf,hd,Or.inr h3⟩
  · have h := quadratic_population_le fam φ Q f hQ hd hf h2 (fun j i a ha => by
      obtain ⟨_,hi,hc⟩ := hs j i a ha
      exact ⟨hi,by omega⟩) (fun i hi hj hc =>
        (by omega : ¬p ≤ i) (Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff K p i).mp hc)))
      hn ht.ge
    omega

#print axioms square_specialization_bound
#print axioms quadratic_population_le
#print axioms actual_cubic_or_quartic

end ProximityGap.SecondPrimeQuadraticFactor
