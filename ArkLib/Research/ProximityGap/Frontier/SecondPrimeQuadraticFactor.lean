/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeParametricQuadratic
import ArkLib.Research.ProximityGap.Frontier.PaddedPowerSpecialization
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

/-- Every scalar with a square fiber of a discriminant with moving squarefree part
uses the padded resultant budget, except when the entire square factor vanishes there. -/
theorem square_specialization_bound_padded (D E H : Polynomial K[X]) (S : Finset K)
    (hD : D ≠ 0) (heq : D = E^2*H) (hr : 0 < H.natDegree)
    (hRes : resultant H H.derivative H.natDegree (H.natDegree-1) ≠ 0)
    (hS : ∀ z ∈ S, ∃ W : K[X], D.map (evalRingHom z) = W^2) :
    S.card ≤ 4 * Bivariate.degreeX D - 1 := by
  classical
  have hmul : E ^ 2 * H ≠ 0 := heq ▸ hD
  have hE : E ≠ 0 := by intro h; simp [h] at hmul
  have hH := right_ne_zero_of_mul hmul
  let A := S.filter fun t => Bivariate.evalX t E = 0
  let T := S \ A
  have hA : A.card ≤ Bivariate.degreeX E := Bivariate.card_evalX_eq_zero_le_degreeX E hE S
  have hsplit : T.card + A.card = S.card := card_sdiff_add_card_eq_card (filter_subset ..)
  have hheight : Bivariate.degreeX D = 2 * Bivariate.degreeX E + Bivariate.degreeX H := by
    rw [heq, pow_two, Bivariate.degreeX_mul _ _ (mul_ne_zero hE hE) hH,
      Bivariate.degreeX_mul _ _ hE hE]
    omega
  rcases T.eq_empty_or_nonempty with h0 | hne
  · rw [h0, card_empty] at hsplit
    omega
  · have hcount := PaddedPowerSpecialization.square_fibers_lt H T hne hr hRes (by
      intro t ht
      obtain ⟨htS, htA⟩ := mem_sdiff.mp ht
      let φ := evalRingHom t
      have hv : E.map φ ≠ 0 := fun h =>
        htA (mem_filter.mpr ⟨htS, (Bivariate.evalX_eq_map t E).trans h⟩)
      obtain ⟨W, hW⟩ := hS t htS
      have hmap : (E.map φ) ^ 2 * H.map φ = W ^ 2 := by
        simpa only [heq, Polynomial.map_mul, Polynomial.map_pow] using hW
      have hdvd : (E.map φ) ^ 2 ∣ W ^ 2 := ⟨H.map φ, hmap.symm⟩
      obtain ⟨q, hq⟩ := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hdvd
      refine ⟨q, ?_⟩
      rw [hq, mul_pow] at hmap
      exact mul_left_cancel₀ (pow_ne_zero 2 hv) hmap)
    omega

/-- The previous five-times-degree estimate follows from the padded bound. -/
theorem square_specialization_bound (D E H : Polynomial K[X]) (S : Finset K)
    (hD : D ≠ 0) (heq : D = E^2*H) (hr : 0 < H.natDegree)
    (hRes : resultant H H.derivative H.natDegree (H.natDegree-1) ≠ 0)
    (hS : ∀ z ∈ S, ∃ W : K[X], D.map (evalRingHom z) = W^2) :
    S.card ≤ 5*Bivariate.degreeX D := by
  have hh := square_specialization_bound_padded D E H S hD heq hr hRes hS
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
private theorem actual_discriminant_degrees {w : ℕ} (Q f : Factor K) (hQ : Q ≠ 0) (hdiv : f ∣ Q)
    (hshape : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
      i+j ≤ 34 ∧ a ≤ w) :
    let P := (f.coeff 1)^2-4*f.coeff 2*f.coeff 0
    Bivariate.degreeX (Bivariate.swap P) ≤ 66 ∧ (Bivariate.swap P).natDegree ≤ 2 * w := by
  classical
  let P := (f.coeff 1)^2-4*f.coeff 2*f.coeff 0
  have ht := factor_totalDegree_le hQ hdiv (fun j i a h => (hshape j i a h).1)
  have coeffd (j : ℕ) (hj : j ≤ 34) : (f.coeff j).natDegree ≤ 34-j := by
    rcases Bivariate.coeff_totalDegree_le' f j with h | h
    · omega
    · simp [h]
  have hWQ : weight 0 Q ≤ w := by
    apply weight_le_of_coeff
    intro j i a h
    have := (hshape j i a h).2
    omega
  have hW : weight 0 f ≤ w := by
    obtain ⟨g,hg⟩ := hdiv
    rw [hg] at hQ hWQ
    rw [weight_mul 0 f g (left_ne_zero_of_mul hQ) (right_ne_zero_of_mul hQ)] at hWQ
    omega
  have degcoord (j : ℕ) : (Bivariate.swap (f.coeff j)).natDegree ≤ w := by
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
    exact discriminant_height _ _ _ (degcoord 2) (degcoord 1) (degcoord 0) (by omega) (by omega)

open Classical in
/-- A quadratic of total degree at most 34 has at most 263 moving square fibers.
The remaining discriminant class is controlled by the same secant extraction as a line. -/
theorem quadratic_population_of_extraction {k w : ℕ} (fam : BadScalarRichPointFamily dom k δ u) (φ : F →+* K)
    (Q f : Factor K) (hQ : Q ≠ 0) (hdiv : f ∣ Q) (hf : Irreducible f) (hd : f.natDegree = 2)
    (hshape : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i+j ≤ 34 ∧ a ≤ w)
    (hw : 0 < w) (hchar : ∀ i : ℕ, 0 < i → i ≤ 2 * w → (i : K) ≠ 0)
    {m : ℕ} (extract : SecantExtraction fam (m+1)) :
    (fam.G.filter fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0).card ≤
      max m 263 := by
  classical
  let pop := fam.G.filter fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0
  change pop.card ≤ max m 263
  let P := (f.coeff 1)^2 - 4*f.coeff 2*f.coeff 0
  let D := Bivariate.swap P
  have hheight := actual_discriminant_degrees Q f hQ hdiv hshape
  change Bivariate.degreeX D ≤ 66 ∧ D.natDegree ≤ 2*w at hheight
  have back : P = Bivariate.swap D := (Bivariate.swap_swap_apply P).symm
  have param (s : K[X]) (V : Polynomial K[X]) (h : P = s.map C * V^2) :
      pop.card ≤ max m 263 := by
    have htotal := factor_totalDegree_le hQ hdiv (fun j i a h => (hshape j i a h).1)
    have hc : (2 : K) ≠ 0 := hchar 2 (by decide) (by omega)
    exact (parametric_population_of_extraction fam φ f hf hd htotal hc s V h extract).trans (le_max_left _ _)
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
  let T := pop.image φ
  have hT : T.card = pop.card := card_image_of_injective _ φ.injective
  have hcap := square_specialization_bound_padded D E H T hD hEH.symm (Nat.pos_of_ne_zero hHz) hres (by
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

/-- At the second-prime sixteenth-rate predecessor, both discriminant cases give at most 263. -/
theorem quadratic_population_le_263 (fam : Family dom δ u) (φ : F →+* K)
    (Q f : Factor K) (hQ : Q ≠ 0) (hdiv : f ∣ Q) (hf : Irreducible f) (hd : f.natDegree = 2)
    (hshape : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i+j ≤ 34 ∧ a < 357913943)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 715827884 → (i : K) ≠ 0)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊) :
    (population fam φ f).card ≤ 263 := by
  apply quadratic_population_of_extraction (w := 357913942) (m := 184) fam φ Q f hQ hdiv hf hd
    (fun j i a ha => ⟨(hshape j i a ha).1, Nat.le_of_lt_succ (hshape j i a ha).2⟩)
    (by decide) hchar
  intro M hM hm U
  exact many_on_secant fam M hM hm U hn ht

/-- The terminal population bound with the original numerical interface. -/
theorem quadratic_population_le (fam : Family dom δ u) (φ : F →+* K)
    (Q f : Factor K) (hQ : Q ≠ 0) (hdiv : f ∣ Q) (hf : Irreducible f) (hd : f.natDegree = 2)
    (hshape : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i+j ≤ 34 ∧ a < 357913943)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 715827884 → (i : K) ≠ 0)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊) :
    (population fam φ f).card ≤ 330 := by
  exact (quadratic_population_le_263 fam φ Q f hQ hdiv hf hd hshape hchar hn ht).trans (by decide)

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

#print axioms square_specialization_bound_padded
#print axioms quadratic_population_le_263
#print axioms square_specialization_bound
#print axioms quadratic_population_le
#print axioms actual_cubic_or_quartic

end ProximityGap.SecondPrimeQuadraticFactor
