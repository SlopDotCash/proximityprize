/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AlgebraicSectionSpecialization
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSSpecializedConditions
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.Algebra.Polynomial.Lifts

/-! # Descent below the weighted-degree characteristic bound

For a primitive component of any positive value degree, division by its
order-(d+1) implicit derivative numerator forces a single algebraic
polynomial section once the coordinate/value weighted degree is below the
characteristic. Its coefficients descend by integrality followed by polynomial
division over their relative algebraic closure.
-/

set_option autoImplicit false
noncomputable section
open Polynomial Polynomial.Bivariate
open scoped Differential
namespace ArkLib.ProximityGap.Frontier.FlatSectionWeightedDescent
variable {k L : Type} [Field k] [Field L] [Algebra k L]
section Differential
variable [Differential L] {p : ℕ} [CharP L p]

/-- A moving coordinate has no polynomial relation of degree below the characteristic
with differential-constant coefficients. -/
theorem flat_relation_eq_zero (x : L) (hx : x′ ≠ 0) (P : L[X])
    (hdeg : P.natDegree < p) (hflat : Differential.mapCoeffs P = 0)
    (hroot : P.eval x = 0) : P = 0 := by
  induction n : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hzero : P.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero hzero] at hroot ⊢
      simpa using congrArg C hroot
    · have ht := natDegree_derivative_lt hzero
      have hf : Differential.mapCoeffs P.derivative = 0 := by
        ext i
        have hh := congrArg (fun Q : L[X] => Q.coeff (i+1)) hflat
        change (P.coeff (i+1))′ = 0 at hh
        simp [coeff_derivative, Differential.deriv.leibniz, hh]
      have he := Differential.deriv_aeval_eq x P
      change (P.eval x)′ = (Differential.mapCoeffs P).eval x + P.derivative.eval x * x′ at he
      rw [hroot, hflat, map_zero] at he
      have hr : P.derivative.eval x = 0 := by
        simpa [hx] using he.symm
      have hz := ih P.derivative.natDegree (by omega) P.derivative (by omega) hf hr rfl
      exact False.elim (hzero
        (PositiveCharacteristicHeightDescent.natDegree_eq_zero_of_derivative_eq_zero P hdeg hz))

private theorem map_flat (hk : ∀ a : k, (algebraMap k L a)′ = 0) (r : k[X]) :
    Differential.mapCoeffs (r.map (algebraMap k L)) = 0 := by ext i; simp [hk]

/-- A flat polynomial section through one moving point is an identity after substitution
whenever its equation has coordinate/value weighted degree below the characteristic. -/
theorem section_identity (hk : ∀ a : k, (algebraMap k L a)′ = 0)
    (x : L) (hx : x′ ≠ 0) (f : k[X][X]) (q : L[X]) (d : ℕ)
    (hq : q.natDegree ≤ d) (hflat : Differential.mapCoeffs q = 0)
    (hw : natWeightedDegree f 1 d < p)
    (he : (f.map (aeval x).toRingHom).eval (q.eval x) = 0) :
    (f.map (mapRingHom (algebraMap k L))).eval q = 0 := by
  let F := f.map (mapRingHom (algebraMap k L))
  apply flat_relation_eq_zero x hx
  · have h₁ := degree_eval_le_weightedDegree F q (d+1) (by simpa using hq)
    exact (by simpa using h₁ : (F.eval q).natDegree ≤ natWeightedDegree F 1 d) |>.trans_lt
      ((GuruswamiSudan.OverRatFunc.natWeightedDegree_map_le (algebraMap k L) f 1 d).trans_lt hw)
  · clear he hw F
    induction f using Polynomial.induction_on' with
    | add a b ha hb => simp [ha, hb]
    | monomial i a =>
      simp [Differential.mapCoeffs.leibniz, Differential.mapCoeffs.leibniz_pow, map_flat hk,
        hflat]
  · rw [← he]
    simp only [eval_map, eval₂_eq_sum, eval_finsetSum, eval_mul, eval_pow, Polynomial.sum]
    apply Finset.sum_congr rfl
    intro i _
    change ((f.coeff i).map (algebraMap k L)).eval x * _ = _
    rw [eval_map_algebraMap]
    rfl

end Differential

attribute [local instance] Polynomial.algebra in
/-- The coefficients of a polynomial solving a nonzero equation over k[X] are
algebraic over k, even if the equation is nonmonic and k is finite. -/
theorem coefficient_algebraic (f : k[X][X]) (hf : f ≠ 0) (q : L[X])
    (he : (f.map (mapRingHom (algebraMap k L))).eval q = 0) (i : ℕ) :
    IsAlgebraic k (q.coeff i) := by
  classical
  let E := algebraicClosure k L
  let φ := algebraMap E L
  let a := f.leadingCoeff.map (algebraMap k E)
  have hφ : a.map φ = f.leadingCoeff.map (algebraMap k L) := by
    rw [Polynomial.map_map]; rfl
  have ha : a.map φ ≠ 0 := by
    rw [hφ, Polynomial.map_ne_zero_iff (algebraMap k L).injective]
    exact leadingCoeff_ne_zero.mpr hf
  have hr : aeval q f = 0 := by
    change f.eval₂ (algebraMap k[X] L[X]) q = 0
    rw [eval₂_eq_eval_map]
    exact he
  have hg := isIntegral_leadingCoeff_smul f q hr
  change IsIntegral k[X] (f.leadingCoeff.map (algebraMap k L)*q) at hg
  rw [← hφ] at hg
  have hL : a.map φ*q ∈ lifts φ := by
    apply (lifts_iff_coeff_lifts _).mpr
    intro j
    have hj := isAlgebraic_iff_isIntegral.mpr (hg.coeff j)
    exact ⟨⟨_, mem_algebraicClosure_iff.mpr hj⟩, rfl⟩
  obtain ⟨g,hg'⟩ := (mem_lifts _).mp hL
  have hmap : (g/a).map φ = q := by
    rw [Polynomial.map_div, hg', mul_div_cancel_left₀ _ ha]
  have hh := congrArg (fun P : L[X] => P.coeff i) hmap
  rw [coeff_map] at hh
  exact hh ▸ (mem_algebraicClosure_iff.mp ((g/a).coeff i).property)

open MovingCubicVanishingBranch AlgebraicSectionSpecialization

set_option maxHeartbeats 800000

set_option backward.isDefEq.respectTransparency false in
/-- For a primitive separable component, divisibility by its implicit numerator
gives a single algebraic polynomial section through every coefficient-field site.
The value degree is unrestricted and the characteristic exceeds the weighted degree. -/
theorem generic_section_with_sites {p : ℕ} [CharP k p] (hp : p.Prime)
    (f : k[X][X]) (hirr : Irreducible (genericEquation f)) (hprim : f.IsPrimitive)
    (hsep : f.derivative ≠ 0) (d : ℕ) (hd : d < p) (hw : natWeightedDegree f 1 d < p)
    (hdiv : genericEquation f ∣ genericEquation (coordinateNumerator f d)) :
    ∃ q : (AdjoinRoot (genericEquation f))[X], q.natDegree ≤ d ∧
      q.eval (AdjoinRoot.of (genericEquation f) (RatFunc.X : RatFunc k)) = AdjoinRoot.root (genericEquation f) ∧
      (∀ j, IsAlgebraic k (q.coeff j)) ∧
      ∀ a w : k, (f.map (evalRingHom a)).eval w = 0 →
        q.eval (algebraMap k _ a) = algebraMap k _ w := by
  let g := genericEquation f
  let L := AdjoinRoot g
  let _ : Fact (Irreducible g) := ⟨hirr⟩
  obtain ⟨D,hk,hx,hy⟩ := exists_generic_flat_differential f hsep d hdiv
  let _ : Differential L := D
  let x : L := AdjoinRoot.of g RatFunc.X
  let y : L := AdjoinRoot.root g
  let q := InverseTaylorFlat.expansion x y d
  let _ : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  obtain ⟨hdeg,hv,hflat⟩ := InverseTaylorFlat.expansion_spec hp x y hx d hd hy
  have hX : algebraMap k[X] L Polynomial.X = x := rfl
  have heval : (aeval x).toRingHom = algebraMap k[X] L := by
    ext a
    · exact aeval_C x a
    · exact (aeval_X x).trans hX.symm
  have hr : (f.map (aeval x).toRingHom).eval (q.eval x) = 0 := by
    rw [hv, heval, eval_map_algebraMap, aeval_def]
    have hh := AdjoinRoot.eval₂_root g
    change (f.map _).eval₂ _ _ = 0 at hh
    rw [eval₂_map] at hh
    exact hh
  have hz := section_identity hk x (hx ▸ one_ne_zero) f q d hdeg
    (by ext i; exact hflat i) hw hr
  have hf : f ≠ 0 := by
    intro hh
    exact hsep (by rw [hh, derivative_zero])
  have hcoeff := coefficient_algebraic f hf q hz
  exact ⟨q,hdeg,hv,hcoeff,section_at_site _ _ rfl f (generic_root_dvd f hprim) q hv hcoeff⟩

/-- A flat component carrying enough agreement must coincide at its generic root
with the affine interpolation of two base-field messages. The alternative bounds
the number of labels by the degree of the received restrictions times the exact
agreement surplus. -/
theorem component_small_or_head {F ι : Type*} [Field F] [DecidableEq F]
    {p : ℕ} [CharP k p] (hp : p.Prime) (f : k[X][X]) (hirr : Irreducible (genericEquation f))
    (hprim : f.IsPrimitive) (hsep : f.derivative ≠ 0) (d t m : ℕ) (hd : d < p)
    (hw : natWeightedDegree f 1 d < p)
    (hdiv : genericEquation f ∣ genericEquation (coordinateNumerator f d))
    (φ : F →+* k) (γ : k) (D : Finset ι) (dom : ι ↪ F) (u v : ι → F)
    (M : Finset F) (R : ι → F[X]) (hdt : d < t) (ht : t ≤ D.card)
    (hdeg : ∀ i ∈ D, (R i).natDegree ≤ m)
    (hfit : ∀ z ∈ M, t ≤ (D.filter fun i => (R i).eval z = 0).card)
    (hs : ∀ i ∈ D, R i = 0 →
      (f.map (evalRingHom (φ (dom i)))).eval (φ (u i) + γ*φ (v i)) = 0) :
    M.card * (t-d) ≤ (D.card-d)*m ∨
      ∃ A B : F[X], A.natDegree ≤ d ∧ B.natDegree ≤ d ∧
        AdjoinRoot.root (genericEquation f) =
          (A.map ((algebraMap k _).comp φ) +
            C (algebraMap k _ γ) * B.map ((algebraMap k _).comp φ)).eval
              (AdjoinRoot.of (genericEquation f) (RatFunc.X : RatFunc k)) := by
  classical
  rcases le_or_gt (M.card*(t-d)) ((D.card-d)*m) with h | h
  · exact Or.inl h
  right
  let I := D.filter fun i => R i = 0
  have hm : m < M.card := by
    by_contra! hn
    exact h.not_ge ((Nat.mul_le_mul hn (Nat.sub_le_sub_right ht d)).trans_eq (Nat.mul_comm _ _))
  have hI : d < I.card := by
    by_contra! hc
    have hsum := SecondPrimeComponentIncidence.component_incidence D M R t m hdeg hfit
    have hp := D.card_filter_add_card_filter_not (fun i => R i = 0)
    change I.card + (D.filter fun i => R i ≠ 0).card = D.card at hp
    change M.card*t ≤ I.card*M.card + (D.filter fun i => R i ≠ 0).card*m at hsum
    have ha : I.card*(M.card-m) ≤ d*(M.card-m) := Nat.mul_le_mul_right _ hc
    rw [Nat.mul_sub, Nat.mul_sub] at ha
    have hnt := Nat.sub_add_cancel hdt.le
    have hnd := Nat.sub_add_cancel (hdt.le.trans ht)
    have hinc := congrArg (fun z : ℕ => z*m) hp
    have hinc' := congrArg (fun z : ℕ => z*m) hnd
    have hinc'' := congrArg (fun z : ℕ => M.card*z) hnt
    simp only [Nat.add_mul, Nat.mul_add] at hinc hinc' hinc''
    have ha' := Nat.mul_le_mul_left I.card hm.le
    have hb' := Nat.mul_le_mul_left d hm.le
    rw [Nat.mul_comm M.card d] at hinc''
    omega
  let _ : Fact (Irreducible (genericEquation f)) := ⟨hirr⟩
  obtain ⟨q,hq,hv,_,hspec⟩ := generic_section_with_sites hp f hirr hprim hsep d hd hw hdiv
  let ψ := algebraMap k (AdjoinRoot (genericEquation f))
  obtain ⟨A,B,hA,hB,he⟩ := SecondPrimeComponentIncidence.generic_section_is_head
    (ψ.comp φ) (ψ γ) I dom u v d q hq hI (by
      intro i hi
      obtain ⟨hiD,hRi⟩ := Finset.mem_filter.mp hi
      simpa only [RingHom.comp_apply, map_add, map_mul] using hspec _ _ (hs i hiD hRi))
  exact ⟨A,B,hA,hB,he ▸ hv.symm⟩

end ArkLib.ProximityGap.Frontier.FlatSectionWeightedDescent

open ArkLib.ProximityGap.Frontier.FlatSectionWeightedDescent in
#print axioms flat_relation_eq_zero
open ArkLib.ProximityGap.Frontier.FlatSectionWeightedDescent in
#print axioms section_identity
open ArkLib.ProximityGap.Frontier.FlatSectionWeightedDescent in
#print axioms coefficient_algebraic
open ArkLib.ProximityGap.Frontier.FlatSectionWeightedDescent in
#print axioms generic_section_with_sites
open ArkLib.ProximityGap.Frontier.FlatSectionWeightedDescent in
#print axioms component_small_or_head
