/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarSyndromeInterpolation
import ArkLib.Research.ProximityGap.Frontier.ApolarRootTransition
import ArkLib.Research.ProximityGap.Frontier.ApolarChartCancellation
import ArkLib.Research.ProximityGap.Frontier.ApolarReciprocalCharts

/-! # Reciprocal parameter transition for the two cubic interpolation remainders

Reflecting the reciprocal interpolation equation to one common degree gives
a polynomial identity over the coordinate polynomial ring. Cancellation of
the bad-parameter vanisher leaves the required cleared divisibility.
-/

set_option autoImplicit false
namespace ProximityGap.ApolarParameterTransition
open Polynomial Finset
open ApolarDividedLocator ApolarDividedPolynomial ApolarChartCancellation
open ArkLib.ProximityGap.Frontier.ApolarReciprocalCharts

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
private theorem rereflect (p : R[X]) {w z : ℕ} (hw : p.natDegree ≤ w) :
    reflect (w+z) (reflect w p) = X^z*p := by
  have hd := (natDegree_reflect_le (N := w) (p := p)).trans (max_le le_rfl hw)
  simpa only [mul_one, one_mul, reflect_reflect, reflect_one, mul_comm] using
    reflect_mul (reflect w p) 1 hd (show (1:R[X]).natDegree ≤ z by simp)

/-- Reflect the two polynomial interpolation identities and cancel the bad-parameter
vanisher. Here T is the outer variable and R can be the coordinate polynomial ring.
The reciprocal vanisher is scaled to the literal reflection of the forward vanisher. -/
theorem negative_dvd {ι : Type*} (D : Finset ι) (site : ι → R)
    (f U Q Qt B Bt : R[X]) {l m k w : ℕ}
    (hM : D.card = w+k) (hf : f.natDegree ≤ l) (hU : U.natDegree ≤ w)
    (hQ : l+Qt.natDegree ≤ D.card+m) (hBt : Bt.natDegree ≤ m)
    (hfree : ∀ i ∈ D, f.eval (site i) ≠ 0)
    (forward : U = f*Q + Lagrange.nodal D site*B)
    (backward : reflect w U = (reflect l f)*Qt +
      reflect D.card (Lagrange.nodal D site)*Bt) :
    f ∣ reflect m Bt - X^(m+k)*B := by
  let S := Lagrange.nodal D site
  have hs : S.natDegree ≤ D.card := (Lagrange.natDegree_nodal ..).le
  have hl : l ≤ D.card+m := by omega
  let q := D.card+m-l
  have hq : Qt.natDegree ≤ q := by dsimp [q]; omega
  have htl := (natDegree_reflect_le (N := l) (p := f)).trans (max_le le_rfl hf)
  have hts := (natDegree_reflect_le (N := D.card) (p := S)).trans (max_le le_rfl hs)
  have left : reflect (D.card+m) (reflect w U) = X^(m+k)*U := by
    rw [show D.card+m=w+(m+k) by omega,rereflect U hU]
  have qprod : reflect (D.card+m) (reflect l f*Qt) = f*reflect q Qt := by
    rw [show D.card+m=l+q by dsimp [q]; omega,reflect_mul _ _ htl hq,reflect_reflect]
  have sp : reflect (D.card+m) (reflect D.card S*Bt) = S*reflect m Bt := by
    rw [reflect_mul _ _ hts hBt,reflect_reflect]
  change reflect w U = (reflect l f)*Qt + (reflect D.card S)*Bt at backward
  change U = f*Q + S*B at forward
  rw [backward,reflect_add,qprod,sp] at left
  apply cancel_nodal D site _ _ hfree
  refine ⟨X^(m+k)*Q-reflect q Qt, ?_⟩
  change S*(reflect m Bt-X^(m+k)*B) = _
  rw [forward] at left
  linear_combination left

/-- Homogenizing the vanisher of inverse parameter sites gives the literal reversed
nodal polynomial times an explicitly invertible constant. -/
theorem nodal_reverse {ι : Type*} (D : Finset ι) (site : ι → Rˣ) :
    reflect D.card (Lagrange.nodal D (fun i => (site i:R))) =
      C (↑(∏ i ∈ D, -(site i)):R) * Lagrange.nodal D (fun i => (↑(site i)⁻¹:R)) := by
  classical
  induction D using Finset.induction_on with
  | empty => simp [Lagrange.nodal, reflect_one]
  | insert i s hi ih =>
    rw [card_insert_of_notMem hi, Nat.add_comm, Lagrange.nodal_insert_eq_nodal hi,
      reflect_mul _ _ (by rw [natDegree_X_sub_C]) (Lagrange.natDegree_nodal ..).le,
      ih, prod_insert hi, Lagrange.nodal_insert_eq_nodal hi]
    have he : reflect 1 (X-C (site i:R)) = C (-(site i:R))*(X-C (↑(site i)⁻¹:R)) := by
      rw [reflect_sub,reflect_one_X,reflect_C,pow_one,mul_sub,← C_mul]
      simp only [neg_mul,Units.mul_inv,map_neg,map_one]
      ring
    rw [he,Units.val_mul,map_mul,Units.val_neg]
    ring

private theorem unscale_nodal {ι : Type*} (D : Finset ι) (site : ι → Rˣ) (B : R[X]) :
    reflect D.card (Lagrange.nodal D (fun i => (site i:R))) *
      (C (↑(∏ i ∈ D, -(site i))⁻¹:R)*B) =
      Lagrange.nodal D (fun i => (↑(site i)⁻¹:R))*B := by
  rw [nodal_reverse]
  let c := ∏ i ∈ D, -(site i)
  change C (c:R)*_*(C (↑c⁻¹:R)*B) = _
  have h : C (c:R)*C (↑c⁻¹:R) = (1:R[X]) := by rw [← C_mul,c.mul_inv,map_one]
  linear_combination (Lagrange.nodal D (fun i => (↑(site i)⁻¹:R))*B)*h

variable {K : Type*} [Field K]
local notation "Biv" => K[X][X]

private theorem reflect_sum {ι : Type*} (D : Finset ι) (g : ι → K[X]) (w : ℕ) :
    reflect w (∑ i ∈ D,g i) = ∑ i ∈ D, reflect w (g i) := by
  classical
  induction D using Finset.induction_on with
  | empty => simp [reflect_zero]
  | insert i s hi ih => rw [sum_insert hi,reflect_add,ih,sum_insert hi]

private theorem reverse_degree (f : Biv) (l : ℕ) :
    (reverseCoeffs l f).natDegree = f.natDegree := by
  have le (h : Biv) : (reverseCoeffs l h).natDegree ≤ h.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    simp [coeff_eq_zero_of_natDegree_lt hj]
  have h := le (reverseCoeffs l f)
  have eq : reverseCoeffs l (reverseCoeffs l f) = f := by ext; simp
  rw [eq] at h
  exact le_antisymm (le f) h

private theorem divided_coeff_reverse (f : Biv) (y : K) (l j : ℕ) :
    (divided (reverseCoeffs l f) (C y)).coeff j = reflect l ((divided f (C y)).coeff j) := by
  rw [divided,divided,coeff_divByMonic_X_sub_C,coeff_divByMonic_X_sub_C,reverse_degree,reflect_sum]
  apply sum_congr rfl
  intro i hi
  rw [coeff_reverseCoeffs,← C_pow,reflect_C_mul]

/-- The literal polynomial representative on the reversed parameter chart is the
coefficientwise reflection of the original representative at weight l+1. -/
theorem representative_reversed (D : Finset K) (w : K → K[X]) (f : Biv) (l : ℕ)
    (hw : ∀ i ∈ D, (w i).natDegree ≤ 1) (hf : ∀ j, (f.coeff j).natDegree ≤ l) :
    representative D C (fun i => reflect 1 (w i)) (reverseCoeffs l f) =
      reverseCoeffs (l+1) (representative D C w f) := by
  ext j : 1
  simp only [representative,finsetSum_coeff,coeff_C_mul,coeff_reverseCoeffs,reflect_sum]
  apply sum_congr rfl
  intro i hi
  have hd : ((divided f (C i)).coeff j).natDegree ≤ l := by
    rw [divided,coeff_divByMonic_X_sub_C]
    apply natDegree_sum_le_of_forall_le
    intro v hv
    rw [← C_pow]
    exact (natDegree_C_mul_le ..).trans (hf v)
  rw [divided_coeff_reverse,show l+1=1+l by omega,reflect_mul _ _ (hw i hi) hd]

/-- Swapping variables turns coefficientwise parameter reflection into outer reflection. -/
theorem swap_reverse (f : Biv) (l : ℕ) :
    Bivariate.swap (reverseCoeffs l f) = reflect l (Bivariate.swap f) := by
  ext j k
  simp only [swap_coeff,coeff_reverseCoeffs,coeff_reflect]

private theorem reflect_cube (P : (K[X])[X]) (w : ℕ) (h : P.natDegree ≤ w) :
    reflect (3*w) (P^3) = (reflect w P)^3 := by
  have d : (P^2).natDegree ≤ 2*w := (natDegree_pow_le ..).trans (Nat.mul_le_mul_left _ h)
  rw [show 3*w=2*w+w by omega,show (3:ℕ)=2+1 by decide,pow_succ P 2,
    reflect_mul _ _ d h,show 2*w=w+w by omega,pow_two P,reflect_mul _ _ h h]
  ring

/-- The reciprocal numerator, built from the same coordinate vanisher, is precisely
the weight-3(l+1) parameter reflection of the original numerator. -/
theorem cubic_reversed (D : Finset K) (w : K → K[X]) (f : Biv) (l : ℕ)
    (V : K[X]) (hw : ∀ i ∈ D, (w i).natDegree ≤ 1) (hf : ∀ j, (f.coeff j).natDegree ≤ l) :
    C V * (Bivariate.swap (representative D C (fun i => reflect 1 (w i))
      (reverseCoeffs l f)))^3 =
    reflect (3*(l+1)) (C V * (Bivariate.swap (representative D C w f))^3) := by
  rw [representative_reversed _ _ _ _ hw hf,swap_reverse,reflect_C_mul,
    reflect_cube _ _ (ApolarSyndromeInterpolation.degree_swap _ _ (pencil_coefficient_degree D w f l hw hf))]

/-- Four-chart input from the actual cubed representatives and the two interpolation
identities. Here B and Bt are polynomials in the parameter with coordinate-polynomial
coefficients. The reciprocal interpolation uses the monic vanisher of the inverse sites. -/
theorem cleared_cubic_remainders {ι : Type*} (Z : Finset ι) (site : ι → K[X]ˣ)
    (D : Finset K) (w : K → K[X]) (f : Biv) (V : K[X]) (l m k : ℕ)
    (Q Qt B Bt : Biv) (hM : Z.card = 3*(l+1)+k) (hw : ∀ i ∈ D, (w i).natDegree ≤ 1)
    (hf : ∀ j, (f.coeff j).natDegree ≤ l) (hQt : l+Qt.natDegree ≤ Z.card+m)
    (hBt : Bt.natDegree ≤ m) (hfree : ∀ i ∈ Z, (Bivariate.swap f).eval (site i:K[X]) ≠ 0)
    (forward : C V * (Bivariate.swap (representative D C w f))^3 =
      Bivariate.swap f * Q + Lagrange.nodal Z (fun i => (site i:K[X])) * B)
    (backward : C V * (Bivariate.swap (representative D C (fun i => reflect 1 (w i))
        (reverseCoeffs l f)))^3 =
      Bivariate.swap (reverseCoeffs l f)*Qt + Lagrange.nodal Z (fun i => (↑(site i)⁻¹:K[X]))*Bt) :
    let Bt' := C (↑(∏ i ∈ Z, -(site i))⁻¹:K[X])*Bt
    f ∣ C 1 * reverseCoeffs m (Bivariate.swap Bt') - C (X^(m+k))*Bivariate.swap B := by
  let c := ∏ i ∈ Z, -(site i)
  let Bt' := C (↑c⁻¹:K[X])*Bt
  change f ∣ C 1*reverseCoeffs m (Bivariate.swap Bt')-C (X^(m+k))*Bivariate.swap B
  rw [cubic_reversed D w f l V hw hf, swap_reverse,
      ← unscale_nodal Z site Bt] at backward
  have hu : (C V * (Bivariate.swap (representative D C w f))^3).natDegree ≤ 3*(l+1) :=
    (natDegree_C_mul_le ..).trans (natDegree_pow_le_of_le 3
      (ApolarSyndromeInterpolation.degree_swap _ _ (pencil_coefficient_degree D w f l hw hf)))
  obtain ⟨q,hq⟩ := negative_dvd Z (fun i => (site i:K[X])) (Bivariate.swap f) _ Q Qt B Bt'
    hM (ApolarSyndromeInterpolation.degree_swap f l hf) hu hQt ((natDegree_C_mul_le ..).trans hBt) hfree forward backward
  have ht : Bivariate.swap (reflect m Bt') = reverseCoeffs m (Bivariate.swap Bt') := by
    rw [← Bivariate.swap_swap_apply Bt', ← swap_reverse, Bivariate.swap_swap_apply,
      Bivariate.swap_swap_apply]
  refine ⟨Bivariate.swap q,?_⟩
  have hpower : Bivariate.swap (X^(m+k) : Biv) = C (X^(m+k)) := by
    rw [map_pow,Bivariate.swap_Y,C_pow]
  simpa only [map_sub,map_mul,Bivariate.swap_swap_apply,ht,hpower,map_one,one_mul]
    using congrArg Bivariate.swap hq

/-- The constant used to turn the monic inverse-site vanisher into the reversed
one preserves both parameter and coordinate degrees of the remainder. -/
theorem unit_rescale_degrees (u : K[X]ˣ) (B : Biv) :
    (C (u:K[X])*B).natDegree = B.natDegree ∧
    (Bivariate.swap (C (u:K[X])*B)).natDegree = (Bivariate.swap B).natDegree := by
  refine ⟨natDegree_C_mul_of_isUnit u.isUnit _,?_⟩
  rw [map_mul,Bivariate.swap_C]
  have h := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit u.isUnit)
  have hn : (u:K[X]).coeff 0 ≠ 0 := fun z => u.ne_zero (h.trans (by simp [z]))
  have hc : ((u:K[X]).map (C : K →+* K[X])) = C (C ((u:K[X]).coeff 0)) := by
    conv_lhs => rw [h, Polynomial.map_C]
  rw [hc,natDegree_C_mul_of_isUnit ((isUnit_iff_ne_zero.mpr hn).map C)]

/-- Reversing the polynomial weight of a syndrome row pencil exchanges its rows. -/
theorem reverse_row_weight (a b : K) :
    reflect 1 (C a+X*C b) = C b+X*C a := by
  rw [reflect_add,reflect_C,pow_one,mul_comm X (C b),reflect_C_mul,reflect_one_X]
  ring

/-- Reciprocal-node interpolation indexed by the image of field inversion equals
the product over the original nodes with reciprocal site arguments. -/
theorem nodal_inverse_image [DecidableEq K] (G : Finset K) :
    Lagrange.nodal (G.image Inv.inv) (C : K →+* K[X]) =
      Lagrange.nodal G (fun x => (C x⁻¹ : K[X])) := by
  classical
  rw [Lagrange.nodal,Lagrange.nodal,Finset.prod_image]
  exact fun a _ b _ h => inv_injective h

omit [IsDomain R] in
/-- Fiber divisibility is preserved at inverse parameters, including repeated
roots in the coordinate polynomial. No reversed syndrome hypothesis is required. -/
theorem inverse_fiber (f U : R[X]) (t : Rˣ) {l w : ℕ} (hf : f.natDegree ≤ l)
    (hU : U.natDegree ≤ w) (hd : f.eval (t:R) ∣ U.eval (t:R)) :
    (reflect l f).eval (↑t⁻¹:R) ∣ (reflect w U).eval (↑t⁻¹:R) := by
  rw [ApolarRootTransition.eval_reflect t⁻¹ l f hf,ApolarRootTransition.eval_reflect t⁻¹ w U hU,
    inv_inv,(t⁻¹.isUnit.pow l).mul_left_dvd,(t⁻¹.isUnit.pow w).dvd_mul_left]
  exact hd

/-- A single forward interpolation identity already supplies the inverse-chart
interpolants. Their parameter degrees are the ones used to clear denominators. -/
theorem interpolate_inverse [DecidableEq K] (G : Finset K) (hG : G.Nonempty)
    (hne : ∀ t ∈ G, t ≠ 0) (f U Q B : Biv) (l w : ℕ)
    (hf : f.natDegree ≤ l) (hU : U.natDegree ≤ w) (hsize : w<G.card+l)
    (forward : U = f*Q + Lagrange.nodal G C*B) :
    ∃ Qt Bt : Biv, reflect w U = reflect l f * Qt +
      Lagrange.nodal G (fun t => (C t⁻¹ : K[X]))*Bt ∧
      Qt.natDegree < G.card ∧ (Bt=0 ∨ Bt.natDegree<l) := by
  classical
  let Z := G.image Inv.inv
  have hc : Z.card = G.card := Finset.card_image_of_injective _ inv_injective
  have hdiv (s : K) (hs : s ∈ Z) : (reflect l f).eval (C s) ∣ (reflect w U).eval (C s) := by
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
    let v : K[X]ˣ := Units.map (C : K →+* K[X]).toMonoidHom (Units.mk0 t (hne t ht))
    have hd : f.eval (C t) ∣ U.eval (C t) := by
      rw [forward,eval_add,eval_mul,eval_mul,Lagrange.eval_nodal_at_node ht,zero_mul,add_zero]
      exact dvd_mul_right _ _
    exact inverse_fiber f U v hf hU hd
  obtain ⟨Qt,Bt,he,hq,hb⟩ :=
    ArkLib.ProximityGap.Frontier.ApolarFiberInterpolation.interpolate_fiber_quotients
      Z (hG.image _) (reflect l f) (reflect w U) l
      (natDegree_reflect_le.trans (max_le le_rfl hf))
      ((natDegree_reflect_le.trans (max_le le_rfl hU)).trans_lt (hc ▸ hsize)) hdiv
  refine ⟨Qt,Bt,?_,hc ▸ hq,hb⟩
  simpa only [Z,Polynomial.algebraMap_eq,nodal_inverse_image] using he

/-- Once the coordinate charts put B and Bt below the locator degree, the
negative parameter transition kills the two original interpolation remainders. -/
theorem vanish_of_cleared (f B Bt : Biv) (u : K[X]ˣ) {m k : ℕ} (hk : 0<k)
    (hb : (Bivariate.swap B).natDegree < f.natDegree)
    (hbt : (Bivariate.swap Bt).natDegree < f.natDegree) (hm : Bt.natDegree ≤ m)
    (h : f ∣ C 1*reverseCoeffs m (Bivariate.swap (C (u:K[X])*Bt)) -
      C (X^(m+k))*Bivariate.swap B) : B=0 ∧ Bt=0 := by
  have hu := unit_rescale_degrees u Bt
  have hc (j : ℕ) : ((Bivariate.swap (C (u:K[X])*Bt)).coeff j).natDegree ≤ m := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro v hv
    rw [swap_coeff, coeff_eq_zero_of_natDegree_lt ((hu.1.trans_le hm).trans_lt hv),coeff_zero]
  obtain ⟨hb0,hbt0⟩ := negative_twist hk hb (hu.2.trans_lt hbt) hc h
  have hs : C (u:K[X])*Bt = 0 := Bivariate.swap.injective (by simpa using hbt0)
  exact ⟨Bivariate.swap.injective (by simpa using hb0),
    (mul_eq_zero.mp hs).resolve_left (C_ne_zero.mpr u.ne_zero)⟩

#print axioms inverse_fiber
#print axioms interpolate_inverse
#print axioms reverse_row_weight
#print axioms nodal_inverse_image
#print axioms vanish_of_cleared
#print axioms unit_rescale_degrees
#print axioms nodal_reverse
#print axioms cleared_cubic_remainders
#print axioms negative_dvd
#print axioms representative_reversed
#print axioms cubic_reversed
end ProximityGap.ApolarParameterTransition
