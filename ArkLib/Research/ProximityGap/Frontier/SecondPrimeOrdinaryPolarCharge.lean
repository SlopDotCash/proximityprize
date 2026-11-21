/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeOrdinarySiteBudget
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeReceivedJetColumns

/-! # The two ordinary polar resultants of an actual received cubic -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeOrdinaryPolarCharge

open Polynomial Finset
open scoped Differential
open GenericProjectivePolarGcd CanonicalQuarticSiteOrder WeightedHessianResultant
open ScalarHessianLocalOrder MovingCubicVanishingBranch ReceivedPolarContacts
open SecondPrimeOrdinarySiteBudget
set_option maxRecDepth 4096

variable {K k I : Type} [Field K] [Field k] [Fintype I]

/-- Raw ordinary projective polar resultant at an actual constant slope. -/
noncomputable def polarRes (F : (RatFunc k)[X][X]) (c : k) : (RatFunc k)[X] :=
  F.resultant (polar (dx F) F.derivative (RatFunc.C c)) 3 3

private theorem polar_degree_bound (F : K[X][X]) (d W : ℕ)
    (hW : Bivariate.natWeightedDegree F 1 d ≤ W) (c : K) :
    (F.resultant (polar (dx F) F.derivative c) 3 3).natDegree ≤ 6 * W := by
  have hcoeff (i : ℕ) : (F.coeff i).natDegree ≤ W := by
    by_cases hz : F.coeff i = 0
    · simp [hz]
    · have h := (ArkLib.BivariateDegreeToolkit.weight_coeff_le_natWeightedDegree F 1 d
        (mem_support_iff.mpr hz)).trans hW
      omega
  have hpolar (i : ℕ) : ((polar (dx F) F.derivative c).coeff i).natDegree ≤ W := by
    rw [polar, coeff_add, coeff_dx, coeff_C_mul, coeff_derivative]
    apply natDegree_add_le_of_degree_le ((natDegree_derivative_le _).trans
      ((Nat.sub_le _ _).trans (hcoeff _)))
    apply (natDegree_C_mul_le _ _).trans
    exact (natDegree_mul_le.trans (by simp [hcoeff]))
  have h := weighted_resultant_le F (polar (dx F) F.derivative c) 3 3 0 W W
    (fun i _ => by simpa using hcoeff i) (fun i _ => by simpa using hpolar i)
  omega

open Classical in
/-- Two distinct nonexceptional slopes achieve the ordinary-polar local-to-global bound
on the original scalar-rational cubic and the actual values on each received line. -/
theorem two_polar_budget [Infinite k] (p : ℕ) [CharP k p] (hp : 3 < p)
    (F : (RatFunc k)[X][X]) (hb : F.natDegree = 3) (hprim : F.IsPrimitive)
    (hi : Irreducible (genericEquation F))
    (hnd : ¬ genericEquation F ∣ genericEquation (scalarFieldHessian F))
    (d W : ℕ) (hlo : 3 * d ≤ W) (hw : Bivariate.natWeightedDegree F 1 d ≤ W)
    (hchar : 6 * W < p) (dom : I ↪ k) (u v : I → k) (except : Finset k) :
    ∃ a ∉ except, ∃ b ∉ insert a except, polarRes F a ≠ 0 ∧ polarRes F b ≠ 0 ∧
      3 * (∑ i, siteOrder F (RatFunc.C (dom i))
        (C (RatFunc.C (u i) + RatFunc.X * RatFunc.C (v i)))) +
        2 * (GCDMonoid.gcd (polarRes F a) (polarRes F b)).natDegree + 39 * d ≤
      2 * Fintype.card I + 20 * W := by
  classical
  let _ : Differential k[X] := coordinateDifferential
  let _ : Differential (RatFunc k) := scalarFieldDifferential k
  let _ : Differential (RatFunc k)[X] := ImplicitDerivativeBidegree.coefficientDifferential
  have small_cast (n : ℕ) (hn : 0 < n) (hlt : n < p) : (n : RatFunc k) ≠ 0 :=
    fun h => hlt.not_ge (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff (RatFunc k) p n).mp h))
  have h₂ := small_cast 2 (by decide) (by omega)
  have h₃ := small_cast 3 (by decide) hp
  let χ := algebraMap (RatFunc k)[X] (RatFunc (RatFunc k))
  have hinj := RatFunc.algebraMap_injective (RatFunc k)
  have hdeg : (F.map χ).natDegree = 3 := (natDegree_map_eq_of_injective hinj F).trans hb
  have hsep := irreducible_cubic_separable (F.map χ) hi hdeg
    (fun h => hp.not_ge (Nat.le_of_dvd (by decide : 0 < 3)
      ((CharP.cast_eq_zero_iff (RatFunc (RatFunc k)) p 3).mp h)))
  have hV := padded_ne_zero χ hinj F F.derivative 3 ((natDegree_derivative_le F).trans (by omega))
    hi (by rw [← derivative_map]; exact hi.coprime_iff_not_dvd.mp hsep)
  have hH := padded_ne_zero χ hinj F (hessian F) 7 (CubicSheetExcess.hessian_degree F hb.le) hi hnd
  rw [hb] at hV hH
  let e := dom.trans (⟨RatFunc.C, RatFunc.C_injective⟩ : k ↪ RatFunc k)
  let w (i : I) := RatFunc.C (u i) + RatFunc.X * RatFunc.C (v i)
  let l := Function.extend e w (fun _ => 0)
  have he (i : I) : l (e i) = w i := e.injective.extend_apply _ _ i
  have hC (a : k) : (RatFunc.C a)′ = 0 := by
    change (algebraMap k[X] (RatFunc k) (C a))′ = 0
    rw [GenericDifferentialFunctionField.fraction_deriv_algebraMap k[X] (RatFunc k)]
    change algebraMap k[X] (RatFunc k) (C a).derivative = 0
    simp
  have hZ : (RatFunc.X : RatFunc k)′ = 1 := by
    change (algebraMap k[X] (RatFunc k) Polynomial.X)′ = 1
    rw [GenericDifferentialFunctionField.fraction_deriv_algebraMap k[X] (RatFunc k)]
    change algebraMap k[X] (RatFunc k) (Polynomial.X : k[X]).derivative = 1
    simp
  have hdomain : ∀ a ∈ univ.map e, a′ = 0 := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := mem_map.mp ha
    exact hC _
  have hline : ∀ a ∈ univ.map e, (l a)′′ = 0 := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := mem_map.mp ha
    rw [he]
    simp [w, Derivation.leibniz, smul_eq_mul, hC, hZ]
  have one := raw_budget RatFunc.C p h₂ h₃ F hb hprim hV hH (1 : (RatFunc k)[X]) one_ne_zero
    (by simp; omega) except (univ.map e) l hdomain hline
  obtain ⟨a, ha, hA, _⟩ := one
  have hAp := (polar_degree_bound F d W hw (RatFunc.C a)).trans_lt hchar
  obtain ⟨b, hbe, hB, hbudget⟩ := raw_budget RatFunc.C p h₂ h₃ F hb hprim hV hH
    (polarRes F a) hA hAp (insert a except) (univ.map e) l hdomain hline
  have hweight := CubicPolarSiteBudget.weighted_degree_budget F hb d W hlo hw
  simp only [sum_map, card_map, card_univ, he] at hbudget
  refine ⟨a, ha, b, hbe, hA, hB, ?_⟩
  change 3 * (∑ i, siteOrder F (e i) (C (w i))) +
    2 * (GCDMonoid.gcd (polarRes F a) (polarRes F b)).natDegree + 39 * d ≤ _
  have hsmall : 2 * Fintype.card I + 4 * F.leadingCoeff.natDegree +
      (F.resultant (hessian F) 3 7).natDegree + 39 * d ≤ 2 * Fintype.card I + 20 * W := by omega
  have hfinal := (Nat.add_le_add_right hbudget (39 * d)).trans hsmall
  simp only [polarRes, e, Function.Embedding.trans_apply,
    Function.Embedding.coeFn_mk, w] at hfinal ⊢
  omega

open Classical in
/-- A common divisor of the two actual polars pays the ordinary charge. This formulation on a
finite coordinate set may be applied directly after a common projective coordinate change. -/
theorem charge_of_persistent_gcd [Infinite k] (p : ℕ) [CharP k p] (hp : 3 < p)
    (F : (RatFunc k)[X][X]) (hb : F.natDegree = 3) (hprim : F.IsPrimitive)
    (hi : Irreducible (genericEquation F))
    (hnd : ¬ genericEquation F ∣ genericEquation (scalarFieldHessian F))
    (d W defect : ℕ) (hlo : 3 * d ≤ W) (hw : Bivariate.natWeightedDegree F 1 d ≤ W)
    (hchar : 6 * W < p) (D : Finset k) (u v : k → k)
    (hgc : ∀ a b : k, a ≠ b → polarRes F a ≠ 0 → polarRes F b ≠ 0 →
      2 * (W - d) ≤ (GCDMonoid.gcd (polarRes F a) (polarRes F b)).natDegree + defect) :
    3 * (∑ x ∈ D, siteOrder F (RatFunc.C x)
        (C (RatFunc.C (u x) + RatFunc.X * RatFunc.C (v x)))) + 35 * d ≤
      2 * D.card + 16 * W + 2 * defect := by
  classical
  let e : D ↪ k := ⟨Subtype.val, Subtype.val_injective⟩
  obtain ⟨a, _, b, hab, hA, hB, hsum⟩ := two_polar_budget p hp F hb hprim hi hnd d W hlo hw hchar
    e (fun i => u i) (fun i => v i) ∅
  have hneq : a ≠ b := fun h => hab (h ▸ mem_insert_self ..)
  have hg := hgc a b hneq hA hB
  let r (x : k) := siteOrder F (RatFunc.C x) (C (RatFunc.C (u x) + RatFunc.X * RatFunc.C (v x)))
  change 3 * (∑ i : D, r i.val) + 2 *
    (GCDMonoid.gcd (polarRes F a) (polarRes F b)).natDegree + 39 * d ≤
    2 * Fintype.card D + 20 * W at hsum
  rw [D.sum_coe_sort (f := r), Fintype.card_coe] at hsum
  change 3 * (∑ i ∈ D, r i) + 35 * d ≤ _
  omega

/-- Identify the multiplicity in the ordinary-polar sum with the actual received order in the
jet interpolation theorem, including after changing coordinates. -/
theorem receivedOrder_eq (A : k[X][X][X]) (x u v : k) :
    IntrinsicReceivedSections.receivedOrder A x u v =
      siteOrder (JetMultiplierGraph.mapPlane (algebraMap k[X] (RatFunc k)) A) (RatFunc.C x)
        (C (RatFunc.C u + RatFunc.X * RatFunc.C v)) := by
  unfold IntrinsicReceivedSections.receivedOrder IntrinsicReceivedSections.received
  rw [map_add, map_mul]
  rfl

open Classical in
/-- The genuine received jet multiplicities satisfy the ordinary charge over any transformed
domain whenever its two polar resultants satisfy the persistent common-divisor estimate. -/
theorem received_charge_of_persistent_gcd [Infinite k] (p : ℕ) [CharP k p] (hp : 3 < p)
    (A : k[X][X][X]) (F : (RatFunc k)[X][X])
    (hF : F = JetMultiplierGraph.mapPlane (algebraMap k[X] (RatFunc k)) A)
    (hb : F.natDegree = 3) (hprim : F.IsPrimitive) (hi : Irreducible (genericEquation F))
    (hnd : ¬ genericEquation F ∣ genericEquation (scalarFieldHessian F))
    (d W defect : ℕ) (hlo : 3 * d ≤ W) (hw : Bivariate.natWeightedDegree F 1 d ≤ W)
    (hchar : 6 * W < p) (D : Finset k) (u v : k → k)
    (hgc : ∀ a b : k, a ≠ b → polarRes F a ≠ 0 → polarRes F b ≠ 0 →
      2 * (W - d) ≤ (GCDMonoid.gcd (polarRes F a) (polarRes F b)).natDegree + defect) :
    3 * (∑ x ∈ D, IntrinsicReceivedSections.receivedOrder A x (u x) (v x)) + 35 * d ≤
      2 * D.card + 16 * W + 2 * defect := by
  subst F
  simp only [receivedOrder_eq]
  exact charge_of_persistent_gcd p hp _ hb hprim hi hnd d W defect hlo hw hchar D u v hgc

end ArkLib.ProximityGap.Frontier.SecondPrimeOrdinaryPolarCharge
