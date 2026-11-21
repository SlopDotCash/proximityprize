/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.FiniteNormalizationColength
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Padded resultant orders in a common tame parameter

The fixed nominal degree of the second argument is allowed to exceed the
degree after specialization. The sum counts formal roots with multiplicity.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset PowerSeries
open scoped PowerSeries BigOperators

namespace ArkLib.ProximityGap.Frontier.TameResultantOrders

open FiniteNormalizationColength

variable {K ι : Type*} [Field K] [Fintype ι]

/-- For any splitting over a power coordinate, the padded resultant equals
the product of the literal substituted values on every sheet. -/
theorem expanded_resultant (F G : K⟦X⟧[X]) (q : ℕ) (hG : G.natDegree ≤ q)
    {n : ℕ} (hn : n ≠ 0) (y : ι → K⟦X⟧)
    (hF : F.map (PowerSeries.expand n hn (R := K)).toRingHom = ∏ i, (Polynomial.X-Polynomial.C (y i))) :
    let e := (PowerSeries.expand n hn (R := K)).toRingHom
    e (F.resultant G (Fintype.card ι) q) = ∏ i, (G.map e).eval (y i) := by
  classical
  let e := (PowerSeries.expand n hn (R := K)).toRingHom
  change e (F.resultant G (Fintype.card ι) q) = _
  rw [← Polynomial.resultant_map_map F G (Fintype.card ι) q e, show F.map e = _ from hF]
  have hm : ∀ i ∈ (univ : Finset ι), (Polynomial.X-Polynomial.C (y i)).Monic := fun i _ => monic_X_sub_C _
  have hd := Polynomial.natDegree_prod_of_monic univ (fun i => Polynomial.X-Polynomial.C (y i)) hm
  simp only [natDegree_X_sub_C, sum_const, card_univ, smul_eq_mul, mul_one] at hd
  have hg := (Polynomial.natDegree_map_le (f := e) (p := G)).trans hG
  rw [← hd, resultant_prod_left]
  · simp only [natDegree_X_sub_C]
    exact prod_congr rfl fun i _ => resultant_X_sub_C_left (G.map e) q (y i) hg
  · simp
  · exact hg

/-- Multiplying the ordinary local resultant order by the parameter degree
gives the sum of the sheet valuations, including zero factors at infinity. -/
theorem resultant_order_sum (F G : K⟦X⟧[X]) (q : ℕ) (hG : G.natDegree ≤ q)
    {n : ℕ} (hn : n ≠ 0) (y : ι → K⟦X⟧)
    (hF : F.map (PowerSeries.expand n hn (R := K)).toRingHom = ∏ i, (Polynomial.X-Polynomial.C (y i))) :
    let e := (PowerSeries.expand n hn (R := K)).toRingHom
    n • (F.resultant G (Fintype.card ι) q).order = ∑ i, ((G.map e).eval (y i)).order := by
  have h := congrArg PowerSeries.order (expanded_resultant F G q hG hn y hF)
  change (PowerSeries.expand n hn (F.resultant G (Fintype.card ι) q)).order = _ at h
  simpa only [PowerSeries.order_expand, PowerSeries.order_prod] using h

/-- A generic line through a fiber point computes the sum of truncated
contact orders in the common tame parameter. -/
theorem generic_line_contact [Infinite K] (F : K⟦X⟧[X]) {n : ℕ} (hn : n ≠ 0) (y : ι → K⟦X⟧)
    (hF : F.map (PowerSeries.expand n hn (R := K)).toRingHom = ∏ i, (Polynomial.X-Polynomial.C (y i)))
    (l : K) : ∃ c : K,
      n • (F.eval (PowerSeries.C l+c • PowerSeries.X)).order =
        ∑ i, min (y i-PowerSeries.C l).order (n : ℕ∞) := by
  classical
  obtain ⟨c,hc⟩ := exists_generic_polar (fun i => y i-PowerSeries.C l)
    (fun _ => -(PowerSeries.X^n : K⟦X⟧)) (fun _ => Or.inr (neg_ne_zero.mpr (pow_ne_zero _ PowerSeries.X_ne_zero)))
  let e := (PowerSeries.expand n hn (R := K)).toRingHom
  let v := PowerSeries.C l+c • (PowerSeries.X : K⟦X⟧)
  have h := congrArg (fun f : K⟦X⟧[X] => f.eval (e v)) hF
  rw [Polynomial.eval_map, Polynomial.eval₂_hom] at h
  rw [Polynomial.eval_prod] at h
  have h' := congrArg PowerSeries.order h
  change (PowerSeries.expand n hn (F.eval v)).order = _ at h'
  simp only [PowerSeries.order_expand, PowerSeries.order_prod] at h'
  refine ⟨c, h'.trans (sum_congr rfl (fun i _ => ?_))⟩
  rw [eval_sub, eval_X, eval_C]
  have hv : e v = PowerSeries.C l + c • (PowerSeries.X^n : K⟦X⟧) := by
    dsimp [e,v]
    rw [map_add, PowerSeries.expand_C, PowerSeries.expand_smul, PowerSeries.expand_X]
  rw [hv, ← PowerSeries.order_neg]
  convert (hc i).2 using 1
  · congr 1
    rw [smul_neg]
    abel
  · simp only [PowerSeries.order_neg, PowerSeries.order_X_pow]

/-- Generic contact on projective sheets. A sheet over infinity has
zero contact with every finite section. -/
theorem generic_projective_line_contact [Infinite K] (F : K⟦X⟧[X]) {n : ℕ} (hn : n ≠ 0)
    (a b : ι → K⟦X⟧) (ha : ∀ i, a i ≠ 0) (hab : ∀ i, IsCoprime (b i) (a i))
    (u : K⟦X⟧) (hu : IsUnit u)
    (hF : F.map (PowerSeries.expand n hn (R := K)).toRingHom =
      Polynomial.C u*∏ i, (Polynomial.C (a i)*Polynomial.X-Polynomial.C (b i)))
    (l : K⟦X⟧) : ∃ c : K,
      n • (F.eval (l+c • PowerSeries.X)).order =
        ∑ i, min ((PowerSeries.expand n hn l)*(a i)-b i).order (n : ℕ∞) := by
  classical
  let e := (PowerSeries.expand n hn (R := K)).toRingHom
  let U (i : ι) := e l*a i-b i
  let V (i : ι) := PowerSeries.X^n*a i
  obtain ⟨c,hc⟩ := exists_generic_polar U V (fun i => Or.inr (mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (ha i)))
  let v := l+c • (PowerSeries.X : K⟦X⟧)
  have h := congrArg (fun f : K⟦X⟧[X] => f.eval (e v)) hF
  rw [Polynomial.eval_map, Polynomial.eval₂_hom] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X] at h
  have ho := congrArg PowerSeries.order h
  change (PowerSeries.expand n hn (F.eval v)).order = _ at ho
  have hu' : u.order = 0 := by
    by_contra! h
    exact (PowerSeries.isUnit_iff_constantCoeff.mp hu).ne_zero
      (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp h)
  rw [PowerSeries.order_expand, PowerSeries.order_mul, hu', zero_add, PowerSeries.order_prod] at ho
  refine ⟨c, ho.trans (sum_congr rfl (fun i _ => ?_))⟩
  have hv : e v = e l + c • (PowerSeries.X^n : K⟦X⟧) := by
    dsimp [e,v]
    rw [map_add, PowerSeries.expand_smul, PowerSeries.expand_X]
  have hi : a i*(e v)-b i = U i+c • V i := by
    dsimp [U,V]
    rw [hv, ← smul_mul_assoc]
    ring
  rw [hi, (hc i).2]
  change min (U i).order (V i).order = min (U i).order n
  by_cases h₀ : (a i).order = 0
  · simp [V, PowerSeries.order_mul, PowerSeries.order_X_pow, h₀]
  · have hacc := PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp h₀
    have hbcc : PowerSeries.constantCoeff (b i) ≠ 0 := by
      rintro hz
      obtain ⟨x,z,hh⟩ := hab i
      have h' := congrArg (PowerSeries.constantCoeff (R := K)) hh
      simp [hz,hacc] at h'
    have hu₀ : (U i).order = 0 := by
      by_contra! h
      have h' := PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp h
      simp [U, hacc, hbcc] at h'
    simp [hu₀]

#print axioms generic_projective_line_contact
#print axioms expanded_resultant
#print axioms resultant_order_sum
#print axioms generic_line_contact

end ArkLib.ProximityGap.Frontier.TameResultantOrders
