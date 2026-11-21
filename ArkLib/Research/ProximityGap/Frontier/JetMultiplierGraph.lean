/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PolynomialJetConstraintSpace

/-! # Intrinsic jet identities vanish on actual selected polynomial sections

A polynomial multiplier identity before specialization implies a graph root of
the full specified multiplicity at each received agreement. A degree-bounded
section with sufficiently many such sites consequently vanishes identically.
-/

set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped BigOperators Matrix

namespace ArkLib.ProximityGap.Frontier.JetMultiplierGraph

open TruncatedJetMultipliers

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The monomial multiplier polynomial encoded by a jet-column vector. -/
def multiplier {ν : ℕ} (q : JetIdx ν → R) : R[X][X] :=
  ∑ c, monomialMultiple (1 : R[X][X]) c * C (C (q c))

private theorem jet_mul_const (G : R[X][X]) (z : R) {μ : ℕ} (i : JetIdx μ) :
    jet (G*C (C z)) i = jet G i*z := by
  simp only [jet, coeff_mul_C]

/-- Columns times a vector are the mixed jet of the actual product. -/
theorem jet_product {μ ν : ℕ} (G : R[X][X]) (q : JetIdx ν → R) (i : JetIdx μ) :
    jet (G*multiplier q) i = (columns μ ν G).mulVec q i := by
  have hterm (c : JetIdx ν) :
      G * (monomialMultiple 1 c * C (C (q c))) = monomialMultiple G c * C (C (q c)) := by
    simp only [monomialMultiple,one_mul,mul_assoc]
  have hsum (f : JetIdx ν → R[X][X]) : jet (∑ c, f c) i = ∑ c, jet (f c) i := by
    simp only [jet,finsetSum_coeff]
  rw [multiplier,Finset.mul_sum,hsum]
  change _ = ∑ c, jet (monomialMultiple G c) i*q c
  simp only [hterm,jet_mul_const]

/-- Zero triangular jet implies order at least μ along any graph through the origin. -/
theorem pow_dvd_graph {μ : ℕ} (G : R[X][X]) (q : R[X]) (hq : Polynomial.X ∣ q)
    (h : ∀ i : JetIdx μ, jet G i = 0) : (Polynomial.X : R[X])^μ ∣ G.eval q := by
  rw [eval_eq_sum,sum_def]
  apply Finset.dvd_sum
  intro v _
  have hc : (Polynomial.X : R[X])^(μ-v) ∣ G.coeff v := by
    apply X_pow_dvd_iff.mpr
    intro t ht
    let idx : JetIdx μ := ⟨⟨v+t,by omega⟩,⟨v,by change v < v+t+1; omega⟩⟩
    have he := h idx
    simpa only [jet,idx,Nat.add_sub_cancel_left] using he
  have hh := mul_dvd_mul hc (pow_dvd_pow_of_dvd hq v)
  rw [← pow_add] at hh
  exact (pow_dvd_pow _ (show μ ≤ (μ-v)+v by omega)).trans hh

/-- Change the origin in both variables. -/
def shift (G : R[X][X]) (a w : R) : R[X][X] :=
  (G.taylor (C w)).map (taylorAlgHom a).toRingHom

private theorem shift_graph (G : R[X][X]) (a w : R) (q : R[X]) :
    (shift G a w).eval ((q-C w).taylor a) = (G.eval q).taylor a := by
  change ((G.taylor (C w)).map (taylorAlgHom a).toRingHom).eval
    ((taylorAlgHom a).toRingHom (q-C w)) = _
  rw [eval_map_apply,taylor_eval_sub]
  rfl

/-- Apply a coefficient homomorphism to both indeterminates of the plane equation. -/
def mapPlane (f : R →+* S) (G : R[X][X]) : S[X][X] := G.map (mapRingHom f)

theorem mapPlane_shift (f : R →+* S) (G : R[X][X]) (a w : R) :
    mapPlane f (shift G a w) = shift (mapPlane f G) (f a) (f w) := by
  apply Polynomial.ext
  intro i
  simp only [mapPlane,shift,coeff_map,coe_mapRingHom]
  change ((((G.taylor (C w)).coeff i).taylor a).map f) =
    ((((G.map (mapRingHom f)).taylor (C (f w))).coeff i).taylor (f a))
  rw [map_taylor]
  congr 1
  have he := congrArg (fun W : S[X][X] => W.coeff i) (map_taylor G (C w) (mapRingHom f))
  simpa only [coeff_map,coe_mapRingHom,map_C] using he

theorem mapPlane_jet (f : R →+* S) (G : R[X][X]) {μ : ℕ} (i : JetIdx μ) :
    jet (mapPlane f G) i = f (jet G i) := by simp only [mapPlane,jet,coeff_map,coe_mapRingHom]

private theorem mapPlane_mul (f : R →+* S) (G B : R[X][X]) :
    mapPlane f (G*B) = mapPlane f G * mapPlane f B := Polynomial.map_mul _

/-- A polynomial-vector identity in the scalar before specialization supplies
multiplicity μ at each received agreement, including exceptional labels. -/
theorem specialized_site {K : Type} [Field K] {μ ν : ℕ} (z a w₀ w₁ : K)
    (F P : K[X][X][X]) (q : K[X]) (hF : (mapPlane (evalRingHom z) F).eval q = 0)
    (ha : q.eval a = w₀+z*w₁) (v : JetIdx ν → K[X])
    (hjet : jet (shift P (C a) (C w₀+Polynomial.X*C w₁)) =
      (columns μ ν (shift F (C a) (C w₀+Polynomial.X*C w₁))).mulVec v) :
    (Polynomial.X-C a)^μ ∣ (mapPlane (evalRingHom z) P).eval q := by
  let φ := evalRingHom z
  let w := C w₀+Polynomial.X*C w₁
  have hw : φ w = w₀+z*w₁ := by
    change (C w₀+Polynomial.X*C w₁).eval z = _
    rw [eval_add,eval_C,eval_mul,eval_X,eval_C]
  let F' := mapPlane φ F
  let P' := mapPlane φ P
  let B := mapPlane φ (multiplier v)
  have he (i : JetIdx μ) : jet (shift P' a (φ w) - shift F' a (φ w)*B) i = 0 := by
    have hh := congrArg φ (congrFun hjet i)
    rw [← jet_product] at hh
    rw [← mapPlane_jet, ← mapPlane_jet, mapPlane_mul, mapPlane_shift, mapPlane_shift] at hh
    simp only [φ,coe_evalRingHom,eval_C] at hh
    change ((shift P' a (φ w) - shift F' a (φ w)*B).coeff i.2.val).coeff
      (i.1.val-i.2.val) = 0
    rw [coeff_sub,coeff_sub,sub_eq_zero]
    exact hh
  have hx : Polynomial.X ∣ (q-C (φ w)).taylor a := by
    rw [X_dvd_iff, taylor_coeff_zero,eval_sub,eval_C,sub_eq_zero]
    exact ha.trans hw.symm
  have hv := pow_dvd_graph _ _ hx he
  rw [eval_sub,eval_mul, shift_graph,shift_graph,show F'.eval q=0 from hF, map_zero,
    zero_mul,sub_zero] at hv
  have hh := map_dvd (taylorAlgHom (-a)) hv
  simpa only [map_pow,taylorAlgHom_apply,taylor_X,C_neg,← sub_eq_add_neg,taylor_taylor,
    neg_add_cancel,add_neg_cancel,taylor_zero] using hh

/-- Every selected polynomial with enough agreements is a genuine root of the
specialized auxiliary section, on arbitrary distinct received sites. -/
theorem selected_section {K : Type} [Field K] {μ : ℕ} (z : K) (D : Finset K)
    (u v : K → K) (F P : K[X][X][X]) (q : K[X])
    (hF : (mapPlane (evalRingHom z) F).eval q = 0)
    (hagree : ∀ a ∈ D, q.eval a = u a+z*v a)
    (hjets : ∀ a ∈ D, ∃ ν, ∃ b : JetIdx ν → K[X],
      jet (shift P (C a) (C (u a)+Polynomial.X*C (v a))) =
        (columns μ ν (shift F (C a) (C (u a)+Polynomial.X*C (v a)))).mulVec b)
    (hdeg : ((mapPlane (evalRingHom z) P).eval q).natDegree < D.card*μ) :
    (mapPlane (evalRingHom z) P).eval q = 0 := by
  by_contra hn
  have hh := SylvesterLocalMultiplicity.sum_local_orders_le_natDegree _ hn D (fun _ => μ) (by
    intro a ha
    obtain ⟨ν,b,hb⟩ := hjets a ha
    exact specialized_site z a (u a) (v a) F P q hF (hagree a ha) b hb)
  exact (not_le_of_gt hdeg) (by simpa only [Finset.sum_const,smul_eq_mul] using hh)

end ArkLib.ProximityGap.Frontier.JetMultiplierGraph

open ArkLib.ProximityGap.Frontier.JetMultiplierGraph in
#print axioms selected_section
