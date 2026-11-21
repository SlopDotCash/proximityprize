/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCoordinateWeight
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticInterpolation
import Mathlib.RingTheory.Polynomial.Content

/-! # Every rich label survives removal of the value content

A nonzero coordinate coefficient of the content vanishes wherever the entire
content vanishes on a received scalar line. Multiplying a primitive section by
that coefficient restores every agreement and costs at most the weight removed.
-/
set_option autoImplicit false
noncomputable section
open Finset Polynomial
namespace ArkLib.ProximityGap.Frontier.PrimitiveReceivedInterpolation
open SecondPrimeCoordinateWeight
variable {K I : Type} [Field K]

/-- Restrict a trivariate surface to the affine line at a fixed coordinate. -/
def site (x a b : K) : Surface K →+* K[X] :=
  eval₂RingHom (mapRingHom (evalRingHom x)) (C a + X*C b)

/-- Substituting the received section and then the site agrees with the other order. -/
theorem site_section (P : Surface K) (x a b z : K) (q : K[X]) (hq : q.eval x=a+z*b) :
    ((site x a b P).eval z) = (P.eval₂ (evalRingHom (C z)) q).eval x := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ => simp [map_add,eval₂_add,ihP,ihQ]
  | monomial j f =>
    have hf : (f.map (evalRingHom x)).eval z=(f.eval (C z)).eval x := by
      simpa only [coe_evalRingHom,eval_C] using eval_map_apply (p:=f) (evalRingHom x) (C z)
    simp [site,eval₂_monomial,eval_add,eval_mul,hq,hf]
    exact Or.inl (by rw [mul_comm b z])

/-- Specializing the scalar and a degree-d candidate respects the trivariate coordinate weight. -/
theorem section_degree (P : Surface K) (d : ℕ) (z : K) (q : K[X]) (hq : q.natDegree≤d) :
    (P.eval₂ (evalRingHom (C z)) q).natDegree≤weight d P := by
  classical
  rw [eval₂_eq_sum,sum_def]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj' : P.coeff j≠0 := mem_support_iff.mp hj
  have hd (i : ℕ) (hi : (P.coeff j).coeff i≠0) :
      ((P.coeff j).coeff i).natDegree+j*d≤weight d P :=
    coeff_weight_le d P (leadingCoeff_ne_zero.mpr hi)
  have hmax := hd _ (leadingCoeff_ne_zero.mpr hj')
  have hcoeff : ((P.coeff j).eval (C z)).natDegree≤weight d P-j*d := by
    rw [eval_eq_sum,sum_def]
    apply natDegree_sum_le_of_forall_le
    intro i hi
    have h := hd _ (mem_support_iff.mp hi)
    rw [← C_pow]
    exact (natDegree_mul_C_le ..).trans (by omega)
  have hpow : (q^j).natDegree≤j*d := (natDegree_pow_le ..).trans (Nat.mul_le_mul_left _ hq)
  exact (natDegree_mul_le ..).trans ((Nat.add_le_add hcoeff hpow).trans (by omega))

/-- For a value-independent factor, removing its full content preserves every
rich section of the original received rows. -/
theorem section_of_factor (dom : I ↪ K) (u₀ u₁ : I → K) {d t : ℕ}
    (Q P : Surface K) (V : K[X][X]) (hQ : Q≠0) (hfactor : Q=C V*P)
    (hw : weight d Q<t) (hlines : ∀ i, site (dom i) (u₀ i) (u₁ i) Q=0)
    (z : K) (q : K[X]) (hq : q.natDegree≤d) (S : Finset I) (hS : t≤S.card)
    (ha : ∀ i∈S, q.eval (dom i)=u₀ i+z*u₁ i) :
    P.eval₂ (evalRingHom (C z)) q=0 := by
  classical
  have hnP : P≠0 := fun h => hQ (by simp [hfactor,h])
  have hnV : V≠0 := fun h => hQ (by simp [hfactor,h])
  let g := V.coeff V.natDegree
  have hg : g≠0 := leadingCoeff_ne_zero.mpr hnV
  have hgW : g.natDegree≤weight d (C V) := by
    have h : (((C V : Surface K).coeff 0).coeff V.natDegree).coeff g.natDegree≠0 := by
      simpa [g] using leadingCoeff_ne_zero.mpr hg
    simpa using coeff_weight_le d (C V) h
  have hw' : g.natDegree+weight d P<t := by
    rw [hfactor,weight_mul d _ _ (C_ne_zero.mpr hnV) hnP] at hw
    omega
  let v := P.eval₂ (evalRingHom (C z)) q
  have hv : v.natDegree≤weight d P := section_degree P d z q hq
  have prodzero : g*v=0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f:=fun i : S => dom i.val)
      (dom.injective.comp Subtype.val_injective)
    · intro i
      rw [eval_mul,mul_eq_zero]
      have hi := hlines i.val
      rw [hfactor,map_mul] at hi
      rcases mul_eq_zero.mp hi with h0 | h0
      · left
        have hz : V.map (evalRingHom (dom i.val))=0 := by simpa [site] using h0
        simpa [g,coeff_map] using congrArg (fun f : K[X] => f.coeff V.natDegree) hz
      · right
        have h := congrArg (eval z) h0
        rwa [site_section P _ _ _ _ q (ha i.val i.property),eval_zero] at h
    · rw [Fintype.card_coe]
      exact (natDegree_mul_le ..).trans_lt (by omega)
  exact (mul_eq_zero.mp prodzero).resolve_left hg

/-- Pure-scalar and coordinate-dependent content may be removed simultaneously.
Every section is on the same primitive part with no exceptional labels. -/
theorem section_on_primPart [NormalizedGCDMonoid K[X][X]] (dom : I ↪ K) (u₀ u₁ : I → K) {d t : ℕ}
    (Q : Surface K) (hQ : Q≠0) (hw : weight d Q<t) (hlines : ∀ i, site (dom i) (u₀ i) (u₁ i) Q=0)
    (z : K) (q : K[X]) (hq : q.natDegree≤d) (S : Finset I) (hS : t≤S.card)
    (ha : ∀ i∈S, q.eval (dom i)=u₀ i+z*u₁ i) :
    Q.primPart.eval₂ (evalRingHom (C z)) q=0 :=
  section_of_factor dom u₀ u₁ Q Q.primPart Q.content hQ (eq_C_content_mul_primPart Q) hw hlines z q hq S hS ha

open SecondPrimeQuarticInterpolation
/-- The coefficient-indexed interpolation kernel gives genuine received-line identities for its surface. -/
theorem raw_site {s v d t : ℕ} (c : Monomials s v d t → K) (x a b : K) :
    site x a b (surface c)=receivedLine c x a b :=
  surface_received_line c x a b

/-- Every section meeting the agreement threshold survives the value-primitive
normalization of any nonzero first-order interpolation-kernel member. -/
theorem raw_primitive_section [NormalizedGCDMonoid K[X][X]] (dom : I ↪ K) (u₀ u₁ : I → K)
    {s v d t : ℕ} {c : Monomials s v d t → K} (hc : c≠0) (ht : 0<t)
    (hlines : ∀ i, receivedLine c (dom i) (u₀ i) (u₁ i)=0)
    (z : K) (q : K[X]) (hq : q.natDegree≤d) (S : Finset I) (hS : t≤S.card)
    (ha : ∀ i∈S, q.eval (dom i)=u₀ i+z*u₁ i) :
    (surface c).primPart.eval₂ (evalRingHom (C z)) q=0 := by
  apply section_on_primPart dom u₀ u₁ (surface c) (surface_ne_zero hc) _ _ z q hq S hS ha
  · have hw := weight_le_of_coeff d (surface c) (W:=t-1) (fun j i a hh => by
      have h := (surface_support c hh).2.2
      omega)
    omega
  · intro i
    rw [raw_site, hlines]

#print axioms raw_primitive_section
#print axioms section_on_primPart
#print axioms raw_site
#print axioms section_of_factor
end ArkLib.ProximityGap.Frontier.PrimitiveReceivedInterpolation
