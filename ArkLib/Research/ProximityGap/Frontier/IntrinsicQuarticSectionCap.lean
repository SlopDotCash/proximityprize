/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.QuarticIntrinsicAuxiliary

/-! # Actual scalar-label cap for a proper quartic

The padded resultant is nonzero over the double polynomial coefficient ring.
Swapping the coordinate and scalar variables only in that ring makes its scalar
degree visible and lets any common selected polynomial kill it there directly.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.IntrinsicQuarticSectionCap

open JetMultiplierGraph IntrinsicReceivedSections QuarticIntrinsicAuxiliary

variable {K : Type} [Field K]

/-- Swapping the coefficient variables turns total scalar/value height into
the coefficient bounds of a weighted Sylvester matrix. -/
private theorem swapped_height (F : K[X][X][X]) (m : ℕ) (hf : ScalarValueBound F m)
    (j : ℕ) (hn : (F.map Bivariate.swap.toRingEquiv.toRingHom).coeff j ≠ 0) :
    ((F.map Bivariate.swap.toRingEquiv.toRingHom).coeff j).natDegree + 1*j ≤ m := by
  classical
  let A := F.coeff j
  have ha : A ≠ 0 := by
    intro hz
    apply hn
    simp [coeff_map,show F.coeff j=0 from hz]
  have hcomp (l : ℕ) (hl : l ∈ A.support) : (A.coeff l).natDegree+j ≤ m :=
    hf j l (Polynomial.mem_support_iff.mp hl)
  have hj : j ≤ m := by
    have he := hcomp A.natDegree (natDegree_mem_support_of_nonzero ha)
    omega
  have hdeg : (Bivariate.swap A).natDegree ≤ m-j := by
    conv_lhs => rw [← sum_monomial_eq A,sum_def,map_sum]
    apply natDegree_sum_le_of_forall_le
    intro l hl
    rw [Bivariate.swap_monomial]
    have hL := hcomp l hl
    exact natDegree_mul_le.trans (by
      rw [natDegree_C,add_zero]
      exact natDegree_map_le.trans (by omega))
  rw [coeff_map,one_mul]
  change (Bivariate.swap A).natDegree+j ≤ m
  omega

/-- Scalar evaluation after swapping is coefficientwise scalar evaluation of
the original coordinate polynomial. The coordinate itself stays indeterminate. -/
private theorem eval_swap (H : K[X][X]) (z : K) :
    (Bivariate.swap H).eval (C z) = H.map (evalRingHom z) := by
  induction H using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add,eval_add,hp,hq,Polynomial.map_add]
  | monomial n c =>
    rw [Bivariate.swap_monomial,eval_mul,eval_map_apply,eval_C,map_monomial]
    exact C_mul_X_pow_eq_monomial ..

/-- A lower-value-degree nonzero auxiliary yields a common-label cap directly
from generic irreducibility, without switching rational-function fields. -/
theorem common_section_cap (F P : K[X][X][X]) {b a m s : ℕ}
    (ha : (mapPlane (algebraMap K[X] (RatFunc K)) F).natDegree = a)
    (hb : b < a) (hP : P ≠ 0) (hPb : P.natDegree ≤ b)
    (hir : Irreducible (MovingCubicVanishingBranch.genericEquation
      (mapPlane (algebraMap K[X] (RatFunc K)) F)))
    (hm : ScalarValueBound F m) (hs : ScalarValueBound P s)
    (L : Finset K) (q : K → K[X])
    (hroots : ∀ z ∈ L, (mapPlane (evalRingHom z) F).eval (q z) = 0 ∧
      (mapPlane (evalRingHom z) P).eval (q z) = 0) :
    L.card ≤ b*m + a*s - a*b := by
  classical
  let φ := algebraMap K[X] (RatFunc K)
  let ψ : K[X][X] →+* RatFunc (RatFunc K) :=
    (algebraMap (RatFunc K)[X] (RatFunc (RatFunc K))).comp (mapRingHom φ)
  have hi : Function.Injective ψ :=
    (RatFunc.algebraMap_injective (RatFunc K)).comp (Polynomial.map_injective φ (RatFunc.algebraMap_injective K))
  have hφ : Function.Injective (mapRingHom φ) := Polynomial.map_injective φ (RatFunc.algebraMap_injective K)
  have hf : F.natDegree = a := by
    change (F.map (mapRingHom φ)).natDegree = a at ha
    rwa [natDegree_map_eq_of_injective hφ] at ha
  have hg : Irreducible (F.map ψ) := by
    simpa only [MovingCubicVanishingBranch.genericEquation,mapPlane,Polynomial.map_map,φ,ψ] using hir
  have hnp : P.map ψ ≠ 0 := fun hz => hP ((Polynomial.map_injective ψ hi) (hz.trans (Polynomial.map_zero ψ).symm))
  have hnd : ¬F.map ψ ∣ P.map ψ := by
    intro hd
    have he := Polynomial.natDegree_le_of_dvd hd hnp
    rw [natDegree_map_eq_of_injective hi,natDegree_map_eq_of_injective hi,hf] at he
    omega
  let H := resultant F P a b
  have hn : H ≠ 0 := by
    change resultant F P a b ≠ 0
    rw [← hf]
    exact WeightedHessianResultant.padded_ne_zero ψ hi F P b hPb hg hnd
  let τ := (Bivariate.swap (R := K)).toRingEquiv.toRingHom
  have hdeg : (Bivariate.swap H).natDegree ≤ b*m+a*s-a*b := by
    change (τ (resultant F P a b)).natDegree ≤ _
    rw [← resultant_map_map]
    simpa only [Nat.mul_one] using (WeightedHessianResultant.weighted_resultant_le
      (F.map τ) (P.map τ) a b 1 m s (swapped_height F m hm) (swapped_height P s hs))
  by_contra! hlarge
  have hz : Bivariate.swap H = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun z : L => C (z:K))
      (C_injective.comp Subtype.val_injective)
    · intro z
      rw [eval_swap]
      exact map_resultant_eq_zero_of_common_root (mapRingHom (evalRingHom (z:K))) F P
        hf.le hPb (Or.inl (by omega)) (q z) (hroots z z.property).1 (hroots z z.property).2
    · simpa using hdeg.trans_lt hlarge
  exact hn (Bivariate.swap.injective (hz.trans (map_zero _).symm))

/-- Every scalar label whose selected polynomial is rich on this actual proper
quartic belongs to a set of size at most 268435546. -/
theorem secondPrime_proper_quartic_label_cap (F : K[X][X][X]) (D : Finset K)
    (hn : D.card = 1073741824) (u v : K → K) (hscalar : ScalarValueBound F 34)
    (hprim : (mapPlane (algebraMap K[X] (RatFunc K)) F).IsPrimitive)
    (hfour : (mapPlane (algebraMap K[X] (RatFunc K)) F).natDegree = 4)
    (hir : Irreducible (MovingCubicVanishingBranch.genericEquation
      (mapPlane (algebraMap K[X] (RatFunc K)) F)))
    (hnd : ¬MovingCubicVanishingBranch.genericEquation (mapPlane (algebraMap K[X] (RatFunc K)) F)
      ∣ MovingCubicVanishingBranch.genericEquation (CanonicalQuarticSiteOrder.scalarFieldHessian
        (mapPlane (algebraMap K[X] (RatFunc K)) F)))
    (hw : Polynomial.Bivariate.natWeightedDegree (mapPlane (algebraMap K[X] (RatFunc K)) F)
      1 67108863 ≤ 302954072) (L : Finset K) (q : K → K[X])
    (hsel : ∀ z ∈ L, (q z).natDegree ≤ 67108863 ∧
      (mapPlane (evalRingHom z) F).eval (q z) = 0 ∧
      ∃ H ⊆ D, 357913943 ≤ H.card ∧ ∀ a ∈ H, (q z).eval a = u a+z*v a) :
    L.card ≤ 268435546 := by
  obtain ⟨P,hP,hy,hs,hall⟩ := secondPrime_quartic_auxiliary F D hn u v hscalar hprim hfour hir hnd hw
  apply common_section_cap F P hfour (by decide : 3 < 4) hP hy hir hscalar hs L q
  intro z hz
  obtain ⟨hd,hF,H,hHD,ht,ha⟩ := hsel z hz
  exact ⟨hF,hall z (q z) H hHD ht hd hF ha⟩

end ArkLib.ProximityGap.Frontier.IntrinsicQuarticSectionCap

open ArkLib.ProximityGap.Frontier.IntrinsicQuarticSectionCap in
#print axioms secondPrime_proper_quartic_label_cap
