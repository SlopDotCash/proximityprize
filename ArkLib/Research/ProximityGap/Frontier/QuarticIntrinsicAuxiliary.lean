/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.IntrinsicReceivedSections
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticInterpolation

/-! # An explicit auxiliary of smaller value degree on the production quartic -/

set_option autoImplicit false
noncomputable section

open Polynomial Finset Module
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.QuarticIntrinsicAuxiliary

open JetMultiplierGraph IntrinsicReceivedSections
open SecondPrimeQuarticInterpolation (Monomials)

variable {K : Type} [Field K] {s b d t : ℕ}

private def term (m : Monomials s b d t) (x : K) : K[X][X][X] :=
  monomial m.1.val (monomial m.2.2.val (monomial m.2.1.val x))

/-- Monomial section space, with the scalar variable innermost so polynomial
multipliers and evaluation at a scalar are literal coefficientwise operations. -/
def sectionMap : (Monomials s b d t → K) →ₗ[K] K[X][X][X] where
  toFun c := ∑ m, term m (c m)
  map_add' c e := by simp only [Pi.add_apply,term,map_add,Finset.sum_add_distrib]
  map_smul' z c := by simp only [Pi.smul_apply,term,Finset.smul_sum,smul_monomial,smul_eq_mul,
    RingHom.id_apply]

private theorem section_coeff (c : Monomials s b d t → K) (m : Monomials s b d t) :
    ((((sectionMap c).coeff m.1.val).coeff m.2.2.val).coeff m.2.1.val) = c m := by
  change (((∑ m', term m' (c m')).coeff _).coeff _).coeff _ = _
  simp only [finsetSum_coeff]
  classical
  rw [Finset.sum_eq_single m]
  · simp only [term,coeff_monomial,ite_true]
  · intro h _ hne
    by_cases hy : h.1.val = m.1.val
    · by_cases hx : h.2.2.val = m.2.2.val
      · have hz : h.2.1.val ≠ m.2.1.val := by
          intro he
          rcases h with ⟨h₀,hi,ha⟩
          rcases m with ⟨m₀,mi,ma⟩
          have h₁ : h₀=m₀ := Fin.ext hy
          subst m₀
          have h₂ : hi=mi := Fin.ext he
          have h₃ : ha=ma := Fin.ext hx
          exact hne (by subst mi; subst ma; rfl)
        simp [term,coeff_monomial,hy,hx,hz]
      · simp [term,coeff_monomial,hy,hx]
    · simp [term,coeff_monomial,hy]
  · simp

theorem section_ne_zero (c : Monomials s b d t → K) (hc : c ≠ 0) : sectionMap c ≠ 0 := by
  intro hz
  apply hc
  funext m
  rw [← section_coeff c m,hz]
  simp

theorem section_value_degree (c : Monomials s b d t → K) : (sectionMap c).natDegree ≤ b := by
  apply natDegree_sum_le_of_forall_le
  intro m _
  exact (natDegree_monomial_le _).trans (by have := m.1.isLt; omega)

theorem section_scalar_bound (c : Monomials s b d t → K) (hb : b ≤ s) :
    ScalarValueBound (sectionMap c) s := by
  intro j l hne
  have hj : j ≤ b := by
    by_contra! hh
    exact hne (by rw [coeff_eq_zero_of_natDegree_lt ((section_value_degree c).trans_lt hh),
      coeff_zero])
  have hd : (((sectionMap c).coeff j).coeff l).natDegree ≤ s-j := by
    change (((∑ m, term m (c m)).coeff j).coeff l).natDegree ≤ s-j
    simp only [finsetSum_coeff]
    apply natDegree_sum_le_of_forall_le
    intro m _
    by_cases hy : m.1.val = j
    · by_cases hx : m.2.2.val = l
      · simp only [term,coeff_monomial,hy,hx,ite_true]
        exact (natDegree_monomial_le _).trans (by have := m.2.1.isLt; omega)
      · simp [term,coeff_monomial,hy,hx]
    · simp [term,coeff_monomial,hy]
  omega

private theorem eval_section (c : Monomials s b d t → K) (z : K) (q : K[X]) :
    (mapPlane (evalRingHom z) (sectionMap c)).eval q =
      ∑ m, monomial m.2.2.val ((c m)*z^m.2.1.val)*q^m.1.val := by
  change (((∑ m, term m (c m)).map (mapRingHom (evalRingHom z))).eval q) = _
  simp only [Polynomial.map_sum,eval_finsetSum,term,map_monomial,coe_mapRingHom,
    eval_monomial,coe_evalRingHom]

theorem section_graph_degree (c : Monomials s b d t → K) (z : K) (q : K[X])
    (hq : q.natDegree ≤ d) (ht : 0 < t) :
    ((mapPlane (evalRingHom z) (sectionMap c)).eval q).natDegree < t := by
  rw [eval_section]
  apply Nat.lt_of_le_pred ht
  rw [Nat.pred_eq_sub_one]
  apply natDegree_sum_le_of_forall_le
  intro m _
  have hj := (natDegree_pow_le (p := q) (n := m.1.val)).trans (Nat.mul_le_mul_left _ hq)
  have ha := m.2.2.isLt
  exact natDegree_mul_le.trans ((Nat.add_le_add (natDegree_monomial_le _) hj).trans (by omega))

/-- The concrete value-cubic window, including every coordinate and scalar monomial. -/
abbrev ProductionWindow := Monomials 67108864 3 67108863 (64*357913943)

theorem card_production : Fintype.card ProductionWindow = 6121893077231948920 := by
  simp only [ProductionWindow,Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  exact (by decide : (∑ j : Fin 4, (67108864+1-j.val)*(64*357913943-j.val*67108863)) = 6121893077231948920)

/-- A nonzero cubic-in-value auxiliary contains *every* selected polynomial
on a proper quartic with the production interpolation and weight budgets.
This uses the entire n-site domain and all 357913943 agreements. -/
theorem secondPrime_quartic_auxiliary (F : K[X][X][X]) (D : Finset K)
    (hn : D.card = 1073741824) (u v : K → K) (hscalar : ScalarValueBound F 34)
    (hprim : (mapPlane (algebraMap K[X] (RatFunc K)) F).IsPrimitive)
    (hfour : (mapPlane (algebraMap K[X] (RatFunc K)) F).natDegree = 4)
    (hir : Irreducible (MovingCubicVanishingBranch.genericEquation
      (mapPlane (algebraMap K[X] (RatFunc K)) F)))
    (hnd : ¬MovingCubicVanishingBranch.genericEquation (mapPlane (algebraMap K[X] (RatFunc K)) F)
      ∣ MovingCubicVanishingBranch.genericEquation (CanonicalQuarticSiteOrder.scalarFieldHessian
        (mapPlane (algebraMap K[X] (RatFunc K)) F)))
    (hw : Polynomial.Bivariate.natWeightedDegree (mapPlane (algebraMap K[X] (RatFunc K)) F)
      1 67108863 ≤ 302954072) :
    ∃ P : K[X][X][X], P ≠ 0 ∧ P.natDegree ≤ 3 ∧ ScalarValueBound P 67108864 ∧
      ∀ (z : K) (q : K[X]) (H : Finset K), H ⊆ D → 357913943 ≤ H.card →
        q.natDegree ≤ 67108863 → (mapPlane (evalRingHom z) F).eval q = 0 →
        (∀ a ∈ H, q.eval a = u a+z*v a) → (mapPlane (evalRingHom z) P).eval q = 0 := by
  classical
  let G := mapPlane (algebraMap K[X] (RatFunc K)) F
  let r (a : K) := receivedOrder F a (u a) (v a)
  have small (a : K) : r a ≤ 4 :=
    (CanonicalQuarticSiteOrder.siteOrder_le G _ _).trans hfour.le
  have fieldLine (a : K) : algebraMap K[X] (RatFunc K) (received (u a) (v a)) =
      RatFunc.C (u a)+RatFunc.X*RatFunc.C (v a) := by
    rw [received,map_add,map_mul]
    rfl
  have Hsum : ∑ a ∈ D, r a ≤ 1412316443 := by
    simpa only [r,receivedOrder,fieldLine] using
      CanonicalQuarticSiteOrder.secondPrime_quartic_received_budget G hfour hir hnd hw D hn u v
  let E := ProductionWindow → K
  let surf : E →ₗ[K] K[X][X][X] := sectionMap
  have hbound := quartic_count (fun x : D => r x.val) (by simpa using hn)
    (fun x => small x.val) (by simpa only [D.sum_coe_sort (f := r)] using Hsum)
  have hcard : finrank K E = 6121893077231948920 := by
    rw [show finrank K E = Fintype.card ProductionWindow from Module.finrank_pi K,card_production]
  let cost (x : K) := ((64-r x)*(64-r x+1)/2)*67108831
  have hcost : (∑ x : D, cost x.val) = ∑ x ∈ D, cost x := D.sum_coe_sort (f := cost)
  change Fintype.card {x // x ∈ D} * (2080*67108865) <
    6121893077231948920 + ∑ x : D, cost x.val at hbound
  rw [hcost,Fintype.card_coe] at hbound
  obtain ⟨e,he,hall⟩ := exists_section_outside (μ := 64) D u v F hprim hscalar
    (fun x _ => (small x).trans (by decide)) (by decide : 34 ≤ 67108864+1) surf
    (fun c => section_scalar_bound c (by decide)) ⊥ (by
      rw [finrank_bot,add_zero,hcard]
      exact hbound)
  refine ⟨surf e,section_ne_zero e he,section_value_degree e,section_scalar_bound e (by decide),?_⟩
  intro z q H hH ht hd hF ha
  exact hall z q H hH hF ha ((section_graph_degree e z q hd (by decide)).trans_le (by omega))

end ArkLib.ProximityGap.Frontier.QuarticIntrinsicAuxiliary

open ArkLib.ProximityGap.Frontier.QuarticIntrinsicAuxiliary in
#print axioms secondPrime_quartic_auxiliary
