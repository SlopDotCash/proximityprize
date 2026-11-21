/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.CommonSectionChart
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSectionResultant
import ArkLib.Research.ProximityGap.Frontier.IntegralOrdinaryPolars

/-! # A single integral cubic chart for polynomial sections

The coordinate change is performed over the unaltered scalar polynomial ring.
Its four specialized ordinate coefficients are the ones in the simultaneous
section chart. It preserves both the coordinate weight and the scalar grading.
-/
set_option autoImplicit false
noncomputable section
open Polynomial Finset
namespace ArkLib.ProximityGap.Frontier.IntegralSectionChart
open _root_.ProximityGap.CommonSectionChart
variable {K : Type} [Field K]

/-- Change the coordinate from X to r+1/U, clearing the weight separately in
each ordinate slot. The scalar variable remains a free indeterminate. -/
def chart (r : K) (w d : ℕ) (F : K[X][X][X]) : K[X][X][X] :=
  F.sum (fun j a => monomial j (reflect (w-d*j) (a.taylor (C r))))

theorem coeff_chart (r : K) (w d : ℕ) (F : K[X][X][X]) (j : ℕ) :
    (chart r w d F).coeff j = reflect (w-d*j) ((F.coeff j).taylor (C r)) := by
  classical
  rw [chart, coeff_sum, sum_def]
  simp only [coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp [notMem_support_iff.mp h]

def fiber (F : K[X][X][X]) (z : K) := F.map (mapRingHom (evalRingHom z))

theorem fiber_chart_coeff (r z : K) (w d : ℕ) (F : K[X][X][X]) (j : ℕ) :
    ((fiber (chart r w d F) z).coeff j) = change r (w-d*j) ((fiber F z).coeff j) := by
  simp only [fiber,Polynomial.coeff_map,coeff_chart,coe_mapRingHom,← reflect_map,map_taylor,change]
  rw [show (evalRingHom z) (C r) = r from eval_C]

theorem chart_natDegree (r : K) (w d : ℕ) (F : K[X][X][X]) :
    (chart r w d F).natDegree = F.natDegree := by
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    simp [coeff_chart, coeff_eq_zero_of_natDegree_lt hj]
  · by_cases h : F = 0
    · simp [h]
    apply le_natDegree_of_ne_zero
    rw [coeff_chart]
    simpa using leadingCoeff_ne_zero.mpr h

private theorem scalar_height_slot (r : K) (a : ℕ) (p : K[X][X]) :
    Bivariate.degreeX (reflect a (p.taylor (C r))) ≤ Bivariate.degreeX p := by
  classical
  unfold Bivariate.degreeX
  apply Finset.sup_le
  intro j _
  rw [coeff_reflect,taylor_coeff,eval_eq_sum,sum_def]
  apply natDegree_sum_le_of_forall_le
  intro i _
  rw [hasseDeriv_coeff,← C_pow,← C_eq_natCast]
  have h := natDegree_mul_C_le (C ((i+revAt a j).choose (revAt a j) : K) * p.coeff (i+revAt a j)) (r^i)
  exact h.trans ((natDegree_C_mul_le _ _).trans (Bivariate.coeff_natDegree_le_degreeX p _))

/-- The total scalar-ordinate bound survives uniformly, including all cancellations. -/
theorem scalar_weight (r : K) (w d m : ℕ) (F : K[X][X][X])
    (hM : ∀ j, F.coeff j ≠ 0 → Bivariate.degreeX (F.coeff j)+j ≤ m) :
    ∀ j, (chart r w d F).coeff j ≠ 0 →
      Bivariate.degreeX ((chart r w d F).coeff j)+j ≤ m := by
  intro j hn
  rw [coeff_chart] at hn ⊢
  have h0 : F.coeff j ≠ 0 := fun hz => hn (by simp [hz])
  exact (Nat.add_le_add_right (scalar_height_slot r _ _) _).trans (hM _ h0)

/-- The pullback remains in the same coordinate-ordinate weighted space. -/
theorem coordinate_weight (r : K) (w d : ℕ) (F : K[X][X][X])
    (hW : ∀ j, F.coeff j ≠ 0 → (F.coeff j).natDegree+d*j ≤ w) :
    ∀ j, (chart r w d F).coeff j ≠ 0 →
      ((chart r w d F).coeff j).natDegree+d*j ≤ w := by
  intro j hn
  rw [coeff_chart] at hn ⊢
  have h0 : F.coeff j ≠ 0 := fun hz => hn (by simp [hz])
  have h := hW j h0
  have hb : ((F.coeff j).taylor (C r)).natDegree ≤ w-d*j := by simpa using (by omega : (F.coeff j).natDegree ≤ w-d*j)
  have := natDegree_reflect_le (N := w-d*j) (p := (F.coeff j).taylor (C r))
  omega

/-- Exchange coordinate and scalar in each coefficient of a geometric surface
originally written in the order coordinate, scalar, ordinate. -/
def orient (F : K[X][X][X]) : K[X][X][X] := F.map Bivariate.swap.toRingEquiv.toRingHom

theorem fiber_orient (F : K[X][X][X]) (z : K) :
    fiber (orient F) z = F.map (evalRingHom (C z)) := by
  ext1 j
  simp only [fiber,orient,Polynomial.coeff_map,coe_mapRingHom]
  change (Bivariate.swap (F.coeff j)).map (evalRingHom z) = (F.coeff j).eval (C z)
  generalize F.coeff j = P
  induction P using Polynomial.induction_on' with
  | add f g hf hg => simp [hf,hg]
  | monomial n a =>
    rw [Bivariate.swap_monomial,Polynomial.map_mul,Polynomial.map_C,eval_monomial,Polynomial.map_map]
    have hg : (evalRingHom z).comp C = RingHom.id K := by ext x; exact eval_C
    rw [hg,map_id]
    change a * C ((Polynomial.X ^ n : K[X]).eval z) = _
    simp

theorem orient_profile (F : K[X][X][X]) (j : ℕ) :
    ((orient F).coeff j).natDegree = Bivariate.degreeX (F.coeff j) ∧
      Bivariate.degreeX ((orient F).coeff j) = (F.coeff j).natDegree := by
  simp only [orient,Polynomial.coeff_map]
  exact ⟨Bivariate.natDegree_swap _,Bivariate.degreeX_swap _⟩

private theorem fiber_slot_degree (F : K[X][X][X]) (z : K) (j : ℕ) :
    ((fiber F z).coeff j).natDegree ≤ (F.coeff j).natDegree := by
  simp only [fiber,Polynomial.coeff_map,coe_mapRingHom]
  exact natDegree_map_le

/-- One integral chart realizes all simple sections in their full derivative
degree. The sites and optional tests can be prescribed before choosing it. -/
theorem common_chart [Infinite K] {L : Type*} [Field L] (φ : K →+* L)
    (tests : Finset L[X]) (htests : ∀ p ∈ tests, p ≠ 0)
    (F : K[X][X][X]) (S sites : Finset K) (q : K → K[X]) (w d : ℕ)
    (hw : 3*d ≤ w) (hd : F.natDegree ≤ 3)
    (hW : ∀ j, F.coeff j ≠ 0 → (F.coeff j).natDegree+d*j ≤ w)
    (hq : ∀ z ∈ S, (q z).natDegree ≤ d)
    (hroot : ∀ z ∈ S, (fiber F z).eval (q z) = 0)
    (hsimple : ∀ z ∈ S, (fiber F z).derivative.eval (q z) ≠ 0) :
    ∃ r ∉ sites, (∀ p ∈ tests, p.eval (φ r) ≠ 0) ∧ Function.Injective (fun x : K => (x-r)⁻¹) ∧
      ∀ z ∈ S, (fiber (chart r w d F) z).eval (change r d (q z)) = 0 ∧
        ((fiber (chart r w d F) z).derivative.eval (change r d (q z))).natDegree = w-d ∧
        (change r d (q z)).natDegree ≤ d ∧ ∀ x ∈ sites, ∀ v : K,
          (change r d (q z)).eval (x-r)⁻¹ = (x-r)⁻¹^d*v ↔ (q z).eval x = v := by
  let v := w-3*d
  have hv : v+d+d+d=w := by dsimp [v]; omega
  have hf (z : K) : (fiber F z).natDegree ≤ 3 := natDegree_map_le.trans hd
  have hc (j : ℕ) (z : K) : ((fiber F z).coeff j).natDegree ≤ w-d*j := by
    apply (fiber_slot_degree F z j).trans
    by_cases h : F.coeff j = 0
    · simp [h]
    · have := hW j h; omega
  have hb (z : K) : ((fiber F z).coeff 1).natDegree ≤ v+d+d := by have := hc 1 z; omega
  have hc' (z : K) : ((fiber F z).coeff 2).natDegree ≤ v+d := by have := hc 2 z; omega
  have he (z : K) : ((fiber F z).coeff 3).natDegree ≤ v := by have := hc 3 z; omega
  obtain ⟨r,hr,ht,hinj,h⟩ := simple_fibers S sites φ tests htests (fiber F) q v d
    (fun z _ => hf z) (fun z _ => hb z) (fun z _ => hc' z) (fun z _ => he z) hq hroot hsimple
  refine ⟨r,hr,ht,hinj,?_⟩
  intro z hz
  let Q := change r d (q z)
  have hdc : (fiber (chart r w d F) z).natDegree ≤ 3 := natDegree_map_le.trans ((chart_natDegree r w d F).le.trans hd)
  obtain ⟨hval,hder⟩ := section_values (fiber (chart r w d F) z) hdc Q
  simp only [fiber_chart_coeff] at hval hder
  obtain ⟨hs,hh⟩ := h z hz
  have h₀ : w-d*0=v+d+d+d := by omega
  have h₁ : w-d*1=v+d+d := by omega
  have h₂ : w-d*2=v+d := by omega
  have h₃ : w-d*3=v := by omega
  rw [h₀,h₁,h₂,h₃] at hval
  rw [h₁,h₂,h₃] at hder
  refine ⟨hval.trans hs,?_,degree_le r d (q z) (hq z hz),?_⟩
  · rw [show (change r d (q z)) = Q from rfl,hder,hh]
    omega
  · intro x hx value
    exact eval_site_eq_iff r x d (q z) (hq z hz) (fun e => hr (e ▸ hx)) value

/-- A raw irreducible cubic at terminal population supplies a common chart
and the ordinary-polar gcd lower bound on that same transformed equation.
All simple sections, scalar labels, and their received values are retained. -/
theorem production_chart [Infinite K] (p₃ : (3:K) ≠ 0)
    (f : K[X][X][X]) (hi : Irreducible f) (hd : f.natDegree = 3)
    (w : ℕ) (hw : 201326589 ≤ w) (hw' : w ≤ 290805098)
    (hW : ∀ j, f.coeff j ≠ 0 → Bivariate.degreeX (f.coeff j)+67108863*j ≤ w)
    (hM : WeightedSylvesterDegree.TotalDegreeLe f 34)
    (G sites : Finset K) (hG : 1342177249 ≤ G.card) (q : K → K[X])
    (hq : ∀ z ∈ G, (q z).natDegree ≤ 67108863)
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C z)) (q z) = 0)
    {L : Type*} [Field L] (φ : K →+* L) (tests : Finset L[X]) (htests : ∀ t ∈ tests, t ≠ 0) :
    ∃ (S : Finset K) (r : K), S ⊆ G ∧ G.card ≤ S.card+161 ∧ r ∉ sites ∧
      (∀ p ∈ tests, p.eval (φ r) ≠ 0) ∧ Function.Injective (fun x : K => (x-r)⁻¹) ∧
      let F := chart r w 67108863 (orient f)
      (∀ z ∈ S, (fiber F z).eval (change r 67108863 (q z)) = 0 ∧
        ((fiber F z).derivative.eval (change r 67108863 (q z))).natDegree = w-67108863 ∧
        (change r 67108863 (q z)).natDegree ≤ 67108863 ∧ ∀ x ∈ sites, ∀ v : K,
        (change r 67108863 (q z)).eval (x-r)⁻¹ = (x-r)⁻¹^67108863*v ↔ (q z).eval x = v) ∧
      ∀ c₁ c₂ : K, IntegralOrdinaryPolars.polarResultant F (C c₁) ≠ 0 →
        IntegralOrdinaryPolars.polarResultant F (C c₂) ≠ 0 →
        2*(w-67108863) ≤ OrdinaryPolarGcdBudget.genericDegree
          (IntegralOrdinaryPolars.polarResultant F (C c₁))
          (IntegralOrdinaryPolars.polarResultant F (C c₂)) + 201 := by
  classical
  let mult (z : K) := f.derivative.eval₂ (evalRingHom (C z)) (q z) = 0
  let S := G.filter (fun z => ¬ mult z)
  have hs : S ⊆ G := filter_subset _ _
  have cap := SecondPrimeSectionResultant.cubic_multiple_section_cap (RingHom.id K) f p₃ hi hd
    (by decide : 3 ≤ 34) hM G q hroot
  change (G.filter mult).card ≤ 5*34-9 at cap
  have hcount := card_filter_add_card_filter_not (s := G) mult
  change (G.filter mult).card + S.card = G.card at hcount
  have hn (j : ℕ) (h : (orient f).coeff j ≠ 0) : f.coeff j ≠ 0 := by
    intro hz; apply h; simp [orient,hz]
  have hw₀ (j : ℕ) (h : (orient f).coeff j ≠ 0) :
      ((orient f).coeff j).natDegree+67108863*j ≤ w := by
    rw [(orient_profile f j).1]; exact hW _ (hn _ h)
  have hm₀ (j : ℕ) (h : (orient f).coeff j ≠ 0) :
      Bivariate.degreeX ((orient f).coeff j)+j ≤ 34 := by
    rw [(orient_profile f j).2]; exact hM _ (hn _ h)
  have hdo : (orient f).natDegree ≤ 3 := natDegree_map_le.trans hd.le
  obtain ⟨r,hr,ht,hinj,h⟩ := common_chart φ tests htests (orient f) S sites q w 67108863
    (by omega) hdo hw₀ (fun z hz => hq z (hs hz)) (fun z hz => by
      rw [fiber_orient,eval_map]; exact hroot z (hs hz)) (fun z hz => by
      rw [fiber_orient,derivative_map,eval_map]; exact (mem_filter.mp hz).2)
  refine ⟨S,r,hs,by omega,hr,ht,hinj,h,?_⟩
  intro c₁ c₂ ha hb
  apply IntegralOrdinaryPolars.supported_gcd_lower _ c₁ c₂ w hw hw' ((chart_natDegree ..).le.trans hdo)
    (coordinate_weight r w 67108863 (orient f) hw₀) (scalar_weight r w 67108863 34 (orient f) hm₀)
    ha hb S (by omega) (fun z => change r 67108863 (q z))
    (fun z hz => (h z hz).1) (fun z hz => (h z hz).2.1)

#print axioms production_chart
#print axioms common_chart
#print axioms fiber_orient
#print axioms coeff_chart
#print axioms coordinate_weight
#print axioms scalar_weight
end ArkLib.ProximityGap.Frontier.IntegralSectionChart
