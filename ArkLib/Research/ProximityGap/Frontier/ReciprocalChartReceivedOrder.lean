/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.CommonSectionChart
import ArkLib.Research.ProximityGap.Frontier.ReceivedJetContact
import ArkLib.Research.ProximityGap.Frontier.JetMultiplierGraph

/-! # Received joint multiplicity in a reciprocal coordinate chart

A line in the new coordinates pulls back to a polynomial graph of degree at most
the section degree. The old site order bounds the intersection along that graph.
The homogeneous leading jet is detected by a line over an infinite field.
-/
set_option autoImplicit false
noncomputable section

open Polynomial Finset
namespace ArkLib.ProximityGap.Frontier.ReciprocalChartReceivedOrder
open _root_.ProximityGap.CommonSectionChart CanonicalQuarticSiteOrder TruncatedJetMultipliers
variable {K : Type} [Field K]

private theorem chart_pow (a α : K) (r : ℕ) :
    change a r ((Polynomial.X-C α)^r) = (change a 1 (Polynomial.X-C α))^r := by
  induction r with
  | zero => simp [change,reflect_C]
  | succ r ih =>
    rw [pow_succ, change_mul a _ _ (by simp) (by simp), ih, pow_succ]

/-- The weight-cleared reciprocal change preserves all finite-site vanishing powers. -/
theorem chart_power_dvd (a α : K) (ha : α ≠ a) (w r : ℕ) (P : K[X])
    (hw : P.natDegree ≤ w) (h : (Polynomial.X-C α)^r ∣ P) :
    (Polynomial.X-C ((α-a)⁻¹))^r ∣ change a w P := by
  by_cases hp : P=0
  · simp [hp,change]
  obtain ⟨Q,hQ⟩ := h
  have hq : Q≠0 := by rintro rfl; simp [hQ] at hp
  have hh : r+Q.natDegree ≤ w := by
    rw [hQ,natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero α)) hq,natDegree_pow,natDegree_X_sub_C] at hw
    simpa using hw
  have hlin : Polynomial.X-C ((α-a)⁻¹) ∣ change a 1 (Polynomial.X-C α) := by
    apply dvd_iff_isRoot.mpr
    change (change a 1 (Polynomial.X-C α)).eval _ = 0
    rw [eval_site a α _ _ (by simp) ha]
    simp
  rw [hQ,show w=r+(w-r) by omega,change_mul a _ _ (by simp) (by omega),chart_pow]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hlin r) _

private theorem graph_power (F : K[X][X]) (α l : K) (r : ℕ)
    (hr : ScalarHessianLocalOrder.HasOrder (Polynomial.X-C α) r (F.taylor (C l))) (q : K[X]) (hq : q.eval α=l) :
    (Polynomial.X-C α)^r ∣ F.eval q := by
  have hw : Polynomial.X-C α ∣ q-C l := dvd_iff_isRoot.mpr (by change (q-C l).eval α=0; simp [hq])
  rw [← taylor_eval_sub (C l) F q,eval_eq_sum,sum_def]
  apply Finset.dvd_sum
  intro j _
  have h := mul_dvd_mul (hr j) (pow_dvd_pow_of_dvd hw j)
  rw [← pow_add] at h
  exact (pow_dvd_pow _ (by omega)).trans h

private def diagonal (H : K[X][X]) (n : ℕ) : K[X] :=
  ∑ i ∈ H.support, monomial i (if i≤n then (H.coeff i).coeff (n-i) else 0)

private theorem diagonal_eval (H : K[X][X]) (n : ℕ) (s : K) :
    (diagonal H n).eval s = (H.eval (C s*Polynomial.X)).coeff n := by
  rw [diagonal,eval_finsetSum,eval_eq_sum,sum_def,finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_monomial,mul_pow,← C_pow,← mul_assoc,coeff_mul_X_pow']
  split_ifs with hi
  · rw [coeff_mul_C]
  · simp

private theorem diagonal_coeff (H : K[X][X]) {n i : ℕ} (hi : i≤n) :
    (diagonal H n).coeff i = (H.coeff i).coeff (n-i) := by
  classical
  simp only [diagonal,finsetSum_coeff,coeff_monomial,Finset.sum_ite_eq']
  by_cases hs : i ∈ H.support
  · simp [hs,hi]
  · simp [hs,notMem_support_iff.mp hs]

private theorem vanishing_of_directions [Infinite K] (H : K[X][X]) (r : ℕ)
    (h : ∀ s : K, Polynomial.X^r ∣ H.eval (C s*Polynomial.X)) :
    ∀ i j, i+j<r → (H.coeff i).coeff j=0 := by
  intro i j hij
  have hz : diagonal H (i+j)=0 := by
    apply Polynomial.funext
    intro s
    rw [diagonal_eval,eval_zero]
    exact X_pow_dvd_iff.mp (h s) _ hij
  have hc := congrArg (fun P : K[X] => P.coeff i) hz
  simpa only [diagonal_coeff H (Nat.le_add_right i j),Nat.add_sub_cancel_left,coeff_zero] using hc

private theorem graph_shift (G : K[X][X]) (b l s : K) :
    ((G.eval (C l+C s*(Polynomial.X-C b))).taylor b) =
      (ReceivedJetContact.shifted G b l).eval (C s*Polynomial.X) := by
  rw [ReceivedJetContact.shifted,taylor_eval]
  have h := eval_map_apply (p := G) (taylorAlgHom b).toRingHom (C l+C s*(Polynomial.X-C b))
  change (taylorAlgHom b).toRingHom (G.eval (C l+C s*(Polynomial.X-C b))) = (G.map (taylorAlgHom b).toRingHom).eval _
  rw [← h]
  congr 1
  simp [taylorAlgHom_apply,taylor_mul,add_comm]

private theorem graph_bounds (F : K[X][X]) (w d : ℕ) (hW : ∀ j, F.coeff j ≠ 0 →
    (F.coeff j).natDegree+d*j ≤ w) (q : K[X]) (hq : q.natDegree≤d) : (F.eval q).natDegree≤w := by
  rw [eval_eq_sum,sum_def]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact natDegree_mul_le.trans ((Nat.add_le_add_left
    (natDegree_pow_le.trans (Nat.mul_le_mul_left j hq)) _).trans (by simpa [Nat.mul_comm] using hW j (mem_support_iff.mp hj)))

private theorem chart_graph (a : K) (w d : ℕ) (hw : 3*d≤w) (F G : K[X][X])
    (hf : F.natDegree ≤ 3) (hg : G.natDegree ≤ 3)
    (hW : ∀ j, F.coeff j ≠ 0 → (F.coeff j).natDegree+d*j ≤ w)
    (hG : ∀ j, G.coeff j = change a (w-d*j) (F.coeff j))
    (q : K[X]) (hq : q.natDegree≤d) :
    G.eval (change a d q) = change a w (F.eval q) := by
  let v := w-3*d
  have hslot (j : ℕ) : (F.coeff j).natDegree ≤ w-d*j := by
    by_cases hj : F.coeff j=0
    · simp [hj]
    · have hh := hW j hj; omega
  have h0 : w-d*0=v+d+d+d := by dsimp [v]; omega
  have h1 : w-d*1=v+d+d := by dsimp [v]; omega
  have h2 : w-d*2=v+d := by dsimp [v]; omega
  have h3 : w-d*3=v := by dsimp [v]; omega
  have he := cubic_chart a (v:=v) (d:=d) (F.coeff 0) (F.coeff 1) (F.coeff 2) (F.coeff 3) q
    (h1 ▸ hslot 1) (h2 ▸ hslot 2) (h3 ▸ hslot 3) hq
  rw [(section_values G hg _).1,(section_values F hf _).1]
  simp only [hG,h0,h1,h2,h3]
  have hw' : w=v+d+d+d := by simpa using h0
  rw [hw']
  exact he.symm

private theorem shifted_eq_translate (F : K[X][X]) (a l : K) :
    ReceivedJetContact.shifted F a l = translate F a (C l) := by
  unfold ReceivedJetContact.shifted translate
  rw [map_taylor]
  simp [taylorAlgHom_apply]

/-- The reciprocal chart does not decrease any known joint order at a finite
site distinct from the chosen pole. The new canonical order has an actual
leading term in the very translated equation used by the cubic polar estimate. -/
theorem chart_site_leader [Infinite K] (a α l : K) (ha : α≠a) (w d : ℕ)
    (hw : 3*d≤w) (hd : 1≤d) (F G : K[X][X]) (hf : F.natDegree≤3) (hg : G.natDegree≤3)
    (hW : ∀ j, F.coeff j ≠ 0 → (F.coeff j).natDegree+d*j ≤ w)
    (hG : ∀ j, G.coeff j = change a (w-d*j) (F.coeff j)) (hprim : G.IsPrimitive)
    (r : ℕ) (hr : ScalarHessianLocalOrder.HasOrder (Polynomial.X-C α) r (F.taylor (C l))) :
    let b := (α-a)⁻¹
    let new := siteOrder G b (C (b^d*l))
    r ≤ new ∧ ∃ j, Leader (ReceivedJetContact.shifted G b (b^d*l)) new j := by
  let b := (α-a)⁻¹
  let m := b^d*l
  change r ≤ siteOrder G b (C m) ∧ ∃ j, Leader (ReceivedJetContact.shifted G b m) _ j
  refine ⟨?_,by rw [shifted_eq_translate]; exact exists_leader_at_site G hprim b (C m)⟩
  apply (le_siteOrder_iff_jet G hprim b (C m) r).mpr
  have hvan : ∀ s : K, Polynomial.X^r ∣ (ReceivedJetContact.shifted G b m).eval (C s*Polynomial.X) := by
    intro s
    let Q : K[X] := C m+C s*(Polynomial.X-C b)
    have hQ : Q.natDegree ≤ d := by
      apply natDegree_add_le_of_degree_le (by simp)
      exact (natDegree_C_mul_le s _).trans (by simpa using hd)
    let q := (reflect d Q).taylor (-a)
    have hq : q.natDegree ≤ d := by
      change ((reflect d Q).taylor (-a)).natDegree ≤ _
      rw [natDegree_taylor]
      exact natDegree_reflect_le.trans (max_le le_rfl hQ)
    have hQq : change a d q = Q := by simp [q,change,taylor_taylor]
    have hqval : q.eval α = l := by
      apply (eval_site_eq_iff a α d q hq ha l).mp
      rw [hQq]
      change Q.eval b=m
      simp [Q]
    have hdiv := chart_power_dvd a α ha w r (F.eval q) (graph_bounds F w d hW q hq)
      (graph_power F α l r hr q hqval)
    rw [← chart_graph a w d hw F G hf hg hW hG q hq,hQq] at hdiv
    have hmap := map_dvd (taylorAlgHom b) hdiv
    rw [← graph_shift]
    simpa [b,Q,taylorAlgHom_apply] using hmap
  have hjet := vanishing_of_directions _ _ hvan
  rw [shifted_eq_translate] at hjet
  simpa only [translate_coeff] using hjet

/-- Any extension of the scalar coefficient field preserves a known order.
This carries the original received-row order into the geometric splitting field. -/
theorem map_hasOrder {L : Type} [Field L] (φ : K →+* L) (F : K[X][X]) (α l : K) :
    ScalarHessianLocalOrder.HasOrder (Polynomial.X-C (φ α)) (siteOrder F α (C l))
      ((JetMultiplierGraph.mapPlane φ F).taylor (C (φ l))) := by
  intro i
  have h := map_dvd (mapRingHom φ) (order_at_site F α (C l) i)
  have he := congrArg (fun P : L[X][X] => P.coeff i) (map_taylor F (C l) (mapRingHom φ))
  simp only [coeff_map,coe_mapRingHom,map_C] at he
  unfold JetMultiplierGraph.mapPlane
  rw [← he]
  simpa only [coe_mapRingHom,Polynomial.map_pow,Polynomial.map_sub,map_X,map_C] using h

#print axioms chart_site_leader
#print axioms map_hasOrder
end ArkLib.ProximityGap.Frontier.ReciprocalChartReceivedOrder
