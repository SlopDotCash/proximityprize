/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PowerFiberEndpoint

/-! # Rational fibers and the bad-scalar event at unique decoding

A completely split fiber of a pencil of degree e+1 supplies one bad scalar per
site. The chosen denominator can be any polynomial in the pencil avoiding the
evaluation sites. The same two words serve every supplied fiber.
-/

set_option autoImplicit false
open Finset Polynomial
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.RationalFiberEndpoint
variable {K : Type} [Field K] [DecidableEq K]

private theorem constant_times_nodal (S : Finset K) (Z : K[X])
    (hz : ∀ x ∈ S, Z.eval x=0) (hd : Z.natDegree≤S.card) :
    ∃ a : K, Z=C a * Lagrange.nodal S id := by
  classical
  have div : Lagrange.nodal S id ∣ Z := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id hij
    · intro i hi
      exact Polynomial.dvd_iff_isRoot.mpr (hz i hi)
  obtain ⟨B,hB⟩ := div
  by_cases hb : B=0
  · exact ⟨0, by simp [hB,hb]⟩
  have hbn : B.natDegree=0 := by
    rw [hB,(Lagrange.nodal_monic ..).natDegree_mul' hb,Lagrange.natDegree_nodal] at hd
    omega
  exact ⟨B.coeff 0, by rw [hB,← eq_C_of_natDegree_eq_zero hbn,mul_comm]⟩

omit [DecidableEq K] in
/-- An inverse of B modulo the monic denominator P gives the shared numerator
of the received rows. -/
theorem exists_weight (V P B : K[X]) (hP : P.Monic) (hdeg : 0<P.natDegree)
    (hc : IsCoprime P B) : ∃ W : K[X], W.natDegree<P.natDegree ∧ P ∣ W*B-V := by
  obtain ⟨a,j,haj⟩ := hc
  let W := (V*j) %ₘ P
  refine ⟨W,natDegree_modByMonic_lt _ hP (by rintro rfl; simp at hdeg),?_⟩
  obtain ⟨c,hc'⟩ := dvd_modByMonic_sub (V*j) P
  change W-V*j=P*c at hc'
  exact ⟨c*B-V*a, by linear_combination B*hc' + V*haj⟩

/-- A rational pencil fiber gives a literal MCA event on the complement of
its other e roots, using a shared numerator W and denominator P. -/
theorem event_of_fiber (D A : Finset K) (k e : ℕ) (hk : 0<k) (he : 0<e)
    (hD : D.card=k+2*e) (hA : A.card=e+1) {t c : K} (ht : t∈A)
    (hsub : A.erase t ⊆ D) (hc : c≠0) (P B W : K[X])
    (hP : P.Monic) (hpdeg : P.natDegree=e+1) (hw : W.natDegree<P.natDegree)
    (hpb : IsCoprime P B) (hpv : IsCoprime P (Lagrange.nodal D id))
    (hWB : P ∣ W*B-Lagrange.nodal D id)
    (hf : Lagrange.nodal A id=P-C c*B) :
    _root_.ProximityGap.mcaEvent
      (ReedSolomon.code (Function.Embedding.subtype (·∈D)) k : Set (D → K))
      ((e:ℝ≥0)/D.card) (fun i => (i.val*W.eval i.val)/P.eval i.val)
      (fun i => -(W.eval i.val/P.eval i.val)) t := by
  classical
  let E := A.erase t
  let S := D \ E
  let Q := Lagrange.nodal S id
  let V := Lagrange.nodal D id
  have hEc : E.card=e := by simp only [E,card_erase_of_mem ht,hA,Nat.add_sub_cancel]
  have hSc : S.card=k+e := by
    dsimp only [S]
    rw [card_sdiff_of_subset hsub,hD,hEc];omega
  have hQdeg : Q.natDegree=k+e := (Lagrange.natDegree_nodal ..).trans hSc
  have hV : V=Q*Lagrange.nodal E id := (Finset.prod_sdiff hsub).symm
  have hid : V*(X-C t)=Q*(P-C c*B) := by
    have ha : Lagrange.nodal E id * (X-C t) = Lagrange.nodal A id := by
      exact prod_erase_mul _ _ ht
    rw [hV,mul_assoc,ha,hf]
  obtain ⟨b,hb⟩ := hWB
  change W*B-V=P*b at hb
  have div : P ∣ (X-C t)*W+C c*Q := by
    apply hpb.dvd_of_dvd_mul_right
    exact ⟨(X-C t)*b+Q,by linear_combination (X-C t)*hb + hid⟩
  obtain ⟨H,hH⟩ := div
  have hdegH : H.natDegree<k := by
    by_cases hz : H=0
    · simpa [hz] using hk
    have hZ := natDegree_add_le ((X-C t)*W) (C c*Q)
    rw [hH,hP.natDegree_mul' hz,hpdeg] at hZ
    have h1 := natDegree_mul_le (p:=X-C t) (q:=W)
    have h2 := natDegree_mul_le (p:=C c) (q:=Q)
    rw [natDegree_X_sub_C] at h1
    rw [natDegree_C,hQdeg] at h2
    omega
  have hpdom (x : K) (hx : x∈D) : P.eval x≠0 := by
    obtain ⟨a,b',hc'⟩ := hpv
    have heq := congrArg (fun R : K[X] => R.eval x) hc'
    intro hzero
    have hroot : (Lagrange.nodal D id).eval x = 0 := Lagrange.eval_nodal_at_node (v:=id) hx
    simp [hzero,hroot] at heq
  have hqroot (x : K) (hx : x∈S) : Q.eval x=0 := Lagrange.eval_nodal_at_node (v:=id) hx
  let S' := S.subtype (·∈D)
  have hs' : S'.card=k+e := by
    dsimp only [S']
    rw [card_subtype,filter_eq_self.mpr (fun _ hx => (mem_sdiff.mp hx).1),hSc]
  refine ⟨S', ?_, ⟨fun i => H.eval i.val,
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval H hdegH (fun _ => rfl), ?_⟩, ?_⟩
  · rw [Fintype.card_coe,tsub_mul,one_mul,div_mul_cancel₀ _ (by rw [hD];positivity),hs',hD]
    simp only [show k+2*e=k+e+e by omega,Nat.cast_add,add_tsub_cancel_right,le_refl]
  · intro i hi
    have h := congrArg (fun R : K[X] => R.eval i.val) hH
    have hx : i.val∈S := by simpa only [S',mem_subtype] using hi
    simp [hqroot i.val hx] at h
    simp only [smul_eq_mul]
    field_simp [hpdom i.val i.property]
    linear_combination -h
  · rintro ⟨_,_,row,hrow,joint⟩
    let _ : NeZero k := ⟨hk.ne'⟩
    obtain ⟨R,hR,hpoly⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hrow
    obtain ⟨a,ha⟩ : ∃ a : K, R*P+W=C a*Q := by
      apply constant_times_nodal S
      · intro x hx
        let i : D := ⟨x,(mem_sdiff.mp hx).1⟩
        have hj := (hpoly i).trans (joint i (by simpa only [S',mem_subtype] using hx)).2
        change R.eval x = -(W.eval x/P.eval x) at hj
        simp only [eval_add,eval_mul,hj]
        field_simp [hpdom x i.property]
        ring
      · apply (natDegree_add_le ..).trans
        rw [hSc]
        have h := natDegree_mul_le (p:=R) (q:=P)
        omega
    have hpq : IsCoprime P Q := hpv.of_isCoprime_of_dvd_right ⟨_,hV⟩
    have div' : P ∣ (C c + C a*(X-C t))*Q :=
      ⟨H+(X-C t)*R,by linear_combination hH - (X-C t)*ha⟩
    have div'' := hpq.dvd_of_dvd_mul_right div'
    have hlinear : (C c+C a*(X-C t)).natDegree≤1 := by
      apply (natDegree_add_le ..).trans
      have h := natDegree_mul_le (p:=C a) (q:=X-C t)
      simp only [natDegree_C, natDegree_X_sub_C, zero_add] at h ⊢
      omega
    have hnz : C c+C a*(X-C t)≠0 := by
      intro hh
      have ht' := congrArg (fun R : K[X] => R.eval t) hh
      exact hc (by simpa using ht')
    have := hP.natDegree_le_of_dvd hnz div''
    omega

#print axioms exists_weight
#print axioms event_of_fiber
end ArkLib.ProximityGap.Frontier.RationalFiberEndpoint
