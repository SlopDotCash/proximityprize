/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ProjectiveListTransfer
import ArkLib.Research.ProximityGap.Frontier.FiniteFingerprintCount
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget

/-! # Scalar list-to-MCA transfer on the same Reed–Solomon code

All q+1 projective evaluations admit literal witnesses. Pairwise collisions
cost at most k−1 coordinates in total, including the coordinate at infinity.
-/

set_option autoImplicit false
open Polynomial Finset Code
open scoped NNReal ENNReal
namespace ProximityGap.SameDomainListMca
open ProjectiveListTransfer
variable {F I : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype I] [DecidableEq I]

/-- Homogenized polynomials of degree at most d collide at most d times
on the whole projective line. -/
theorem collisions {d : ℕ} (f g : F[X]) (hne : f≠g) (hf : f.natDegree≤d) (hg : g.natDegree≤d) :
    (univ.filter fun z : Option F => value d z f=value d z g).card≤d := by
  classical
  let R := f-g
  have hR : R≠0 := sub_ne_zero.mpr hne
  have hd : R.natDegree≤d := (natDegree_sub_le ..).trans (max_le hf hg)
  let T := (univ : Finset F).filter fun z => f.eval z=g.eval z
  have hT : T ⊆ R.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset,mem_roots hR]
    exact (show (f-g).eval z=0 by rw [eval_sub,(mem_filter.mp hz).2,sub_self])
  have htc := (card_le_card hT).trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' R))
  have hcount : (univ.filter fun z : Option F => value d z f=value d z g).card =
      (if f.coeff d=g.coeff d then 1 else 0)+T.card := by
    rw [card_filter,Fintype.sum_option]
    simp only [T,card_filter,value,Option.elim_none,Option.elim_some]
    apply congrArg₂ (·+·)
    · by_cases h : f.coeff d=g.coeff d <;> simp [h]
    · apply sum_congr rfl
      intro z _
      by_cases h : f.eval z=g.eval z <;> simp [h]
  rw [hcount]
  split_ifs with h
  · have hlt : R.natDegree<d := by
      by_contra! hno
      have eq : R.natDegree=d := by omega
      have hz : R.coeff d=0 := by rw [show R=f-g from rfl,coeff_sub,h,sub_self]
      rw [← eq,coeff_natDegree,leadingCoeff_eq_zero] at hz
      exact hR hz
    omega
  · omega

open Classical in
/-- One received pair on the *same* code witnesses the full projective
second-moment lower bound for any supplied scalar list and its center. -/
theorem from_polynomials (D : I ↪ F) {k : ℕ} (hk : 0<k) (δ : ℝ≥0) (y : I → F)
    (P : Finset F[X]) (hdeg : ∀ f∈P, f.natDegree<k)
    (hagr : ∀ f∈P, ∃ S : Finset I, (1-δ)*Fintype.card I ≤ (S.card:ℝ≥0) ∧
      k<S.card ∧ ∀ i∈S, y i=f.eval (D i)) :
    ∃ u v : I → F, P.card*(Fintype.card F+1) ≤
      (univ.filter (mcaEvent (F:=F) (ReedSolomon.code D k : Set (I → F)) δ u v)).card *
        (Fintype.card F+1+(P.card-1)*(k-1)) := by
  classical
  obtain ⟨z,hz⟩ := FiniteFingerprintCount.exists_large_image P (value (k-1)) (k-1)
    (fun f hf g hg hne => collisions f g hne (by have := hdeg f hf;omega)
      (by have := hdeg g hg;omega))
  rw [Fintype.card_option] at hz
  obtain ⟨u,v,hv⟩ := projective_event D hk z y δ
  refine ⟨u,v,hz.trans (Nat.mul_le_mul_right _ ?_)⟩
  let labels := (P.image (value (k-1) z)).map (Equiv.neg F).toEmbedding
  have hsub : labels ⊆ univ.filter (mcaEvent (F:=F) (ReedSolomon.code D k : Set (I → F)) δ u v) := by
    intro γ hγ
    obtain ⟨w,hw,rfl⟩ := mem_map.mp hγ
    obtain ⟨f,hf,rfl⟩ := mem_image.mp hw
    obtain ⟨S,hs,ht,ha⟩ := hagr f hf
    exact mem_filter.mpr ⟨mem_univ _,hv f (hdeg f hf) S hs ht ha⟩
  simpa only [labels,card_map] using card_le_card hsub

open Classical in
/-- A scalar closed list of L+1 distinct codewords gives many genuinely
bad folding parameters while preserving the domain, dimension and radius. -/
theorem from_list (D : I ↪ F) (δ : ℝ≥0) {k t L : ℕ} (hk : 0<k) (hkt : k<t)
    (htn : t≤Fintype.card I) (hδ : (1-δ)*(Fintype.card I : ℝ≥0)≤t)
    (hlist : (L : ℕ∞)<Lambda (ReedSolomon.code D k : Set (I → F))
      (((Fintype.card I - t : ℕ) : ℝ)/(Fintype.card I:ℝ))) :
    ∃ u v : I → F, (L+1)*(Fintype.card F+1) ≤
      (univ.filter (mcaEvent (F:=F) (ReedSolomon.code D k : Set (I → F)) δ u v)).card *
        (Fintype.card F+1+L*(k-1)) := by
  classical
  let _ : NeZero k := ⟨hk.ne'⟩
  let C := (ReedSolomon.code D k : Set (I → F))
  let r := (((Fintype.card I-t:ℕ):ℝ)/(Fintype.card I:ℝ))
  obtain ⟨y,W,hW,hlarge⟩ : ∃ (y : I → F) (W : Finset (I → F)),
      (∀ c∈W, c∈closeCodewordsRel C y r) ∧ L<W.card := by
    by_contra! h
    exact (not_le_of_gt hlist) (Lambda_le_of_forall_finset_card_le fun y W hW => h y W hW)
  obtain ⟨V,hVW,hV⟩ := exists_subset_card_eq (show L+1≤W.card by omega)
  have hclose (w : V) := hW w (hVW w.property)
  have hex (w : V) := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (mem_closeCodewordsRel_iff.mp (hclose w)).1
  choose rep hd he using hex
  let P := univ.image rep
  have hin : Function.Injective rep := by
    intro a b hab
    exact Subtype.ext (funext fun i => ((he a i).symm.trans (congrArg (eval (D i)) hab)).trans (he b i))
  have hP : P.card=L+1 := by simp [P,card_image_of_injective _ hin,hV]
  have hh := from_polynomials D hk δ y P (by
    intro f hf
    obtain ⟨w,_,rfl⟩ := mem_image.mp hf
    exact hd w) (by
    intro f hf
    obtain ⟨w,_,rfl⟩ := mem_image.mp hf
    let S := univ.filter (fun i => (w : I → F) i=y i)
    have hw := (mem_closeCodewordsRel_iff.mp (hclose w)).2
    have hn := lt_of_lt_of_le (Nat.zero_lt_of_lt hkt) htn
    have hr : r=1-(t:ℝ)/Fintype.card I := by
      dsimp [r]
      rw [Nat.cast_sub htn,sub_div,div_self (by exact_mod_cast hn.ne')]
    rw [hr] at hw
    have htS : t≤S.card := by exact_mod_cast (relHammingDist_le_one_sub_div_iff hn).mp hw
    exact ⟨S,hδ.trans (by exact_mod_cast htS),hkt.trans_le htS,
      fun i hi => (mem_filter.mp hi).2.symm.trans (he w i).symm⟩)
  simpa only [hP,Nat.add_sub_cancel] using hh

open Classical in
/-- In the stated field range an over-budget list forces an over-budget MCA
event on the identical Reed–Solomon code and at the same Hamming step. -/
theorem budget (D : I ↪ F) (δ : ℝ≥0) {k t B : ℕ} (hk : 0<k) (hkt : k<t)
    (htn : t≤Fintype.card I) (hδ : (1-δ)*(Fintype.card I : ℝ≥0)≤t)
    (hroom : B^2*(k-1)<Fintype.card F+1)
    (hlist : (B:ℕ∞)<Lambda (ReedSolomon.code D k : Set (I → F))
      (((Fintype.card I-t:ℕ):ℝ)/(Fintype.card I:ℝ))) :
    ∃ u v : I → F, B < (univ.filter
      (mcaEvent (F:=F) (ReedSolomon.code D k : Set (I → F)) δ u v)).card := by
  obtain ⟨u,v,h⟩ := from_list D δ hk hkt htn hδ hlist
  refine ⟨u,v,?_⟩
  by_contra! small
  have := h.trans (Nat.mul_le_mul_right _ small)
  nlinarith only [this,hroom]

/-- An MCA guarantee at tolerance 1/Q bounds the closed scalar list by
the exact integer budget floor(q/Q) on the same Hamming step. -/
theorem closed_list_of_mca [Nonempty I] (D : I ↪ F) (δ : ℝ≥0) {k t Q : ℕ} (hk : 0<k)
    (hkt : k<t) (htn : t≤Fintype.card I) (hδ : (1-δ)*(Fintype.card I : ℝ≥0)≤t) (hQ : 0<Q)
    (hroom : (Fintype.card F/Q)^2*(k-1)<Fintype.card F+1)
    (hmca : epsMCA (F:=F) (ReedSolomon.code D k : Set (I → F)) δ ≤ 1/(Q:ℝ≥0∞)) :
    Lambda (ReedSolomon.code D k : Set (I → F)) (((Fintype.card I-t:ℕ):ℝ)/(Fintype.card I:ℝ))
      ≤ ((Fintype.card F/Q:ℕ):ℕ∞) := by
  classical
  by_contra! hlist
  obtain ⟨u,v,hbad⟩ := budget D δ hk hkt htn hδ hroom hlist
  let C := (ReedSolomon.code D k : Set (I → F))
  let G := univ.filter (mcaEvent (F:=F) C δ u v)
  have hrate := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set C δ
    (![u,v] : WordStack F (Fin 2) I) G (fun γ hγ => (mem_filter.mp hγ).2)
  exact hbad.not_ge ((BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hQ).1 (hrate.trans hmca))

/-- At 128-bit tolerance the field condition is automatic for all q ≤ 2²¹⁶
and all dimensions at most 2⁴⁰, including both nominated production fields. -/
theorem security128_room (q k : ℕ) (hq : q≤2^216) (hk : k≤2^40) :
    (q/2^128)^2*(k-1)<q+1 := by
  have hb : q/2^128 ≤ 2^88 := (Nat.div_le_div_right hq).trans (by decide)
  have hprod : (q/2^128)*(k-1) ≤ 2^128 :=
    (Nat.mul_le_mul hb (show k-1≤2^40 by omega)).trans (by decide)
  calc
    (q/2^128)^2*(k-1) = (q/2^128)*((q/2^128)*(k-1)) := by ring
    _ ≤ (q/2^128)*2^128 := Nat.mul_le_mul_left _ hprod
    _ < q+1 := (Nat.div_mul_le_self ..).trans_lt (Nat.lt_succ_self _)

/-- In the prize's dimension range, an MCA bound on any named code over
a field of size at most 2²¹⁶ also certifies the same scalar list budget. -/
theorem closed_list_128 [Nonempty I] (D : I ↪ F) (δ : ℝ≥0) {k t : ℕ} (hk : 0<k)
    (hkt : k<t) (htn : t≤Fintype.card I) (hδ : (1-δ)*(Fintype.card I : ℝ≥0)≤t)
    (hq : Fintype.card F≤2^216) (hsize : k≤2^40)
    (hmca : epsMCA (F:=F) (ReedSolomon.code D k : Set (I → F)) δ ≤ 1/((2^128:ℕ):ℝ≥0∞)) :
    Lambda (ReedSolomon.code D k : Set (I → F)) (((Fintype.card I-t:ℕ):ℝ)/(Fintype.card I:ℝ))
      ≤ ((Fintype.card F/2^128:ℕ):ℕ∞) :=
  closed_list_of_mca D δ hk hkt htn hδ (by decide) (security128_room _ _ hq hsize) hmca

#print axioms closed_list_128
#print axioms closed_list_of_mca
#print axioms collisions
#print axioms from_polynomials
#print axioms from_list
#print axioms budget
end ProximityGap.SameDomainListMca
