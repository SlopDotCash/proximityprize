/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorBadEventRichPointBridge
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-! # Monotonicity of the worst line-MCA error in the Reed–Solomon dimension

On a support longer than the larger dimension, a row outside the smaller code
can enter the larger code for at most one projective linear multiplier. There
are more multipliers than scalar labels. One multiplier therefore transports
all of a received pair's bad scalar witnesses to the next dimension.
-/
set_option autoImplicit false
noncomputable section
open Polynomial Finset Code
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.DimensionRaiseMCA
open _root_.ProximityGap _root_.ProximityGap.MCAWitnessSpread
attribute [local instance] Classical.propDecidable

variable {I F : Type} [Field F]

private theorem degree_iff {D : ℕ} {P : F[X]} (hD : D ≠ 0) : P.degree < D ↔ P.natDegree < D := by
  rcases eq_or_ne P 0 with rfl | h
  · simp [Nat.pos_of_ne_zero hD]
  · exact (natDegree_lt_iff_degree_lt h).symm

private def Fits (C : Submodule F (I → F)) (S : Finset I) (v : I → F) : Prop :=
  ∃ w ∈ C, ∀ i ∈ S, w i=v i

/-- Projective degree-one coordinate multiplier. The point at infinity is the constant multiplier. -/
def mult (dom : I ↪ F) (a : Option F) (v : I → F) : I → F :=
  match a with
  | none => v
  | some c => fun i => dom i*v i+c*v i

private theorem fit_of_joint (dom : I ↪ F) {k : ℕ} (hk : 0<k) (S : Finset I)
    (hS : k+1<S.card) (v : I → F)
    (h : pairJointAgreesOn (ReedSolomon.code dom (k+1) : Set (I → F)) S (fun i => dom i*v i) v) :
    Fits (ReedSolomon.code dom k) S v := by
  obtain ⟨u,hu,w,hw,ha⟩ := h
  obtain ⟨P,hP,hp⟩ := ReedSolomon.mem_code_iff_eval.mp hw
  obtain ⟨Q,hQ,hq⟩ := ReedSolomon.mem_code_iff_eval.mp hu
  have hp' := (degree_iff (by omega : k+1≠0)).mp hP
  have hq' := (degree_iff (by omega : k+1≠0)).mp hQ
  have he : X*P=Q := by
    apply sub_eq_zero.mp
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (S.map dom)
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
      simp only [eval_sub,eval_mul,eval_X,hp,hq,(ha i hi).1,(ha i hi).2,sub_self]
    · rw [card_map]
      apply (natDegree_sub_le ..).trans_lt
      have hb := natDegree_mul_le (p:=(X : F[X])) (q:=P)
      rw [natDegree_X] at hb
      omega
  refine ⟨ReedSolomon.evalOnPoints dom P,ReedSolomon.evalOnPoints_mem_code_of_degree_lt ?_,?_⟩
  · apply (degree_iff hk.ne').mpr
    by_cases hz : P=0
    · simpa [hz] using hk
    · rw [← he,natDegree_X_mul hz] at hq'
      omega
  · intro i hi
    exact (hp i).trans (ha i hi).2

variable [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I]

private theorem at_most_one (dom : I ↪ F) {k : ℕ} (hk : 0<k) (S : Finset I) (hS : k+1<S.card)
    (v : I → F) (hv : ¬Fits (ReedSolomon.code dom k) S v) :
    (univ.filter fun a : Option F => Fits (ReedSolomon.code dom (k+1)) S (mult dom a v)).card ≤ 1 := by
  classical
  let C := ReedSolomon.code dom (k+1)
  have hno : ¬pairJointAgreesOn (C : Set (I → F)) S (fun i => dom i*v i) v :=
    fun hj => hv (fit_of_joint dom hk S hS v hj)
  have mixed (c : F) (h0 : Fits C S (mult dom none v)) (h1 : Fits C S (mult dom (some c) v)) : False := by
    obtain ⟨w,hw,ha⟩ := h0
    obtain ⟨u,hu,hb⟩ := h1
    apply hno
    refine ⟨u-c • w,C.sub_mem hu (C.smul_mem c hw),w,hw,fun i hi => ⟨?_,ha i hi⟩⟩
    change u i-c*w i=_
    rw [hb i hi, ha i hi]
    simp [mult]
  apply card_le_one.mpr
  intro a ha b hb
  have A := (mem_filter.mp ha).2
  have B := (mem_filter.mp hb).2
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some d => exact (mixed d A B).elim
  | some c =>
    cases b with
    | none => exact (mixed c B A).elim
    | some d => exact congrArg some (unique_bad_gamma_common_witness C S _ _ hno A B)

omit [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I] in
private theorem transform_fit (dom : I ↪ F) {k : ℕ} (hk : 0<k) (a : Option F)
    (S : Finset I) (v : I → F) (hv : Fits (ReedSolomon.code dom k) S v) :
    Fits (ReedSolomon.code dom (k+1)) S (mult dom a v) := by
  obtain ⟨w,hw,ha⟩ := hv
  obtain ⟨P,hP,hev⟩ := ReedSolomon.mem_code_iff_eval.mp hw
  have hd := (degree_iff hk.ne').mp hP
  cases a with
  | none =>
    refine ⟨ReedSolomon.evalOnPoints dom P,ReedSolomon.evalOnPoints_mem_code_of_degree_lt ?_,
      fun i hi => (hev i).trans (ha i hi)⟩
    exact (degree_iff (by omega : k+1≠0)).mpr (by omega)
  | some c =>
    let Q : F[X] := (X+C c)*P
    refine ⟨ReedSolomon.evalOnPoints dom Q,ReedSolomon.evalOnPoints_mem_code_of_degree_lt ?_,?_⟩
    · apply (degree_iff (by omega : k+1≠0)).mpr
      have hb := natDegree_mul_le (p:=X+C c) (q:=P)
      have hc := natDegree_add_le (X : F[X]) (C c)
      simp only [natDegree_X,natDegree_C] at hc
      change ((X+C c)*P).natDegree<k+1
      omega
    · intro i hi
      change Q.eval (dom i)=_
      simp only [Q,eval_mul,eval_add,eval_X,eval_C,hev,ha i hi,mult,add_mul]

omit [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I] in
private theorem mul_fold (dom : I ↪ F) (a : Option F) (v w : I → F) (z : F) (i : I) :
    mult dom a (fun j => v j+z • w j) i=mult dom a v i+z • mult dom a w i := by
  cases a with
  | none => rfl
  | some c => simp only [mult,smul_eq_mul]; ring

/-- A single linear coordinate multiplier preserves all the original pair's bad scalars. -/
theorem transport (dom : I ↪ F) {k : ℕ} (hk : 0<k) (δ : ℝ≥0)
    (ht : k+1<⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊) (v w : I → F) :
    ∃ a : Option F, ∀ z : F,
      mcaEvent (ReedSolomon.code dom k : Set (I → F)) δ v w z →
      mcaEvent (ReedSolomon.code dom (k+1) : Set (I → F)) δ (mult dom a v) (mult dom a w) z := by
  classical
  let G := univ.filter fun z : F => mcaEvent (ReedSolomon.code dom k : Set (I → F)) δ v w z
  have sel (z : G) := (mem_filter.mp z.property).2
  choose S hs hfold hj using sel
  have row (z : G) : ∃ y : I → F, (y=v ∨ y=w) ∧ ¬ Fits (ReedSolomon.code dom k) (S z) y := by
    by_cases hv : Fits (ReedSolomon.code dom k) (S z) v
    · refine ⟨w,Or.inr rfl,?_⟩
      rintro ⟨W,hW,hw⟩
      obtain ⟨V,hV,hh⟩ := hv
      exact hj z ⟨V,hV,W,hW,fun i hi => ⟨hh i hi,hw i hi⟩⟩
    · exact ⟨v,Or.inl rfl,hv⟩
  choose y hy hbad using row
  let E (z : G) := univ.filter fun a : Option F => Fits (ReedSolomon.code dom (k+1)) (S z) (mult dom a (y z))
  have small (z : G) : (E z).card≤1 :=
    at_most_one dom hk (S z) (ht.trans_le (Nat.ceil_le.mpr (hs z))) (y z) (hbad z)
  have hm : (univ.biUnion E).card≤G.card := card_biUnion_le.trans
    ((sum_le_sum (s:=univ) (fun z _ => small z)).trans_eq (by simp))
  have hall : (univ.biUnion E).card < (univ : Finset (Option F)).card := by
    have hh := card_le_univ G
    simp only [card_univ,Fintype.card_option]
    omega
  obtain ⟨a,_,hout⟩ := exists_mem_notMem_of_card_lt_card hall
  refine ⟨a,fun z hz => ?_⟩
  let Z : G := ⟨z,mem_filter.mpr ⟨mem_univ _,hz⟩⟩
  refine ⟨S Z,hs Z,?_,?_⟩
  · obtain ⟨V,hV,hv⟩ := transform_fit dom hk a (S Z) (fun i => v i+z • w i) (hfold Z)
    exact ⟨V,hV,fun i hi => (hv i hi).trans (mul_fold ..)⟩
  · rintro ⟨V,hV,W,hW,hh⟩
    apply hout
    refine mem_biUnion.mpr ⟨Z,mem_univ _,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    rcases hy Z with hv | hw
    · rw [hv]
      exact ⟨V,hV,fun i hi => (hh i hi).1⟩
    · rw [hw]
      exact ⟨W,hW,fun i hi => (hh i hi).2⟩

/-- As long as every permitted witness is longer than the larger dimension, the worst
two-row MCA probability can only increase when the dimension increases by one. -/
theorem eps_le_succ (dom : I ↪ F) {k : ℕ} (hk : 0<k) (δ : ℝ≥0)
    (ht : k+1<⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊) :
    epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) δ ≤
      epsMCA (F:=F) (ReedSolomon.code dom (k+1) : Set (I → F)) δ := by
  classical
  rw [epsMCA_eq_iSup_badCount_div, ENNReal.iSup_div]
  apply iSup_le
  intro u
  obtain ⟨a,ha⟩ := transport dom hk δ ht (u 0) (u 1)
  let U : WordStack F (Fin 2) I := fun j => mult dom a (u j)
  exact epsMCA_ge_card_div_of_mcaEvent_set (ReedSolomon.code dom (k+1) : Set (I → F)) δ U _
    (fun z hz => ha z (mem_filter.mp hz).2)

/-- The dimension comparison holds over every finite field on the same evaluation domain. -/
theorem eps_mono_dimension (dom : I ↪ F) {k K : ℕ} (hk : 0<k) (hK : k≤K) (δ : ℝ≥0)
    (ht : K<⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊) :
    epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) δ ≤
      epsMCA (F:=F) (ReedSolomon.code dom K : Set (I → F)) δ := by
  induction K, hK using Nat.le_induction with
  | base => exact le_rfl
  | succ K hK ih => exact (ih (by omega)).trans (eps_le_succ dom (by omega) δ ht)

#print axioms eps_mono_dimension
end ArkLib.ProximityGap.Frontier.DimensionRaiseMCA
