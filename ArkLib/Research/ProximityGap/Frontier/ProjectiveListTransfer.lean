/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.DeepListMcaTransfer

/-! # Evaluation of a scalar list on the projective line gives bad MCA scalars

The domain, dimension, alphabet and integer agreement threshold are fixed.
At an existing evaluation site the second word is a one-point spike. At an
external finite point it is a reciprocal. At infinity it is the degree-k
monomial. Each choice gives the evaluations of every nearby polynomial as
bad labels on one received pair.
-/

set_option autoImplicit false
open Polynomial Finset Code
open scoped NNReal ENNReal
namespace ProximityGap.ProjectiveListTransfer
variable {F I : Type} [Field F] [DecidableEq F] [Fintype I] [DecidableEq I]

/-- Evaluation of the degree-d homogenization of a polynomial. -/
def value (d : ℕ) (z : Option F) (f : F[X]) : F :=
  z.elim (f.coeff d) f.eval

omit [DecidableEq F] in
private theorem spike_event (D : I ↪ F) {k : ℕ} (hk : 0<k) (j : I) (y : I → F)
    (f : F[X]) (hf : f.natDegree<k) (S : Finset I) (δ : ℝ≥0)
    (hs : (1-δ)*Fintype.card I ≤ (S.card:ℝ≥0)) (ht : k<S.card)
    (ha : ∀ i∈S, y i=f.eval (D i)) :
    mcaEvent (ReedSolomon.code D k : Set (I → F)) δ
      (fun i => if i=j then 0 else y i) (fun i => if i=j then -1 else 0) (-(f.eval (D j))) := by
  classical
  let _ : NeZero k := ⟨hk.ne'⟩
  refine ⟨insert j S,hs.trans (by exact_mod_cast card_le_card (subset_insert j S)),
    ⟨_,ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr ⟨f,hf,fun _ => rfl⟩,?_⟩,?_⟩
  · intro i hi
    by_cases hij : i=j
    · simp [hij,smul_eq_mul]
    · simp [hij,smul_eq_mul,ha i (mem_of_mem_insert_of_ne hi hij)]
  · rintro ⟨_,_,v,hv,hpair⟩
    obtain ⟨g,hg,hv'⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hv
    have hzero : g=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' g ((S.erase j).map D)
      (by
        intro x hx
        obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
        have hh := hpair i (mem_insert_of_mem (mem_of_mem_erase hi))
        simpa only [hv',(mem_erase.mp hi).1,ite_false] using hh.2)
      (by
        rw [card_map]
        have hh := card_le_card (show S ⊆ insert j (S.erase j) by intro x hx; by_cases h:x=j <;> simp [h,hx])
        have hb := card_insert_le j (S.erase j)
        omega)
    have hh := hpair j (mem_insert_self ..)
    simpa [← hv' j,hzero] using hh.2

omit [DecidableEq I] [DecidableEq F] in
private theorem infinity_event (D : I ↪ F) {k : ℕ} (hk : 0<k) (y : I → F)
    (f : F[X]) (hf : f.natDegree<k) (S : Finset I) (δ : ℝ≥0)
    (hs : (1-δ)*Fintype.card I ≤ (S.card:ℝ≥0)) (ht : k<S.card)
    (ha : ∀ i∈S, y i=f.eval (D i)) :
    mcaEvent (ReedSolomon.code D k : Set (I → F)) δ (fun i => D i*y i)
      (fun i => (D i)^k) (-(f.coeff (k-1))) := by
  classical
  let _ : NeZero k := ⟨hk.ne'⟩
  let g : F[X] := X*f-C (f.coeff (k-1))*X^k
  have hdeg : g.natDegree≤k := (natDegree_sub_le ..).trans (max_le
    ((natDegree_mul_le (p:=(X:F[X])) (q:=f)).trans (by rw [natDegree_X];omega))
    ((natDegree_C_mul_le ..).trans (natDegree_X_pow_le _)))
  have hz : g.coeff k=0 := by
    rw [show g=X*f-C (f.coeff (k-1))*X^k from rfl,coeff_sub,coeff_C_mul_X_pow]
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    simp [coeff_X_mul]
  have hg : g.natDegree<k := by
    by_contra! h
    have hn : g.natDegree=k := by omega
    rw [← hn,coeff_natDegree,leadingCoeff_eq_zero] at hz
    rw [hz,natDegree_zero] at hn
    omega
  refine ⟨S,hs,⟨_,ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr ⟨g,hg,fun _ => rfl⟩,?_⟩,?_⟩
  · intro i hi
    simp [g,ha i hi,smul_eq_mul]
    ring
  · rintro ⟨_,_,v,hv,hpair⟩
    obtain ⟨q,hq,hv'⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hv
    have he : q-X^k=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (S.map D) (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
      rw [eval_sub,eval_pow,eval_X,hv', (hpair i hi).2,sub_self])
      (by rw [card_map]; exact ((natDegree_sub_le ..).trans (max_le hq.le (natDegree_X_pow_le _))).trans_lt ht)
    rw [sub_eq_zero.mp he,natDegree_X_pow] at hq
    omega

/-- Every projective fingerprint on the original list has a common pair of
received words on the original code, with one bad scalar per distinct value. -/
theorem projective_event (D : I ↪ F) {k : ℕ} (hk : 0<k) (z : Option F) (y : I → F)
    (δ : ℝ≥0) : ∃ u v : I → F, ∀ (f : F[X]), f.natDegree<k →
      ∀ S : Finset I, (1-δ)*Fintype.card I ≤ (S.card:ℝ≥0) → k<S.card →
      (∀ i∈S, y i=f.eval (D i)) →
      mcaEvent (ReedSolomon.code D k : Set (I → F)) δ u v (-(value (k-1) z f)) := by
  classical
  cases z with
  | none => exact ⟨_,_,fun f hf S hs ht ha => infinity_event D hk y f hf S δ hs ht ha⟩
  | some z =>
    by_cases hz : ∃ j, D j=z
    · obtain ⟨j,rfl⟩ := hz
      exact ⟨_,_,fun f hf S hs ht ha => spike_event D hk j y f hf S δ hs ht ha⟩
    · exact ⟨_,_,fun f hf S hs ht ha => DeepListMcaTransfer.quotient_event D hk z
        (fun i he => hz ⟨i,he⟩) y f hf.le S δ hs ht ha⟩

#print axioms projective_event
end ProximityGap.ProjectiveListTransfer
