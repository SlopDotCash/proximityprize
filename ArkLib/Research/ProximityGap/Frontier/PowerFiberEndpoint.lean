/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.CubicApolarAttainment

/-! # Power-fiber witnesses at the unique-decoding endpoint

At length `k + 2*e`, each site of a full nonzero power fiber of size `e+1`
gives a different bad scalar at radius `e/n`. All of the witnesses share
the same two received words, including across different fibers.
-/

set_option autoImplicit false
open Finset Polynomial
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.PowerFiberEndpoint
open CubicApolarAttainment

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
private theorem fold_identity (V Q : K[X]) (t : K) (m : ℕ)
    (hid : V*(X-C t) = Q*(X^m-C (t^m))) :
    (V*X) /ₘ X^m - C t*(V /ₘ X^m) = Q-C (t^m)*(Q /ₘ X^m) := by
  have h := congrArg (fun P : K[X] => P /ₘ X^m) hid
  simp only [mul_sub, sub_divByMonic] at h
  rw [mul_comm Q (X^m), mul_divByMonic_cancel_left _ (monic_X_pow _),
    mul_comm V (C t), mul_comm Q (C (t^m)), ← smul_eq_C_mul, ← smul_eq_C_mul,
    smul_divByMonic, smul_divByMonic, smul_eq_C_mul, smul_eq_C_mul] at h
  exact h

/-- Removing all but one site of a full power fiber gives a bad witness
on its complementary site set. -/
theorem event_of_fiber (D : Finset K) (k e : ℕ) (hk : 0 < k) (he : 0 < e)
    (hD : D.card = k+2*e) {g t : K} (hg : IsPrimitiveRoot g (e+1)) (ht : t ≠ 0)
    (hsub : nthRootsFinset (e+1) (t^(e+1)) ⊆ D) :
    let dom := Function.Embedding.subtype (· ∈ D)
    let V := Lagrange.nodal D id
    _root_.ProximityGap.mcaEvent (ReedSolomon.code dom k : Set (D → K))
      ((e:ℝ≥0)/D.card) (fun i => ((V*X) /ₘ X^(e+1)).eval i.val)
      (fun i => -(V /ₘ X^(e+1)).eval i.val) t := by
  classical
  let A := nthRootsFinset (e+1) (t^(e+1))
  let E := A.erase t
  let S := (D \ E).subtype (· ∈ D)
  let V := Lagrange.nodal D id
  let Q := Lagrange.nodal (D \ E) id
  have hA := full_power_fiber (Nat.succ_pos e) hg (pow_ne_zero _ ht) ⟨t,rfl⟩
  have hta : t ∈ A := (mem_nthRootsFinset (Nat.succ_pos e) _).mpr rfl
  have hE : E ⊆ D := (erase_subset t A).trans hsub
  have hEc : E.card=e := by simp [E, card_erase_of_mem hta, show A.card = e+1 from hA.1]
  have hSc : S.card = k+e := by
    dsimp only [S]
    rw [card_subtype, filter_eq_self.mpr (fun _ hx => (mem_sdiff.mp hx).1),
      card_sdiff_of_subset hE, hD, hEc]
    omega
  have hz (i : D) (hi : i∈S) : Q.eval i.val=0 :=
    Lagrange.eval_nodal_at_node (v := id) (i := i.val) (by simpa only [S,mem_subtype] using hi)
  have hqdeg : Q.natDegree=k+e := by
    dsimp only [Q]
    rw [Lagrange.natDegree_nodal,card_sdiff_of_subset hE,hD,hEc]
    omega
  have hid : V*(X-C t)=Q*(X^(e+1)-C (t^(e+1))) := by
    have hn : Lagrange.nodal E id * (X-C t) = Lagrange.nodal A id := by
      change (∏ i ∈ A.erase t, (X-C i)) * (X-C t) = ∏ i ∈ A, (X-C i)
      exact prod_erase_mul _ _ hta
    rw [show V = Q * Lagrange.nodal E id from (nodal_partition D E hE).symm,
      mul_assoc, hn, hA.2]
  let U := V /ₘ X^(e+1)
  let P := -(C (t^(e+1))*(Q /ₘ X^(e+1)))
  have hU : U.natDegree = k+e-1 := by
    dsimp only [U,V]
    rw [natDegree_divByMonic _ (monic_X_pow _), natDegree_X_pow, Lagrange.natDegree_nodal, hD]
    omega
  have hP : P.natDegree<k := by
    dsimp only [P]
    rw [natDegree_neg]
    apply natDegree_mul_le.trans_lt
    rw [natDegree_C, zero_add, natDegree_divByMonic _ (monic_X_pow _),natDegree_X_pow,hqdeg]
    omega
  have hfold := fold_identity V Q t (e+1) hid
  refine ⟨S, ?_, ⟨fun i => P.eval i.val,
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval P hP (fun _ => rfl), ?_⟩, ?_⟩
  · rw [Fintype.card_coe, tsub_mul, one_mul, div_mul_cancel₀ _ (by rw [hD]; positivity), hD, hSc]
    simp only [show k+2*e=k+e+e by omega, Nat.cast_add, add_tsub_cancel_right, le_refl]
  · intro i hi
    have hh := congrArg (fun R : K[X] => R.eval i.val) hfold
    simpa [P, hz i hi, smul_eq_mul, sub_eq_add_neg] using hh.symm
  · rintro ⟨_,_,row,hrow,joint⟩
    let _ : NeZero k := ⟨hk.ne'⟩
    obtain ⟨R,hR,hpoly⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hrow
    have hz' (x : K) (hx : x ∈ D \ E) : (R+U).eval x=0 := by
      let i : D := ⟨x,(mem_sdiff.mp hx).1⟩
      have hj := (hpoly i).trans (joint i (by simpa only [S,mem_subtype] using hx)).2
      rw [eval_add]
      exact add_eq_zero_iff_eq_neg.mpr (show R.eval x = -U.eval x from hj)
    have hh := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (R+U) (D \ E) hz' (by
      apply (natDegree_add_le ..).trans_lt
      rw [card_sdiff_of_subset hE,hD,hEc,hU]
      omega)
    have hR' : R = -U := eq_neg_of_add_eq_zero_left hh
    rw [hR',natDegree_neg,hU] at hR
    omega

open Classical in
/-- Every site in the supplied complete fibers is a distinct bad scalar. -/
theorem attain (k e : ℕ) (hk : 0<k) (he : 0<e) {g : K} (hg : IsPrimitiveRoot g (e+1))
    (I : Finset K) (hpow : ∀ c ∈ I, c ≠ 0 ∧ ∃ x : K, x^(e+1)=c)
    (hroom : I.card*(e+1) ≤ k+2*e) (hfield : k+2*e ≤ Fintype.card K) :
    ∃ D : Finset K, D.card=k+2*e ∧
      ∃ u v : D → K, I.card*(e+1) ≤ (univ.filter fun t : K => _root_.ProximityGap.mcaEvent
        (ReedSolomon.code (Function.Embedding.subtype (·∈D)) k : Set (D → K))
        ((e:ℝ≥0)/D.card) u v t).card := by
  classical
  let A := I.biUnion (fun c : K => nthRootsFinset (e+1) c)
  have ha (x : K) : x∈A ↔ x^(e+1)∈I := by simp [A,mem_nthRootsFinset (Nat.succ_pos e)]
  have hcard : A.card = I.card*(e+1) := by
    have dj : (I : Set K).PairwiseDisjoint (fun c : K => nthRootsFinset (e+1) c) := by
      intro a _ b _ hab
      apply disjoint_left.mpr
      intro x hx hy
      exact hab (((mem_nthRootsFinset (Nat.succ_pos e) _).mp hx).symm.trans
        ((mem_nthRootsFinset (Nat.succ_pos e) _).mp hy))
    dsimp only [A]
    rw [card_biUnion dj]
    calc
      _ = ∑ _c ∈ I, (e+1) := sum_congr rfl fun c hc =>
        (full_power_fiber (Nat.succ_pos e) hg (hpow c hc).1 (hpow c hc).2).1
      _ = _ := by simp
  obtain ⟨D,hAD,hD⟩ := exists_superset_card_eq (hcard ▸ hroom) hfield
  let V := Lagrange.nodal D id
  refine ⟨D,hD, fun i => ((V*X) /ₘ X^(e+1)).eval i.val,
    fun i => -(V /ₘ X^(e+1)).eval i.val, ?_⟩
  rw [← hcard]
  apply card_le_card
  intro t ht
  have hval := (ha t).mp ht
  have ht0 : t≠0 := by rintro rfl; simpa using (hpow _ hval).1
  refine mem_filter.mpr ⟨mem_univ _, event_of_fiber D k e hk he hD hg ht0 ?_⟩
  intro x hx
  exact hAD ((ha x).mpr ((mem_nthRootsFinset (Nat.succ_pos e) _).mp hx ▸ hval))

#print axioms event_of_fiber
#print axioms attain
end ArkLib.ProximityGap.Frontier.PowerFiberEndpoint
