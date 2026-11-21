/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.CubicApolarAttainment
import Mathlib.NumberTheory.PrimesCongruentOne

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

omit [Fintype K] in
/-- A scalar is a bad label whenever every other point of its power fiber lies
in the domain. The scalar itself may lie outside the domain. -/
theorem event_of_erased_fiber (D : Finset K) (k e : ℕ) (hk : 0 < k) (he : 0 < e)
    (hD : D.card = k+2*e) {g t : K} (hg : IsPrimitiveRoot g (e+1)) (ht : t ≠ 0)
    (hsub : (nthRootsFinset (e+1) (t^(e+1))).erase t ⊆ D) :
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
  have hE : E ⊆ D := hsub
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

omit [Fintype K] in
/-- Removing all but one site of a full power fiber gives a bad witness
on its complementary site set. -/
theorem event_of_fiber (D : Finset K) (k e : ℕ) (hk : 0 < k) (he : 0 < e)
    (hD : D.card = k+2*e) {g t : K} (hg : IsPrimitiveRoot g (e+1)) (ht : t ≠ 0)
    (hsub : nthRootsFinset (e+1) (t^(e+1)) ⊆ D) :
    let dom := Function.Embedding.subtype (· ∈ D)
    let V := Lagrange.nodal D id
    _root_.ProximityGap.mcaEvent (ReedSolomon.code dom k : Set (D → K))
      ((e:ℝ≥0)/D.card) (fun i => ((V*X) /ₘ X^(e+1)).eval i.val)
      (fun i => -(V /ₘ X^(e+1)).eval i.val) t :=
  event_of_erased_fiber D k e hk he hD hg ht ((erase_subset ..).trans hsub)

omit [Fintype K] in
/-- A union of complete nonzero power fibers has the expected cardinality. -/
theorem full_union_card (e : ℕ) {g : K} (hg : IsPrimitiveRoot g (e+1)) (I : Finset K)
    (hpow : ∀ c ∈ I, c ≠ 0 ∧ ∃ x : K, x^(e+1)=c) :
    (I.biUnion fun c : K => nthRootsFinset (e+1) c).card = I.card*(e+1) := by
  classical
  have dj : (I : Set K).PairwiseDisjoint (fun c : K => nthRootsFinset (e+1) c) := by
    intro a _ b _ hab
    apply disjoint_left.mpr
    intro x hx hy
    exact hab (((mem_nthRootsFinset (Nat.succ_pos e) _).mp hx).symm.trans
      ((mem_nthRootsFinset (Nat.succ_pos e) _).mp hy))
  rw [card_biUnion dj]
  calc
    _ = ∑ _c ∈ I, (e+1) := sum_congr rfl fun c hc =>
      (full_power_fiber (Nat.succ_pos e) hg (hpow c hc).1 (hpow c hc).2).1
    _ = _ := by simp

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
  have hcard : A.card = I.card*(e+1) := full_union_card e hg I hpow
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

open Classical in
/-- Choose distinct nonzero power fibers explicitly in a splitting prime field. -/
theorem prime_fibers (e m p : ℕ) [Fact p.Prime] (he : 0 < e) (hp : 1<p)
    (hroom : m*(e+1) ≤ p-1) (hdiv : e+1 ∣ p-1) :
    ∃ g : ZMod p, IsPrimitiveRoot g (e+1) ∧ ∃ I : Finset (ZMod p), I.card=m ∧
      ∀ c ∈ I, c≠0 ∧ ∃ x : ZMod p, x^(e+1)=c := by
  obtain ⟨z,hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  let g := (z : ZMod p)
  have hg : IsPrimitiveRoot g (p-1) := IsPrimitiveRoot.coe_units_iff.mpr <|
    IsPrimitiveRoot.iff_orderOf.mpr <| by simpa only [Nat.card_eq_fintype_card,ZMod.card_units] using hz
  obtain ⟨c,hc⟩ := hdiv
  have h₁ : IsPrimitiveRoot (g^c) (e+1) := IsPrimitiveRoot.pow (by omega : 0<p-1) hg
    (hc.trans (Nat.mul_comm ..))
  let rep := fun j : ℕ => g^(j*(e+1))
  let I := (range m).image rep
  have ltord (j : ℕ) (hj : j ∈ range m) : j*(e+1) < p-1 := by
    exact (Nat.mul_lt_mul_of_pos_right (mem_range.mp hj) (show 0<e+1 by omega)).trans_le
      hroom
  have hi : I.card=m := by
    rw [Finset.card_image_of_injOn,card_range]
    intro i hi j hj hij
    exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos e) (hg.pow_inj (ltord i hi) (ltord j hj) hij)
  have hpow : ∀ a ∈ I, a≠0 ∧ ∃ x : ZMod p, x^(e+1)=a := by
    intro a ha
    obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    exact ⟨pow_ne_zero _ z.ne_zero,g^j,(pow_mul ..).symm⟩
  exact ⟨g^c,h₁,I,hi,hpow⟩

open Classical in
/-- On every sufficiently large prime field splitting the power fibers,
one can choose their representatives and the additional sites. -/
theorem prime_attain (k e m p : ℕ) [Fact p.Prime] (hk : 0<k) (he : 0<e)
    (hroom : m*(e+1) ≤ k+2*e) (hp : k+2*e < p) (hdiv : e+1 ∣ p-1) :
    ∃ D : Finset (ZMod p), D.card=k+2*e ∧ ∃ u v : D → ZMod p,
      m*(e+1) ≤ (univ.filter fun t : ZMod p => _root_.ProximityGap.mcaEvent
        (ReedSolomon.code (Function.Embedding.subtype (·∈D)) k : Set (D → ZMod p))
        ((e:ℝ≥0)/D.card) u v t).card := by
  classical
  obtain ⟨g,h₁,I,hi,hpow⟩ := prime_fibers e m p he (by omega) (hroom.trans (by omega)) hdiv
  simpa only [hi] using attain k e hk he h₁ I hpow (hi ▸ hroom) (by rw [ZMod.card];omega)

open Classical in
/-- When n+1 is a multiple of the fiber size, deleting one point of a union
of full fibers gives n−e+1 distinct bad labels, including the deleted point. -/
theorem prime_partial (k e p : ℕ) [Fact p.Prime] (hk : 0<k) (he : 0<e)
    (hshape : e+1 ∣ k+2*e+1) (hp : k+2*e<p) (hdiv : e+1 ∣ p-1) :
    let n := k+2*e
    ∃ D : Finset (ZMod p), D.card=n ∧ ∃ u v : D → ZMod p, n-e+1 ≤
      (univ.filter fun t : ZMod p => _root_.ProximityGap.mcaEvent
        (ReedSolomon.code (Function.Embedding.subtype (·∈D)) k : Set (D → ZMod p))
        ((e:ℝ≥0)/D.card) u v t).card := by
  let n := k+2*e
  obtain ⟨b,hb⟩ := hshape
  have hbn : b*(e+1)=n+1 := (Nat.mul_comm ..).trans hb.symm
  have hbpos : 0 < b := by by_contra! h; have := Nat.eq_zero_of_le_zero h; simp_all
  have hroom : b*(e+1)≤p-1 := by
    obtain ⟨a,ha⟩ := hdiv
    by_contra! h
    have hab : a < b := by
      apply Nat.lt_of_mul_lt_mul_left (a:=e+1)
      simpa only [Nat.mul_comm b,ha] using h
    have hle := Nat.mul_le_mul_left (e+1) (Nat.succ_le_of_lt hab)
    rw [Nat.mul_succ,← ha,← hb] at hle
    omega
  obtain ⟨g,hg,I,hi,hpow⟩ := prime_fibers e b p he (by omega) hroom hdiv
  obtain ⟨c,hc⟩ := Finset.card_pos.mp (by omega : 0<I.card)
  obtain ⟨t0,ht0⟩ := (hpow c hc).2
  let A := I.biUnion fun c => nthRootsFinset (e+1) c
  let D := A.erase t0
  have hA (x : ZMod p) : x∈A ↔ x^(e+1)∈I := by simp [A,mem_nthRootsFinset (Nat.succ_pos e)]
  have htA : t0∈A := (hA _).2 (ht0 ▸ hc)
  have ht0nz : t0≠0 := by rintro rfl; rw [zero_pow (by omega : e+1≠0)] at ht0; exact (hpow c hc).1 ht0.symm
  have hsize : A.card=n+1 := (full_union_card e hg I hpow).trans (by rw [hi,hbn])
  have hD : D.card=n := by rw [show D=A.erase t0 from rfl,card_erase_of_mem htA,hsize,Nat.add_sub_cancel]
  let J := I.erase c
  let Z := J.biUnion fun j => nthRootsFinset (e+1) j
  have hZ (x : ZMod p) : x∈Z ↔ x^(e+1)∈J := by simp [Z,mem_nthRootsFinset (Nat.succ_pos e)]
  have htZ : t0∉Z := fun h => (Finset.mem_erase.mp ((hZ _).1 h)).1 ht0
  have hcount : (insert t0 Z).card = n-e+1 := by
    have hj := full_union_card e hg J (fun j hj => hpow j (Finset.mem_of_mem_erase hj))
    have hjs : J.card+1=b := by simp only [J,card_erase_of_mem hc,hi]; omega
    have hx := congrArg (fun j : ℕ => j*(e+1)) hjs
    rw [Nat.add_mul,one_mul,hbn] at hx
    rw [card_insert_of_notMem htZ]
    change Z.card+1=n-e+1
    rw [show Z.card=J.card*(e+1) from hj]
    omega
  let V := Lagrange.nodal D id
  refine ⟨D,hD,fun i => ((V*X) /ₘ X^(e+1)).eval i.val,fun i => -(V /ₘ X^(e+1)).eval i.val,?_⟩
  rw [← hcount]
  apply card_le_card
  intro t ht
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  rcases mem_insert.mp ht with rfl | htz
  · apply event_of_erased_fiber D k e hk he hD hg ht0nz
    intro x hx
    obtain ⟨hne,hroot⟩ := mem_erase.mp hx
    exact mem_erase.mpr ⟨hne,(hA _).2 (by rwa [(mem_nthRootsFinset (Nat.succ_pos e) _).1 hroot,ht0])⟩
  · have htJ := (hZ _).1 htz
    obtain ⟨hne,htI⟩ := mem_erase.mp htJ
    have htnz : t≠0 := by rintro rfl; simpa using (hpow _ htI).1
    apply event_of_erased_fiber D k e hk he hD hg htnz
    intro x hx
    have hr := (mem_nthRootsFinset (Nat.succ_pos e) _).1 (mem_of_mem_erase hx)
    exact mem_erase.mpr ⟨fun ht => hne ((hr.symm.trans (congrArg (·^(e+1)) ht)).trans ht0),
      (hA _).2 (hr ▸ htI)⟩

open Classical in
/-- For any permitted number of complete fibers, the actual lower count is
attained or exceeded over arbitrarily large prime fields. -/
theorem arbitrarily_large_primes (k e m bound : ℕ) (hk : 0<k) (he : 0<e)
    (hroom : m*(e+1) ≤ k+2*e) :
    ∃ (p : ℕ) (hp : Nat.Prime p), bound<p ∧
      let _ : Fact p.Prime := ⟨hp⟩
      ∃ D : Finset (ZMod p), D.card=k+2*e ∧ ∃ u v : D → ZMod p,
        m*(e+1) ≤ (univ.filter fun t : ZMod p => _root_.ProximityGap.mcaEvent
          (ReedSolomon.code (Function.Embedding.subtype (·∈D)) k : Set (D → ZMod p))
          ((e:ℝ≥0)/D.card) u v t).card := by
  obtain ⟨p,hp,hbig,hcong⟩ := Nat.exists_prime_gt_modEq_one (max bound (k+2*e)) (Nat.succ_ne_zero e)
  let _ : Fact p.Prime := ⟨hp⟩
  exact ⟨p,hp,(le_max_left ..).trans_lt hbig,
    prime_attain k e m p hk he hroom ((le_max_right ..).trans_lt hbig) hcong.symm.dvd'⟩

#print axioms prime_partial
#print axioms prime_attain
#print axioms arbitrarily_large_primes
#print axioms event_of_fiber
#print axioms attain
end ArkLib.ProximityGap.Frontier.PowerFiberEndpoint
