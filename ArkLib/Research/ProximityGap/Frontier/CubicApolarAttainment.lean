/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.CubicApolarEvent
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange

/-! # A finite rate-half domain attaining the sharp predecessor MCA count -/

set_option autoImplicit false
open Finset Polynomial
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.CubicApolarAttainment
open CubicApolarEvent CubicApolarWitness

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

omit [Fintype K] in
theorem full_power_fiber {g a : K} {d : ℕ} (hd : 0<d) (hg : IsPrimitiveRoot g d)
    (ha : a ≠ 0) (hpower : ∃ x : K, x^d=a) :
    (nthRootsFinset d a).card = d ∧ Lagrange.nodal (nthRootsFinset d a) id = X^d-C a := by
  classical
  have hcard : (nthRoots d a).card = d := by simp [hg.card_nthRoots,hpower]
  have nodup := hg.nthRoots_nodup ha
  have hval : (nthRootsFinset d a).val = nthRoots d a := by
    rw [nthRootsFinset_def,← Multiset.toFinset_eq nodup]
  constructor
  · simpa only [Finset.card, hval] using hcard
  · have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic_X_pow_sub_C a hd.ne')
      (show (X^d-C a).roots.card = (X^d-C a).natDegree by rw [natDegree_X_pow_sub_C]; exact hcard)
    rw [← nthRoots,← hval] at h
    exact h

omit [Fintype K] in
theorem nodal_partition (D E : Finset K) (h : E⊆D) :
    Lagrange.nodal (D \ E) id * Lagrange.nodal E id = Lagrange.nodal D id :=
  prod_sdiff h

/-- A full M-th power coset and the three cube roots of one of its values
supply the complementary vanisher on the concrete evaluation set. -/
private theorem event_of_two_fibers (D : Finset K) (e L : ℕ) (he : 2≤e) (hM : e+3=3*L)
    (hD : D.card=4*(e+1)) (t : K) {g₁ g₂ : K} (h₁ : IsPrimitiveRoot g₁ (e+3))
    (h₂ : IsPrimitiveRoot g₂ 3) (ht : t ≠ 0) (hcube : ∃ a : K, a^3 = t)
    (hsub : nthRootsFinset (e+3) (t^L) ⊆ D) :
    let dom := Function.Embedding.subtype (· ∈ D)
    let V := Lagrange.nodal D id
    _root_.ProximityGap.mcaEvent (ReedSolomon.code dom (2*(e+1)) : Set (D → K))
      ((e:ℝ≥0)/D.card) (fun i => ((V*X^3) /ₘ X^(e+3)).eval i.val)
      (fun i => -(V /ₘ X^(e+3)).eval i.val) t := by
  classical
  let A := nthRootsFinset (e+3) (t^L)
  let B := nthRootsFinset 3 t
  let E := A \ B
  have hab : B ⊆ A := by
    intro x hx
    rw [mem_nthRootsFinset (by decide)] at hx
    rw [mem_nthRootsFinset (by omega),hM,pow_mul,hx]
  obtain ⟨ha,hmul⟩ := full_power_fiber (by omega : 0<e+3) h₁ (pow_ne_zero _ ht)
    (by obtain ⟨a,ha⟩ := hcube; exact ⟨a,by rw [hM,pow_mul,ha]⟩)
  obtain ⟨hb,hmul'⟩ := full_power_fiber (by decide : 0<3) h₂ ht hcube
  have hE : E ⊆ D := sdiff_subset.trans hsub
  have hEc : E.card=e := by
    change (A \ B).card=e
    rw [card_sdiff_of_subset hab,ha,hb]
    omega
  let S := (D \ E).subtype (·∈D)
  have hSc : S.card = 4*(e+1)-e := by
    dsimp only [S]
    rw [Finset.card_subtype,Finset.filter_eq_self.mpr (fun _ hx => (mem_sdiff.mp hx).1),
      card_sdiff_of_subset hE,hD,hEc]
  have hQ : (Lagrange.nodal (D \ E) id).natDegree=4*(e+1)-e := by
    rw [Lagrange.natDegree_nodal,card_sdiff_of_subset hE,hD,hEc]
  have hid : Lagrange.nodal D id * (X^3-C t) =
      Lagrange.nodal (D \ E) id * (X^(e+3)-C (t^L)) := by
    rw [← nodal_partition D E hE,← hmul',mul_assoc]
    have h := nodal_partition A B hab
    rw [hmul] at h
    rw [show Lagrange.nodal E id * Lagrange.nodal B id = X^(e+3)-C (t^L) from h]
  have hh := bad_at_locator (Function.Embedding.subtype (·∈D)) (Lagrange.nodal D id)
    (Lagrange.nodal (D \ E) id) t e L he (by simpa using hD)
    ((Lagrange.natDegree_nodal ..).trans hD) hQ hid S hSc
    (fun i hi => Lagrange.eval_nodal_at_node (v := @id K) (by simpa only [S,Finset.mem_subtype,Function.Embedding.subtype_apply] using hi))
  simpa only [Fintype.card_coe,Function.Embedding.subtype_apply] using hh

open Classical in
/-- Three distinct nonzero M-th power values supply exactly M bad cube labels
in a rate-half domain extended from their three complete power fibers. -/
theorem three_cosets_with_sites (e L : ℕ) (he : 2≤e) (hM : e+3=3*L) {g₁ g₂ : K}
    (h₁ : IsPrimitiveRoot g₁ (e+3)) (h₂ : IsPrimitiveRoot g₂ 3)
    (I : Finset K) (hI : I.card=3) (hpow : ∀ c ∈ I, c≠0 ∧ ∃ x : K, x^(e+3)=c)
    (hroom : 3*(e+3) ≤ 4*(e+1)) (hfield : 4*(e+1) ≤ Fintype.card K) :
    ∃ D : Finset K, D.card=4*(e+1) ∧ (∀ x : K, x^(e+3)∈I → x∈D) ∧
      ∃ u v : D → K, e+3 ≤ (univ.filter fun t : K => _root_.ProximityGap.mcaEvent
        (ReedSolomon.code (Function.Embedding.subtype (·∈D)) (2*(e+1)) : Set (D → K))
        ((e:ℝ≥0)/D.card) u v t).card := by
  classical
  let A := I.biUnion (fun c : K => nthRootsFinset (e+3) c)
  let T := A.image (fun x => x^3)
  have ha (x : K) : x ∈ A ↔ x^(e+3) ∈ I := by
    simp [A,mem_nthRootsFinset (by omega : 0<e+3)]
  have hAc : A.card = 3*(e+3) := by
    have dj : (I : Set K).PairwiseDisjoint (fun c : K => nthRootsFinset (e+3) c) := by
      intro a ha b hb hab
      apply disjoint_left.mpr
      intro x hx hy
      exact hab (((mem_nthRootsFinset (by omega) _).mp hx).symm.trans
        ((mem_nthRootsFinset (by omega) _).mp hy))
    dsimp only [A]
    rw [card_biUnion dj]
    calc
      _ = ∑ _x ∈ I, (e+3) := sum_congr rfl fun c hc =>
        (full_power_fiber (by omega) h₁ (hpow c hc).1 (hpow c hc).2).1
      _ = _ := by simp [hI]
  obtain ⟨D,hAD,hD⟩ := Finset.exists_superset_card_eq (hAc ▸ hroom) hfield
  have ht (t : K) (ht : t∈T) : t≠0 ∧ (∃ x : K, x^3=t) ∧ nthRootsFinset (e+3) (t^L) ⊆ A := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    have hxc := ha x |>.mp hx
    have hxp := (hpow _ hxc).1
    have hx0 : x≠0 := by rintro rfl; simp at hxp
    refine ⟨pow_ne_zero _ hx0,⟨x,rfl⟩,?_⟩
    intro y hy
    apply (ha y).mpr
    rw [(mem_nthRootsFinset (by omega) _).mp hy,← pow_mul,← hM]
    exact hxc
  have hcount : T.card = e+3 := by
    have hsum := card_eq_sum_card_image (fun x : K => x^3) A
    have eq : ∀ t ∈ T, (A.filter fun x => x^3=t).card=3 := by
      intro t ht'
      have h := ht t ht'
      have hsub : nthRootsFinset 3 t ⊆ A := by
        intro x hx
        apply h.2.2
        rw [mem_nthRootsFinset (by omega),hM,pow_mul,(mem_nthRootsFinset (by decide) _).mp hx]
      have hfil : (A.filter fun x => x^3=t)=nthRootsFinset 3 t := by
        ext x
        rw [mem_filter,mem_nthRootsFinset (by decide)]
        exact ⟨And.right, fun hx => ⟨hsub ((mem_nthRootsFinset (by decide) _).mpr hx),hx⟩⟩
      rw [hfil]
      exact (full_power_fiber (by decide) h₂ h.1 h.2.1).1
    change A.card = ∑ t ∈ T, (A.filter fun x => x^3=t).card at hsum
    rw [sum_congr rfl eq,hAc] at hsum
    simp at hsum
    omega
  let V := Lagrange.nodal D id
  refine ⟨D,hD,fun x hx => hAD ((ha x).mpr hx),fun i => ((V*X^3) /ₘ X^(e+3)).eval i.val,fun i => -(V /ₘ X^(e+3)).eval i.val,?_⟩
  apply hcount.ge.trans
  apply card_le_card
  intro t ht'
  have h := ht t ht'
  exact mem_filter.mpr ⟨mem_univ _,event_of_two_fibers D e L he hM hD t h₁ h₂ h.1 h.2.1
    (h.2.2.trans hAD)⟩

open Classical in
/-- Three distinct nonzero M-th power values supply exactly M bad cube labels
in a rate-half domain extended from their three complete power fibers. -/
theorem three_cosets (e L : ℕ) (he : 2≤e) (hM : e+3=3*L) {g₁ g₂ : K}
    (h₁ : IsPrimitiveRoot g₁ (e+3)) (h₂ : IsPrimitiveRoot g₂ 3)
    (I : Finset K) (hI : I.card=3) (hpow : ∀ c ∈ I, c≠0 ∧ ∃ x : K, x^(e+3)=c)
    (hroom : 3*(e+3) ≤ 4*(e+1)) (hfield : 4*(e+1) ≤ Fintype.card K) :
    ∃ D : Finset K, D.card=4*(e+1) ∧
      ∃ u v : D → K, e+3 ≤ (univ.filter fun t : K => _root_.ProximityGap.mcaEvent
        (ReedSolomon.code (Function.Embedding.subtype (·∈D)) (2*(e+1)) : Set (D → K))
        ((e:ℝ≥0)/D.card) u v t).card := by
  obtain ⟨D,hD,_,hw⟩ := three_cosets_with_sites e L he hM h₁ h₂ I hI hpow hroom hfield
  exact ⟨D,hD,hw⟩

local instance : Fact (Nat.Prime productionPrime) := ⟨productionPrime_prime⟩

open Classical in
/-- The fixed length and dimension over the certified prime field admit a
single received pair with at least 268435458 distinct bad scalars. -/
theorem production_lower_noncoset :
    ∃ D : Finset (ZMod productionPrime), D.card=2^30 ∧
      (¬ ∃ c : ZMod productionPrime, ∀ x∈D, x^(2^30)=c) ∧
      ∃ u v : D → ZMod productionPrime, 268435458 ≤
        (univ.filter fun t : ZMod productionPrime => _root_.ProximityGap.mcaEvent
          (ReedSolomon.code (Function.Embedding.subtype (·∈D)) (2^29) : Set (D → ZMod productionPrime))
          ((268435455:ℝ≥0)/D.card) u v t).card := by
  classical
  obtain ⟨z,hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod productionPrime)ˣ)
  have hg : IsPrimitiveRoot (z : ZMod productionPrime) (productionPrime-1) :=
    IsPrimitiveRoot.coe_units_iff.mpr <| IsPrimitiveRoot.iff_orderOf.mpr <| by
      simpa only [Nat.card_eq_fintype_card,ZMod.card_units] using hz
  let g := (z : ZMod productionPrime)^((productionPrime-1)/268435458)
  have h₁ : IsPrimitiveRoot g 268435458 :=
    hg.pow_of_dvd (p:=(productionPrime-1)/268435458) (by decide) (by decide)
  have h₂ : IsPrimitiveRoot (g^89478486) 3 := h₁.pow_of_dvd (by decide) (by decide)
  let a := (2 : ZMod productionPrime)^268435458
  let b := (4 : ZMod productionPrime)^268435458
  have hab : a ≠ b := by
    dsimp only [a,b]
    simp only [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]
    decide
  have ha : a≠1 := production_cosets.1
  have hb : b≠1 := by
    dsimp only [b]
    rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]
    decide
  let I : Finset (ZMod productionPrime) := {1,a,b}
  have hc : I.card=3 := by simp [I,ha.symm,hb.symm,hab]
  have hpow : ∀ c ∈ I, c≠0 ∧ ∃ x : ZMod productionPrime, x^268435458=c := by
    intro c hc
    simp only [I,mem_insert,mem_singleton] at hc
    rcases hc with rfl|rfl|rfl
    · exact ⟨one_ne_zero,1,one_pow _⟩
    · exact ⟨pow_ne_zero _ (by decide),2,rfl⟩
    · exact ⟨pow_ne_zero _ (by decide),4,rfl⟩
  obtain ⟨D,hD,hs,hw⟩ := three_cosets_with_sites 268435455 89478486 (by decide) (by decide) h₁ h₂ I hc hpow
    (by decide) (by rw [ZMod.card]; decide)

  refine ⟨D,hD,?_,hw⟩
  rintro ⟨c,hc⟩
  have h1 : (1 : ZMod productionPrime) ∈ I := by simp [I]
  have h1D := hs 1 (by simpa only [one_pow] using h1)
  have hroot : (g^89478486)^268435458 = 1 := (h₂.pow_eq_one_iff_dvd _).mpr (by decide)
  have hDroot := hs (g^89478486) (by change (g^89478486)^268435458 ∈ I; rw [hroot]; exact h1)
  have hc1 : (1 : ZMod productionPrime)=c := by simpa only [one_pow] using hc 1 h1D
  exact (by decide : ¬3 ∣ 2^30) (h₂.dvd_of_pow_eq_one _ ((hc _ hDroot).trans hc1.symm))

open Classical in
/-- The fixed length and dimension over the certified prime field admit a
single received pair with at least 268435458 distinct bad scalars. -/
theorem production_lower :
    ∃ D : Finset (ZMod productionPrime), D.card=2^30 ∧
      ∃ u v : D → ZMod productionPrime, 268435458 ≤
        (univ.filter fun t : ZMod productionPrime => _root_.ProximityGap.mcaEvent
          (ReedSolomon.code (Function.Embedding.subtype (·∈D)) (2^29) : Set (D → ZMod productionPrime))
          ((268435455:ℝ≥0)/D.card) u v t).card := by
  obtain ⟨D,hD,_,hw⟩ := production_lower_noncoset
  exact ⟨D,hD,hw⟩

#print axioms production_lower_noncoset
#print axioms production_lower
#print axioms three_cosets
end ArkLib.ProximityGap.Frontier.CubicApolarAttainment
