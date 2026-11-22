/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AuxiliaryRatioSlotData
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSliceSlots
import Mathlib.Algebra.Field.ZMod

/-! # Turning certified integer archive tags into a finite-field row bound -/

namespace ProximityGap.AuxiliaryRatioSlotRow
open Finset AuxiliaryRatioSlotData TwoErrorSlice

private abbrev I := Fin 128
private abbrev K := ZMod modulus

private def lo (A : Finset I) : I := if h : A.Nonempty then A.min' h else 0
private def hi (A : Finset I) : I := if h : A.Nonempty then A.max' h else 0
private def pairId (A : Finset I) := 128*(lo A).val+(hi A).val

private theorem bounds_pair {A : Finset I} (h : A.card=2) : A={lo A,hi A} ∧ lo A<hi A := by
  obtain ⟨x,y,ne,rfl⟩ := card_eq_two.mp h
  rcases lt_or_gt_of_ne ne with h|h
  · simp [lo,hi,Finset.min'_insert,Finset.max'_insert,min_eq_left h.le,max_eq_right h.le,h]
  · rw [pair_comm x y]
    simp [lo,hi,Finset.min'_insert,Finset.max'_insert,min_eq_left h.le,max_eq_right h.le,h]

private theorem valid_site {d : ℕ} {v x : I} (hv : v.val=d) (hx : x∈(univ.erase 0).erase v) :
    validSite d x=true := by
  obtain ⟨xv,hx⟩ := mem_erase.mp hx
  have nz := (mem_erase.mp hx).1
  have n : x.val≠0 := fun he => nz (Fin.ext he)
  have nd : x.val≠d := fun he => xv (Fin.ext (he.trans hv.symm))
  simp [validSite,show 0<x.val by omega,x.isLt,nd]

private theorem pair_id_inj {A B : Finset I} (ha : A.card=2) (hb : B.card=2)
    (ids : pairId A=pairId B) : A=B := by
  have la := (hi A).isLt
  have lb := (hi B).isLt
  unfold pairId at ids
  have low : lo A=lo B := Fin.ext (by omega)
  have high : hi A=hi B := Fin.ext (by omega)
  exact (bounds_pair ha).1.trans (by rw [low,high,←(bounds_pair hb).1])

private theorem residue_eq {s t : ℕ} (hs : s<modulus) (ht : t<modulus) (eq : (s:K)=(t:K)) :
    s=t := by simpa only [ZMod.val_natCast_of_lt hs,ZMod.val_natCast_of_lt ht] using congrArg ZMod.val eq

private def layer (a : Archive) (i : Fin a.heavyCount) (l : Fin 3) :=
  if l.val=0 then i.val else a.heavyCount+l.val-1

private def chargeId (a : Archive) (i : Fin a.heavyCount) (x : I) (l : Fin 3) :=
  128*layer a i l+x.val

/-- Encoded distinct pairs agreeing in product and rank coincide. A rank of at
least two identifies the unique stored product capable of a third representation. -/
structure PairTagFacts [Fact (Nat.Prime modulus)] (a : Archive) (D : I ↪ K) (v : I) where
  tag : Finset I → ℕ
  injective : ∀ A B : Finset I, A ∈ ((univ.erase 0).erase v).powersetCard 2 →
    B ∈ ((univ.erase 0).erase v).powersetCard 2 →
    (∏ x ∈ A,ratio D 0 v x) = ∏ x ∈ B,ratio D 0 v x → tag A=tag B → A=B
  tagged : ∀ A ∈ ((univ.erase 0).erase v).powersetCard 2, 1≤tag A →
    ∃ i : Fin a.heavyCount, (digit a.keys 28 i : K) = (∏ x ∈ A,ratio D 0 v x) ∧
      (2≤tag A → i.val=a.tripleKey)

/-- Interpret the pair part of the integer archive independently of the
weighted-charge certificate. -/
noncomputable def pairTagFacts [Fact (Nat.Prime modulus)] (d : ℕ) (a : Archive) (D : I ↪ K) (v : I)
    (hv : v.val=d)
    (rat : ∀ x : I, validSite d x=true → ratio D 0 v x=(digit a.ratios 28 x:K))
    (pairInj : Set.InjOn (pairCode a) {id | validPair d id=true})
    (tagged : ∀ {id}, validPair d id=true → 1≤digit a.pairTags 6 id →
      let h := digit a.pairKeys 8 id
      h<a.heavyCount ∧ digit a.keys 28 h=pairValue a id ∧ (2≤digit a.pairTags 6 id → h=a.tripleKey)) :
    PairTagFacts a D v := by
  classical
  let tag (A : Finset I) := digit a.pairTags 6 (pairId A)
  let sites : Finset I := (univ.erase 0).erase v
  have pair {A : Finset I} (hA : A∈sites.powersetCard 2) :
      validPair d (pairId A)=true ∧ (pairValue a (pairId A):K)=∏ x ∈ A,ratio D 0 v x := by
    obtain ⟨sub,size⟩ := mem_powersetCard.mp hA
    obtain ⟨rep,ord⟩ := bounds_pair size
    have elems : ({lo A,hi A} : Finset I)⊆sites := rep ▸ sub
    have hl : lo A∈sites := elems (mem_insert_self ..)
    have hh : hi A∈sites := elems (mem_insert_of_mem (mem_singleton_self _))
    have px : pairId A/128=(lo A).val := by unfold pairId;have := (hi A).isLt;omega
    have py : pairId A%128=(hi A).val := by unfold pairId;have := (hi A).isLt;omega
    refine ⟨by simp [validPair,px,py,valid_site hv hl,valid_site hv hh,show (lo A).val<(hi A).val from ord],?_⟩
    calc
      _ = ratio D 0 v (lo A)*ratio D 0 v (hi A) := by
        rw [rat _ (valid_site hv hl),rat _ (valid_site hv hh)]
        simp [pairValue,px,py,ZMod.natCast_mod]
      _ = _ := by conv_rhs => rw [rep]
                  simp [ord.ne]
  refine ⟨tag,?_,?_⟩
  · intro A B hA hB he ht
    obtain ⟨va,pa⟩ := pair hA
    obtain ⟨vb,pb⟩ := pair hB
    have same := residue_eq (s:=pairValue a (pairId A)) (t:=pairValue a (pairId B))
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (pa.trans (he.trans pb.symm))
    exact pair_id_inj (mem_powersetCard.mp hA).2 (mem_powersetCard.mp hB).2
      (pairInj va vb (by change pairValue a (pairId A)*128+tag A=pairValue a (pairId B)*128+tag B; rw [same,ht]))
  · intro A hA pos
    obtain ⟨valid,prod⟩ := pair hA
    obtain ⟨bound,eq,triple⟩ := tagged valid pos
    exact ⟨⟨_,bound⟩,(congrArg (fun t : ℕ => (t:K)) eq).trans prod,triple⟩

/-- A checked archive supplies all hypotheses of the twelve-slot row bound.
Only entries corresponding to actual unordered pairs or actual charged
key-site-layer triples participate. -/
theorem row_of_facts [Fact (Nat.Prime modulus)] (d : ℕ) (a : Archive) (D : I ↪ K) (v : I)
    (hv : v.val=d)
    (rat : ∀ x : I, validSite d x=true → ratio D 0 v x=(digit a.ratios 28 x:K))
    (keyBound : ∀ i : Fin a.heavyCount, digit a.keys 28 i<modulus)
    (keyInj : Function.Injective (fun i : Fin a.heavyCount => digit a.keys 28 i))
    (pairInj : Set.InjOn (pairCode a) {id | validPair d id=true})
    (tagged : ∀ {id}, validPair d id=true → 1≤digit a.pairTags 6 id →
      let h := digit a.pairKeys 8 id
      h<a.heavyCount ∧ digit a.keys 28 h=pairValue a id ∧ (2≤digit a.pairTags 6 id → h=a.tripleKey))
    (chargeInj : Set.InjOn (chargeCode a) {id | id<(a.heavyCount+2)*128 ∧ validSite d (id%128)=true})
    (tagBound : ∀ {id}, id<(a.heavyCount+2)*128 → validSite d (id%128)=true →
      digit a.chargeTags 4 id<12) : RowPenaltyBound D 0 v := by
  classical
  let key (i : Fin a.heavyCount) : K := digit a.keys 28 i
  let cost (i : Fin a.heavyCount) := if i.val=a.tripleKey then 3 else 1
  let facts := pairTagFacts d a D v hv rat pairInj tagged
  let tag := facts.tag
  let slot (i : Fin a.heavyCount) (x : I) (l : Fin 3) : Fin 12 :=
    ⟨digit a.chargeTags 4 (chargeId a i x l)%12,Nat.mod_lt _ (by decide)⟩
  let sites : Finset I := (univ.erase 0).erase v
  have access {A : Finset I} (hA : A∈sites.powersetCard 2) (pos : 1≤tag A) :
      ∃ i, key i=∏ x ∈ A,ratio D 0 v x ∧ (2≤tag A → cost i=3) := by
    obtain ⟨i,hi,htr⟩ := facts.tagged A hA pos
    exact ⟨i,hi,fun h => by simp [cost,htr h]⟩
  refine rowPenaltyBound_of_pair_tags D 0 v key cost (fun i => by unfold cost;split <;> simp)
    (fun i j eq => keyInj (residue_eq (keyBound i) (keyBound j) eq)) tag ?_ ?_ ?_ slot ?_
  · exact facts.injective
  · intro A ha ht
    obtain ⟨i,he,_⟩ := access ha ht
    exact ⟨i,he⟩
  · intro A ha ht
    obtain ⟨i,he,triple⟩ := access ha (by omega)
    exact ⟨i,he,triple ht⟩
  · intro i x l j y m hx hy hli hmj he ht
    have triple {i : Fin a.heavyCount} {l : Fin 3} (hl : l.val<cost i) (hn : l.val≠0) :
        i.val=a.tripleKey := by dsimp only [cost] at hl;split at hl <;> omega
    have bounds (i : Fin a.heavyCount) (x : I) (l : Fin 3) :
        chargeId a i x l<(a.heavyCount+2)*128 ∧ chargeId a i x l%128=x.val ∧
          chargeId a i x l/128=layer a i l := by
      have hl := l.isLt
      have hi := i.isLt
      have hx := x.isLt
      dsimp only [chargeId,layer]
      split <;> omega
    have valEq (i : Fin a.heavyCount) (x : I) (l : Fin 3) (sx : x∈sites) (hl : l.val<cost i) :
        (chargeValue a (chargeId a i x l):K)=key i * ratio D 0 v x := by
      rw [rat x (valid_site hv sx)]
      unfold chargeValue
      rw [(bounds i x l).2.2,(bounds i x l).2.1,ZMod.natCast_mod,Nat.cast_mul]
      have atKey : (if layer a i l<a.heavyCount then layer a i l else a.tripleKey)=i.val := by
        by_cases zero : l.val=0
        · simp [layer,zero,i.isLt]
        · have big : ¬a.heavyCount+l.val-1<a.heavyCount := by omega
          simp [layer,zero,big,triple hl zero]
      rw [atKey]
    have vx := valid_site hv hx
    have vy := valid_site hv hy
    have bx := bounds i x l
    have by' := bounds j y m
    have vx' : validSite d (chargeId a i x l%128)=true := bx.2.1 ▸ vx
    have vy' : validSite d (chargeId a j y m%128)=true := by'.2.1 ▸ vy
    have eq := residue_eq (s:=chargeValue a (chargeId a i x l)) (t:=chargeValue a (chargeId a j y m))
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) ((valEq i x l hx hli).trans
        (he.trans (valEq j y m hy hmj).symm))
    have tagEq := congrArg Fin.val ht
    change digit a.chargeTags 4 (chargeId a i x l)%12=digit a.chargeTags 4 (chargeId a j y m)%12 at tagEq
    rw [Nat.mod_eq_of_lt (tagBound bx.1 vx'),Nat.mod_eq_of_lt (tagBound by'.1 vy')] at tagEq
    have ids := chargeInj ⟨bx.1,vx'⟩ ⟨by'.1,vy'⟩ (by simp only [chargeCode,eq,tagEq])
    have siteEq : x=y := Fin.ext (bx.2.1.symm.trans ((congrArg (·%128) ids).trans by'.2.1))
    have lays := bx.2.2.symm.trans ((congrArg (·/128) ids).trans by'.2.2)
    by_cases l0 : l.val=0 <;> by_cases m0 : m.val=0
    · exact ⟨Fin.ext (by simpa [layer,l0,m0] using lays),siteEq,Fin.ext (l0.trans m0.symm)⟩
    · simp [layer,l0,m0] at lays
      have := i.isLt
      omega
    · simp [layer,l0,m0] at lays
      have := j.isLt
      omega
    · simp [layer,l0,m0] at lays
      exact ⟨Fin.ext ((triple hli l0).trans (triple hmj m0).symm),siteEq,Fin.ext (by omega)⟩

end ProximityGap.AuxiliaryRatioSlotRow
#print axioms ProximityGap.AuxiliaryRatioSlotRow.row_of_facts
