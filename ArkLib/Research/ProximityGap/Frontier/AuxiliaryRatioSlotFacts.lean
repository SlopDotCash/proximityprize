/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AuxiliaryRatioSlotChecks
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSlice
import ArkLib.Research.ProximityGap.Support.BinaryPower
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Ordered slots, finite fibers and the auxiliary evaluation field -/
set_option autoImplicit false
namespace ProximityGap.AuxiliaryRatioSlotFacts
open AuxiliaryRatioSlotData
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)

abbrev Row (d : ℕ) := d=1 ∨ d=2 ∨ d=4 ∨ d=8 ∨ d=16 ∨ d=32
abbrev F := ZMod modulus

private theorem prime : Nat.Prime modulus := by
  apply lucas_primality modulus 3 (by rw [← binaryPow_eq_pow]; decide)
  intro q hq divides
  rw [show modulus-1=2^25*5 by decide] at divides
  rcases hq.dvd_mul.mp divides with h | h
  · have eqn := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    subst q
    rw [← binaryPow_eq_pow]
    decide
  · have eqn := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 5)).mp h
    subst q
    rw [← binaryPow_eq_pow]
    decide

instance : Fact modulus.Prime := ⟨prime⟩

theorem primitive : IsPrimitiveRoot (root : F) 128 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  exact orderOf_eq_prime_pow (p:=2) (n:=6) (by decide) (by decide)

def domain : Fin 128 ↪ F :=
  ⟨fun i => (root:F)^i.val,fun i j eqn => Fin.ext (primitive.pow_inj i.isLt j.isLt eqn)⟩

def site (d : ℕ) (hd : Row d) : Fin 128 := ⟨d,by rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;> decide⟩

private theorem small {d : ℕ} (hd : Row d) : (data d).heavyCount ≤ 190 ∧ (data d).tripleKey<(data d).heavyCount := by
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

theorem big_lt {d : ℕ} (hd : Row d) : (data d).tripleKey < (data d).heavyCount := (small hd).2

private theorem clauses {d i : ℕ} (hd : Row d) (hi : i<24576) :
    let a := data d
    let x := root.powMod i modulus
    let v := root.powMod d modulus
    (128 ≤ i ∨ validSite d i=false ∨ digit a.ratios 28 i < modulus ∧
       digit a.ratios 28 i * (modulus+v-x) % modulus = (modulus+1-x)%modulus) ∧
    (a.heavyCount ≤ i ∨ digit a.keys 28 i < modulus) ∧
    (a.heavyCount ≤ i+1 ∨ digit a.keys 28 i < digit a.keys 28 (i+1)) ∧
    (16384 ≤ i ∨ checkPair a d i=true) ∧ (7875 ≤ i+1 ∨ checkPairOrder a i=true) ∧
    ((a.heavyCount+2)*128 ≤ i ∨ checkCharge a d i=true) ∧
    ((a.heavyCount+2)*126 ≤ i+1 ∨ checkChargeOrder a i=true) := by
  have all := checked hd hi
  simpa only [checkAt,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',decide_eq_true_eq,
    beq_iff_eq,and_assoc,or_assoc] using all

private theorem on_fin {n : ℕ} (f : ℕ → ℕ) (steps : ∀ i, i+1<n → f i<f (i+1)) :
    StrictMono (fun i : Fin n => f i) := by
  cases n with
  | zero => exact fun i => Fin.elim0 i
  | succ n => exact Fin.strictMono_iff_lt_succ.mpr (fun i => steps i (by omega))

/-- Ordered integer keys within the field range are distinct as field elements. -/
theorem key_lt {d : ℕ} (hd : Row d) (i : Fin (data d).heavyCount) : digit (data d).keys 28 i < modulus := by
  have hs := (small hd).1
  exact (clauses hd (by omega : i.val<24576)).2.1.resolve_left (by omega)

theorem key_injective {d : ℕ} (hd : Row d) :
    Function.Injective (fun i : Fin (data d).heavyCount => digit (data d).keys 28 i) := by
  apply (on_fin _ _).injective
  intro i hi
  have hs := (small hd).1
  exact (clauses hd (by omega : i<24576)).2.2.1.resolve_left (by omega)

theorem ratio_eq {d : ℕ} (hd : Row d) (x : Fin 128) (hx : validSite d x=true) :
    TwoErrorSlice.ratio domain 0 (site d hd) x = (digit (data d).ratios 28 x : F) := by
  have lt := x.isLt
  have h := (clauses hd (by omega : x.val<24576)).1.resolve_left (by omega)
  have val := (h.resolve_left (by simp [hx])).2
  have denom : (root:F)^d-(root:F)^x.val ≠ 0 := by
    apply sub_ne_zero.mpr
    exact fun eqn => (by simpa [validSite] using hx : 0<x.val ∧ x.val<128 ∧ x.val≠d).2.2
      (primitive.pow_inj x.isLt (site d hd).isLt eqn.symm)
  have bound : root.powMod x.val modulus < modulus := by
    rw [Nat.powMod_def]
    exact Nat.mod_lt _ (by decide)
  have cast : ∀ j, ((root.powMod j modulus:ℕ):F)=(root:F)^j := by
    intro j
    rw [Nat.powMod_def,ZMod.natCast_mod,Nat.cast_pow]
  have eqF := congrArg (fun a : ℕ => (a:F)) val
  rw [ZMod.natCast_mod,ZMod.natCast_mod,Nat.cast_mul,Nat.cast_sub (by omega),
    Nat.cast_sub (by omega)] at eqF
  simp only [Nat.cast_add,ZMod.natCast_self,zero_add,Nat.cast_one,cast] at eqF
  change ((root:F)^0-(root:F)^x.val)/((root:F)^d-(root:F)^x.val)=_
  rw [pow_zero,div_eq_iff denom]
  exact eqF.symm

private theorem pair_valid {d id : ℕ} (hd : Row d) (hi : validPair d id=true) :
    let a := data d
    let r := digit a.pairRanks 13 id
    r<7875 ∧ digit a.pairOrder 14 r=id ∧
      (digit a.pairTags 6 id=0 ∨ digit a.pairKeys 8 id<a.heavyCount ∧
       digit a.keys 28 (digit a.pairKeys 8 id)=pairValue a id ∧
       (digit a.pairTags 6 id=1 ∨ digit a.pairKeys 8 id=a.tripleKey)) := by
  have range : id<16384 := by
    simp only [validPair,validSite,Bool.and_eq_true,decide_eq_true_eq] at hi
    omega
  have h := (clauses hd (by omega : id<24576)).2.2.2.1.resolve_left (by omega)
  simpa only [checkPair,hi,Bool.not_true,Bool.false_or,Bool.and_eq_true,Bool.or_eq_true,
    decide_eq_true_eq,beq_iff_eq,and_assoc] using h

/-- Every positive tag is charged to a stored heavy key. -/
theorem pair_tagged {d id : ℕ} (hd : Row d) (valid : validPair d id=true)
    (pos : 1 ≤ digit (data d).pairTags 6 id) :
    let a := data d
    let h := digit a.pairKeys 8 id
    h<a.heavyCount ∧ digit a.keys 28 h=pairValue a id ∧ (2 ≤ digit a.pairTags 6 id → h=a.tripleKey) := by
  obtain ⟨_,_,h⟩ := pair_valid hd valid
  rcases h with hz | ⟨hb,he,ha⟩
  · omega
  · exact ⟨hb,he,fun big => ha.resolve_left (by omega)⟩

private theorem inject_on {S : Set ℕ} {N : ℕ} (code order rank : ℕ → ℕ)
    (bounds : ∀ i∈S, rank i<N ∧ order (rank i)=i)
    (steps : ∀ j, j+1<N → code (order j)<code (order (j+1))) : Set.InjOn code S := by
  intro i hi k hk eqn
  obtain ⟨ib,invI⟩ := bounds i hi
  obtain ⟨kb,invK⟩ := bounds k hk
  have eqRank := (on_fin _ steps).injective (a₁:=⟨rank i,ib⟩) (a₂:=⟨rank k,kb⟩)
    (by simpa only [invI,invK] using eqn)
  rw [←invI,←invK]
  exact congrArg order (congrArg Fin.val eqRank)

/-- No two different pair indices have the same product and tag. -/
theorem pair_injective {d : ℕ} (hd : Row d) :
    Set.InjOn (pairCode (data d)) {id | validPair d id=true} := by
  apply inject_on (N:=7875) _ (digit (data d).pairOrder 14) (digit (data d).pairRanks 13)
  · intro i hi
    obtain ⟨ub,he,_⟩ := pair_valid hd hi
    exact ⟨ub,he⟩
  · intro j hj
    exact of_decide_eq_true ((clauses hd (by omega : j<24576)).2.2.2.2.1.resolve_left (by omega))

private theorem charge_valid {d id : ℕ} (hd : Row d) (bound : id<((data d).heavyCount+2)*128)
    (valid : validSite d (id%128)=true) :
    let a := data d
    let r := digit a.chargeRanks 15 id
    r<(a.heavyCount+2)*126 ∧ digit a.chargeOrder 15 r=id ∧ digit a.chargeTags 4 id<12 := by
  have hs := (small hd).1
  have h := (clauses hd (by omega : id<24576)).2.2.2.2.2.1.resolve_left (by omega)
  simpa only [checkCharge,valid,Bool.not_true,Bool.false_or,Bool.and_eq_true,decide_eq_true_eq,
    beq_iff_eq,and_assoc] using h

theorem charge_tag_lt {d id : ℕ} (hd : Row d) (bound : id<((data d).heavyCount+2)*128)
    (valid : validSite d (id%128)=true) : digit (data d).chargeTags 4 id<12 :=
  (charge_valid hd bound valid).2.2

/-- Two different charge records with the same scale have distinct tags. -/
theorem charge_injective {d : ℕ} (hd : Row d) :
    Set.InjOn (chargeCode (data d)) {id | id<((data d).heavyCount+2)*128 ∧ validSite d (id%128)=true} := by
  apply inject_on (N:=((data d).heavyCount+2)*126) _
    (digit (data d).chargeOrder 15) (digit (data d).chargeRanks 15)
  · rintro i ⟨bound,valid⟩
    exact ⟨(charge_valid hd bound valid).1,(charge_valid hd bound valid).2.1⟩
  · intro j hj
    have hs := (small hd).1
    exact of_decide_eq_true ((clauses hd (by omega : j<24576)).2.2.2.2.2.2.resolve_left (by omega))

end ProximityGap.AuxiliaryRatioSlotFacts
#print axioms ProximityGap.AuxiliaryRatioSlotFacts.key_injective
#print axioms ProximityGap.AuxiliaryRatioSlotFacts.pair_injective
#print axioms ProximityGap.AuxiliaryRatioSlotFacts.charge_injective
