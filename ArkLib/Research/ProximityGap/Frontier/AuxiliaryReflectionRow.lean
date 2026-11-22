/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AuxiliarySixRows

/-! # The unique ratio product with three representations on the six auxiliary rows -/

namespace ProximityGap.TwoErrorSlice

open Finset

theorem mem_alternatives_iff {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
    {D : I ↪ K} {u v : I} {t : K} {A : Finset I} :
    A ∈ alternatives D u v t ↔ A ∈ ((univ.erase u).erase v).powersetCard 2 ∧
      (∏ x ∈ A,ratio D u v x)=t := by
  classical
  exact mem_filter

end ProximityGap.TwoErrorSlice

namespace ProximityGap.AuxiliaryReflectionRow

open Finset AuxiliaryRatioSlotData AuxiliaryRatioSlotFacts TwoErrorSlice

private theorem key_product {d : ℕ} (hd : Row d) :
    (digit (data d).keys 28 (data d).tripleKey * root.powMod d modulus)%modulus=1 := by
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

private theorem reflection_key {d : ℕ} (hd : Row d) :
    (digit (data d).keys 28 (data d).tripleKey : F) = (domain (site d hd))⁻¹ := by
  have eqn := congrArg (fun n : ℕ => (n:F)) (key_product hd)
  have hx : domain (site d hd) ≠ 0 := pow_ne_zero d (by decide : (root:F)≠0)
  rw [← one_div]
  apply (eq_div_iff hx).mpr
  change _*(root:F)^d=1
  simpa only [ZMod.natCast_mod,Nat.cast_mul,Nat.powMod_def,Nat.cast_pow,
    Nat.cast_one] using eqn

/-- Any nonreflection product on one of the six rows has at most two
representations as an unordered pair of distinct valid sites. -/
theorem six (d : Fin 128) (hd : StandardRow d) (t : F)
    (big : 3 ≤ (alternatives domain 0 d t).card) : t=(domain d)⁻¹ := by
  classical
  have valid : Row d.val := by rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  let facts := AuxiliaryRatioSlotRow.pairTagFacts d.val (data d.val) domain d rfl
    (ratio_eq valid) (pair_injective valid) (pair_tagged valid)
  by_contra h
  have small {A} (hA : A ∈ alternatives domain 0 d t) : facts.tag A < 2 := by
    by_contra! high
    obtain ⟨i,hi,eq⟩ := facts.tagged A (mem_alternatives_iff.mp hA).1 (by omega)
    rw [eq high] at hi
    exact h (((mem_alternatives_iff.mp hA).2).symm.trans (hi.symm.trans (reflection_key valid)))
  have bound : (alternatives domain 0 d t).card ≤ (range 2).card := by
    apply card_le_card_of_injOn facts.tag (fun A hA => mem_range.mpr (small hA))
    intro A ha B hb eq
    exact facts.injective A B (mem_alternatives_iff.mp ha).1 (mem_alternatives_iff.mp hb).1
      ((mem_alternatives_iff.mp ha).2.trans (mem_alternatives_iff.mp hb).2.symm) eq
  simp only [card_range] at bound
  omega

/-- The reflection target on a row with base values u and v pairs each
remaining nonzero site x with uv/x. -/
theorem product_eq_reflection_iff {K : Type*} [Field K] {u v x y : K}
    (huv : u ≠ v) (hv : v ≠ 0) (hx : v ≠ x) (hy : v ≠ y) :
    (u-x)/(v-x)*((u-y)/(v-y)) = u/v ↔ x*y=u*v := by
  rw [div_mul_div_comm,div_eq_div_iff (mul_ne_zero (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hy)) hv]
  have hh : v-u ≠ 0 := sub_ne_zero.mpr huv.symm
  constructor
  · intro he
    have hzero : (v-u)*(x*y-u*v)=0 := by linear_combination he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hh)
  · intro he
    linear_combination (v-u)*he

end ProximityGap.AuxiliaryReflectionRow

#print axioms ProximityGap.AuxiliaryReflectionRow.six
#print axioms ProximityGap.AuxiliaryReflectionRow.product_eq_reflection_iff
