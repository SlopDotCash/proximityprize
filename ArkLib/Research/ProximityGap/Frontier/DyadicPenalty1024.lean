/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSlice
import ArkLib.Research.ProximityGap.Frontier.DyadicLogWitness237

/-! # A length-1024 obstruction to the twelve-unit pair penalty -/
namespace ProximityGap.DyadicPenalty1024

open Finset TwoErrorSlice ArkLib.ProximityGap.Frontier.DyadicLogWitness237
open ArkLib.ProximityGap.BinaryPower

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

abbrev site := Fin 1024
def D : site ↪ ZMod P :=
  ⟨fun i => g^(i : ℕ),fun i j h => Fin.ext (primitive.pow_inj i.isLt j.isLt h)⟩

private abbrev mu : ℕ := 17604020721808435999692346832441341307636863595387200509242956284148962

def scale : ZMod P := (mu : ZMod P)

private def rows : Fin 13 → site × site × site × site × site := ![
  (9,7,18,14,521), (14,2,18,9,521), (17,18,1023,529,1006), (18,1,15,2,14),
  (20,18,1020,36,510), (34,18,1006,527,545), (36,18,1004,20,510), (510,18,530,20,36),
  (521,9,14,18,519), (527,18,513,34,545), (529,17,1006,18,511),
  (545,18,495,34,527), (1006,17,529,18,34)]

private def cleared (x a b : site) : Prop :=
  (D x-1)*(D a-1)*(D b-1) = scale*((D x-D 16)*(D a-D 16)*(D b-D 16))

private abbrev generator : ℕ :=
  50329493603183882829305332600678170099788838530533491465177960535524808

private def residue (i : site) := generator.powMod i.val P

private def numerator (i : site) := P+residue i-1
private def denominator (i : site) := P+residue i-residue 16

private def numeric (x a b : site) : Bool :=
  ((numerator x*numerator a*numerator b)%P ==
    (mu*(denominator x*denominator a*denominator b))%P)

private theorem numericKeys : ∀ j : Fin 13,
    let r := rows j
    numeric r.1 r.2.1 r.2.2.1 && numeric r.1 r.2.2.2.1 r.2.2.2.2 = true := by
  decide +kernel

private theorem sound {x a b : site} (h : numeric x a b=true) : cleared x a b := by
  have coe (i : site) : (residue i : ZMod P) = D i := by
    simp only [residue,Nat.powMod_def,ZMod.natCast_mod,Nat.cast_pow]
    rfl
  have num (i : site) : (numerator i : ZMod P)=D i-1 := by
    have hp : 1 ≤ P := by decide
    simp only [numerator,Nat.cast_sub (show 1 ≤ P+residue i by omega),
      Nat.cast_add,ZMod.natCast_self,zero_add,Nat.cast_one,coe]
  have den (i : site) : (denominator i : ZMod P)=D i-D 16 := by
    have hle : residue 16 < P := by
      rw [residue,Nat.powMod_def]
      exact Nat.mod_lt _ (by decide)
    simp only [denominator,Nat.cast_sub (show residue 16 ≤ P+residue i by omega),
      Nat.cast_add,ZMod.natCast_self,zero_add,coe]
  unfold numeric at h
  have eqn := congrArg (fun t : ℕ => (t:ZMod P)) (beq_iff_eq.mp h)
  simpa only [ZMod.natCast_mod,Nat.cast_mul,num,den,cleared,scale] using eqn

private theorem keys (j : Fin 13) :
    let r := rows j
    cleared r.1 r.2.1 r.2.2.1 ∧ cleared r.1 r.2.2.2.1 r.2.2.2.2 := by
  have both := numericKeys j
  rw [Bool.and_eq_true] at both
  exact ⟨sound both.1,sound both.2⟩

private def valid (x : site) : Prop := x≠0 ∧ x≠16

private theorem geometry : ∀ j : Fin 13, let r := rows j
    valid r.1 ∧ valid r.2.1 ∧ valid r.2.2.1 ∧ valid r.2.2.2.1 ∧ valid r.2.2.2.2 ∧
    r.2.1 ≠ r.2.2.1 ∧ r.2.2.2.1 ≠ r.2.2.2.2 ∧
    r.2.1 ≠ r.2.2.2.1 ∧ r.2.1 ≠ r.2.2.2.2 := by
  unfold valid
  decide +kernel

private theorem pair_mem {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
    (E : I ↪ K) (u v x a b : I) (t : K)
    (hx : x≠u ∧ x≠v) (ha : a≠u ∧ a≠v) (hb : b≠u ∧ b≠v) (hab : a≠b)
    (h : (E x-E u)*(E a-E u)*(E b-E u) =
      t*((E x-E v)*(E a-E v)*(E b-E v))) :
    {a,b} ∈ alternatives E u v (t / ratio E u v x) := by
  classical
  have den {i : I} (hi : i≠v) : E i-E v ≠ 0 := sub_ne_zero.mpr (E.injective.ne hi)
  have nf := ratio_ne_zero E hx.1.symm hx.2.symm
  have ratio' (y : I) : ratio E u v y = (E y-E u)/(E y-E v) := by
    unfold ratio
    rw [← neg_sub (E y) (E u), ← neg_sub (E y) (E v),neg_div_neg_eq]
  apply mem_filter.mpr
  refine ⟨mem_powersetCard.mpr ⟨?_,by simp [hab]⟩, ?_⟩
  · intro y hy
    simp only [mem_erase,mem_univ,and_true]
    rcases mem_insert.mp hy with rfl | h
    · exact ⟨ha.2,ha.1⟩
    · obtain rfl := mem_singleton.mp h
      exact ⟨hb.2,hb.1⟩
  · rw [prod_insert (show a ∉ ({b}:Finset I) by simpa using hab),prod_singleton]
    apply (eq_div_iff nf).mpr
    simp only [ratio']
    field_simp [den hx.2,den ha.2,den hb.2]
    linear_combination h

private theorem alternative {x a b : site} (hx : valid x) (ha : valid a) (hb : valid b)
    (hab : a ≠ b) (h : cleared x a b) :
    {a,b} ∈ alternatives D 0 16 (scale / ratio D 0 16 x) := by
  apply pair_mem D 0 16 x a b scale hx ha hb hab
  rw [show D 0=1 by rfl]
  exact h

/-- At the specified separation and scale, thirteen distinct tested sites
contribute at least fifteen penalty units. -/
theorem penalty_ge_fifteen :
    15 ≤ ∑ x ∈ (univ.erase (0:site)).erase 16,
      penalty (alternatives D 0 16 (scale/ratio D 0 16 x)).card := by
  classical
  let f (x : site) := penalty (alternatives D 0 16 (scale/ratio D 0 16 x)).card
  let s := (univ : Finset (Fin 13)).image fun j => (rows j).1
  have hinj : Function.Injective (fun j => (rows j).1) := by decide +kernel
  have hs : s.card=13 := by simp [s,card_image_of_injective _ hinj]
  have sub : s ⊆ (univ.erase (0:site)).erase 16 := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    simp only [mem_erase,mem_univ,and_true]
    exact ⟨(geometry i).1.2,(geometry i).1.1⟩
  have lower (x) (hx : x∈s) : 1 ≤ f x := by
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨hx,ha,hb,hc,hd,hab,hcd,hac,had⟩ := geometry i
    obtain ⟨hk,hl⟩ := keys i
    have hcard := card_le_card (insert_subset_iff.mpr
      ⟨alternative hx ha hb hab hk,singleton_subset_iff.mpr (alternative hx hc hd hcd hl)⟩)
    have hne : ({(rows i).2.1,(rows i).2.2.1} : Finset site) ≠ {(rows i).2.2.2.1,(rows i).2.2.2.2} := by
      intro he
      have hmem : (rows i).2.1 ∈ ({(rows i).2.2.2.1,(rows i).2.2.2.2} : Finset site) := he ▸ mem_insert_self _ _
      simp [hac,had] at hmem
    rw [card_pair hne] at hcard
    dsimp [f,penalty]
    split_ifs <;> omega
  have heavy : 3 ≤ f 18 := by
    let A : Finset (Finset site) := {{1,15},{2,14},{3,13}}
    have hA : A.card=3 := by decide
    have inc : A ⊆ alternatives D 0 16 (scale/ratio D 0 16 18) := by
      intro q hq
      simp only [A,mem_insert,mem_singleton] at hq
      rcases hq with rfl|rfl|rfl
      all_goals
        exact alternative (by unfold valid; decide) (by unfold valid; decide)
          (by unfold valid; decide) (by decide) (sound (by decide +kernel))
    have hc : 3 ≤ (alternatives D 0 16 (scale/ratio D 0 16 18)).card := hA ▸ card_le_card inc
    dsimp [f,penalty]
    split_ifs <;> omega
  have mem : 18 ∈ s := mem_image.mpr ⟨3,mem_univ _,by decide⟩
  have n12 : (s.erase 18).card=12 := by rw [card_erase_of_mem mem,hs]
  have uniform := sum_le_sum (s := s.erase 18) (fun k hk => lower k (mem_of_mem_erase hk))
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_one,n12] at uniform
  have hsum := sum_erase_add _ f mem
  have full := sum_le_sum_of_subset_of_nonneg (f := f) sub (fun _ _ _ => Nat.zero_le _)
  change 15 ≤ ∑ x ∈ (univ.erase (0:site)).erase 16, f x
  omega

/-- The 128-site twelve-unit row bound fails on the larger subgroup of the same field. -/
theorem fails : ¬PenaltyBound D := by
  intro safe
  have hn : D 0 ≠ -D 16 := by
    change g^0 ≠ -(g^16)
    simp only [← binaryPow_eq_pow]; decide
  have upper := safe 0 16 (by decide) hn scale (by decide)
  exact (by decide : ¬15 ≤ 12) (penalty_ge_fifteen.trans upper)

end ProximityGap.DyadicPenalty1024

#print axioms ProximityGap.DyadicPenalty1024.fails
