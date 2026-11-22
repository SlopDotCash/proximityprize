/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.RatioProductNorm
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSliceTransfer
import Mathlib.Data.Fin.Tuple.Reflection

/-! # Six cross-ratio rows suffice for every smooth dyadic subgroup of order 128 -/

namespace ProximityGap.TwoErrorSlice

open Finset

/-- The representatives under multiplication of the exponent difference by a
unit modulo 128, excluding the zero difference and the antipodal pair. -/
def StandardRow (d : Fin 128) : Prop := d=1 ∨ d=2 ∨ d=4 ∨ d=8 ∨ d=16 ∨ d=32

private theorem normalize_differences : ∀ d : Fin 128, d≠0 → d≠64 →
    ∃ b : Fin 128, Nat.Coprime b.val 128 ∧ StandardRow (b*d) := by
  unfold StandardRow
  decide +kernel

private theorem power_add {F : Type*} [Field F] {z : F} (hz : IsPrimitiveRoot z 128)
    (a b : Fin 128) : z^((a+b : Fin 128) : ℕ)=z^(a : ℕ)*z^(b : ℕ) := by
  rw [Fin.val_add, ← pow_add]
  simpa only [← hz.eq_orderOf] using pow_mod_orderOf z (a.val+b.val)

private theorem power_mul {F : Type*} [Field F] {z : F} (hz : IsPrimitiveRoot z 128)
    (a b : Fin 128) : z^((a*b : Fin 128) : ℕ)=(z^(a : ℕ))^(b : ℕ) := by
  change z^((a.val*b.val)%128)=_
  rw [← pow_mul]
  simpa only [← hz.eq_orderOf] using pow_mod_orderOf z (a.val*b.val)

private theorem shift_den {F : Type*} [Field F] {z : F} (hz : IsPrimitiveRoot z 128)
    (u v i : Fin 128) (h : i ≠ v) :
    z^((i-u : Fin 128) : ℕ) ≠ z^((v-u : Fin 128) : ℕ) := by
  intro he
  have eq : i-u=v-u := Fin.ext (hz.pow_inj (i-u).isLt (v-u).isLt he)
  apply h
  simpa only [sub_add_cancel] using congrArg (·+u) eq

private theorem scale_ratio {F : Type*} [Field F] {c : F} (hc : c ≠ 0) (x v : F) :
    (c-c*x)/(c*v-c*x)=(x-1)/(x-v) := by
  rw [show c-c*x=c*(1-x) by ring,show c*v-c*x=c*(v-x) by ring,
    mul_div_mul_left _ _ hc,← neg_sub x 1, ← neg_sub x v,neg_div_neg_eq]

set_option maxRecDepth 10000
set_option exponentiation.threshold 1000

/-- A separated source pair can be translated to zero and conjugated to one
of the six auxiliary rows. Triple-product equalities lift by the cyclotomic
norm bound and then reduce in the auxiliary field. -/
theorem penaltyBound_of_six {p : ℕ} [Fact p.Prime] [NeZero (128 : ZMod p)]
    {F : Type*} [Field F] [NeZero (128 : F)]
    (D : Fin 128 ↪ ZMod p) (E : Fin 128 ↪ F)
    (z : ZMod p) (w : F) (hz : IsPrimitiveRoot z 128) (hw : IsPrimitiveRoot w 128)
    (hD : ∀ i, D i=z^(i : ℕ)) (hE : ∀ i, E i=w^(i : ℕ))
    (large : 2^448 < p^2) (rows : ∀ d : Fin 128, StandardRow d → RowPenaltyBound E 0 d) :
    PenaltyBound D := by
  classical
  intro u v hne hanti
  let d := v-u
  have shift (i : Fin 128) : D i=z^(u : ℕ)*z^((i-u : Fin 128) : ℕ) := by
    rw [← power_add hz,add_comm u (i-u), sub_add_cancel,hD]
  have hd : d ≠ 0 := sub_ne_zero.mpr hne.symm
  have hd64 : d ≠ 64 := by
    intro he
    have hs : (z^64)^2=1 := by rw [←pow_mul]; exact hz.pow_eq_one
    have hneg : z^64 = -1 := (sq_eq_one_iff.mp hs).resolve_left
      (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
    have hpow := shift v
    change D v=z^u.val*z^d.val at hpow
    rw [he,show ((64:Fin 128):ℕ)=64 by decide,hneg,mul_neg_one] at hpow
    exact hanti (by rw [hpow,hD,neg_neg])
  obtain ⟨b,hcop,hr⟩ := normalize_differences d hd hd64
  let s := w^b.val
  have hs : IsPrimitiveRoot s 128 := hw.pow_of_coprime _ hcop
  let mapSite (i : Fin 128) := b*(i-u)
  have emul (i) : E (mapSite i)=s^((i-u : Fin 128) : ℕ) := by
    rw [hE]; exact power_mul hw b (i-u)
  let e : Fin 128 ↪ Fin 128 := ⟨mapSite,by
    intro i j hij
    have he := congrArg E hij
    rw [emul,emul] at he
    have ha := hs.pow_inj (i-u).isLt (j-u).isLt he
    have eq : i-u=j-u := Fin.ext ha
    simpa only [sub_add_cancel] using congrArg (·+u) eq⟩
  have eu : e u=0 := by change b*(u-u)=0; simp
  have ev : e v=b*d := rfl
  apply rowPenaltyBound_transfer D E e u v _ (by rw [eu,ev]; exact rows _ hr)
  let U := ((univ : Finset (Fin 128)).erase u).erase v
  let ix (i : Fin 128) : ℕ := (i-u).val
  have nz : z^u.val ≠ 0 := pow_ne_zero _ (by
    intro h
    have he := hz.pow_eq_one
    rw [h,zero_pow (by decide : 128 ≠ 0)] at he
    exact zero_ne_one he)
  have rD (i) : ratio D u v i = (z^(ix i)-1)/(z^(ix i)-z^d.val) := by
    unfold ratio
    rw [hD u,shift v,shift i]
    exact scale_ratio nz _ _
  have rE (i) : ratio E (e u) (e v) (e i) = (s^(ix i)-1)/(s^(ix i)-s^d.val) := by
    unfold ratio
    change (E (mapSite u)-E (mapSite i))/(E (mapSite v)-E (mapSite i))=_
    rw [emul,emul,emul,sub_self,Fin.val_zero,pow_zero]
    rw [← neg_sub (s^(ix i)) 1, ← neg_sub (s^(ix i)) (s^d.val),neg_div_neg_eq]
  intro x hx y hy A hA B hB hsame
  obtain ⟨hAs,hAc⟩ := mem_powersetCard.mp hA
  obtain ⟨hBs,hBc⟩ := mem_powersetCard.mp hB
  obtain ⟨a,c,hac,rfl⟩ := card_eq_two.mp hAc
  obtain ⟨f,g,hfg,rfl⟩ := card_eq_two.mp hBc
  let xs : Fin 3 → Fin 128 := ![x,a,c]
  let ys : Fin 3 → Fin 128 := ![y,f,g]
  have hxs (i : Fin 3) : xs i ∈ U := by
    fin_cases i
    · exact hx
    · exact hAs (mem_insert_self ..)
    · exact hAs (mem_insert_of_mem (mem_singleton_self _))
  have hys (i : Fin 3) : ys i ∈ U := by
    fin_cases i
    · exact hy
    · exact hBs (mem_insert_self ..)
    · exact hBs (mem_insert_of_mem (mem_singleton_self _))
  have transfer := RatioProductNorm.transfer (hn := (by decide : 2 < 128)) hz hs d.val
    (fun i => ix (xs i)) (fun i => ix (ys i))
    (fun i => shift_den hz u v (xs i) (mem_erase.mp (hxs i)).1) (fun i => shift_den hz u v (ys i) (mem_erase.mp (hys i)).1)
    (fun i => shift_den hs u v (xs i) (mem_erase.mp (hxs i)).1) (fun i => shift_den hs u v (ys i) (mem_erase.mp (hys i)).1) (by
      simp only [prod_insert (show a ∉ ({c}:Finset (Fin 128)) by simpa using hac),
        prod_insert (show f ∉ ({g}:Finset (Fin 128)) by simpa using hfg),prod_singleton,rD] at hsame
      simpa [RatioProductNorm.profile,Fin.prod_univ_succ,xs,ys,div_mul_div_comm] using hsame) (by
      simpa only [show Nat.totient 128=64 by decide] using large)
  simp only [prod_insert (show a ∉ ({c}:Finset (Fin 128)) by simpa using hac),
    prod_insert (show f ∉ ({g}:Finset (Fin 128)) by simpa using hfg),prod_singleton,rE]
  simpa [RatioProductNorm.profile,Fin.prod_univ_succ,xs,ys,div_mul_div_comm] using transfer

end ProximityGap.TwoErrorSlice

#print axioms ProximityGap.TwoErrorSlice.penaltyBound_of_six
