/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence
import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic

/-! # Field characteristics on a smooth domain of length two to the thirtieth

An order-`2^30` subgroup in a field of order `p^e < 2^160` forces `e ≤ 5`.
The two-adic lifting-the-exponent identity bounds the order of `p` modulo
`2^30`. The resulting lower bound for `p` is incompatible with the field-size
bound for every extension degree at least six. -/

namespace ArkLib.ProximityGap.Frontier.SmoothCubicCharacteristic

/-- A high power of two dividing the multiplicative group forces the
characteristic close to a multiple of a high power of two. -/
private theorem base_bound {p e a v : ℕ} (hp : 2 ≤ p) (ho : ¬2 ∣ p) (he : 0 < e)
    (hd : 2 ^ 30 ∣ p ^ e - 1) (hv : padicValNat 2 (e + e) ≤ v) (ha : a + v ≤ 30) :
    2 ^ a ≤ p + 1 := by
  have hdouble : e ∣ e + e := dvd_add dvd_rfl dvd_rfl
  have hd' := hd.trans (Nat.pow_sub_one_dvd_pow_sub_one p hdouble)
  have hn : p ^ (e + e) - 1 ≠ 0 := by
    have hx := Nat.one_lt_pow (show e + e ≠ 0 by omega) (show 1 < p by omega)
    omega
  have hbig := (Nat.pow_dvd_iff_le_padicValNat (by decide : 2 ≠ 1) hn).mp hd'
  have hLTE := padicValNat.pow_two_sub_one (by omega : 1 < p) ho
    (by omega : e + e ≠ 0) (show Even (e + e) from ⟨e, rfl⟩)
  have hm : p - 1 ≠ 0 := by omega
  have hs : p + 1 ≠ 0 := by omega
  have hlow : padicValNat 2 (p - 1) ≤ 1 ∨ padicValNat 2 (p + 1) ≤ 1 := by
    by_contra! h
    have h1 := (Nat.pow_dvd_iff_le_padicValNat (by decide : 2 ≠ 1) hm).mpr h.1
    have h2 := (Nat.pow_dvd_iff_le_padicValNat (by decide : 2 ≠ 1) hs).mpr h.2
    change 4 ∣ p - 1 at h1
    change 4 ∣ p + 1 at h2
    omega
  rcases hlow with h | h
  · exact Nat.le_of_dvd (by omega) ((Nat.pow_dvd_iff_le_padicValNat (by decide : 2 ≠ 1) hs).mpr
      (by omega : a ≤ padicValNat 2 (p + 1)))
  · have hd' := (Nat.pow_dvd_iff_le_padicValNat (by decide : 2 ≠ 1) hm).mpr
      (by omega : a ≤ padicValNat 2 (p - 1))
    exact (Nat.le_of_dvd (by omega) hd').trans (by omega)

/-- Every prime power below `2^160` that admits a multiplicative domain of
order `2^30` has extension degree at most five. -/
theorem degree_le_five {p e : ℕ} (hp : p.Prime) (he : 0 < e) (hd : 2 ^ 30 ∣ p ^ e - 1)
    (hq : p ^ e < 2 ^ 160) : e ≤ 5 := by
  have hp2 := hp.two_le
  have hn : p ≠ 2 := by
    rintro rfl
    have hpar := dvd_pow_self 2 he.ne'
    have hprev := dvd_trans (by decide : 2 ∣ 2 ^ 30) hd
    have hpos := Nat.pow_pos (by decide : 0 < 2) (n := e)
    omega
  have ho : ¬2 ∣ p := fun h => hn (hp.eq_one_or_self_of_dvd 2 h |>.resolve_left (by decide)).symm
  have h100 : e ≤ 100 := by
    by_contra! h
    have hl : 3 ^ 101 ≤ p ^ e :=
      (Nat.pow_le_pow_left (by omega : 3 ≤ p) 101).trans (Nat.pow_le_pow_right hp.pos h)
    omega
  by_contra! h6
  by_cases h : e = 6
  · subst e
    have hlarge := base_bound hp2 ho (by decide : 0 < 6) hd
      (show padicValNat 2 (6 + 6) ≤ 2 by
        by_contra! hval
        exact (by decide : ¬2 ^ 3 ∣ 6 + 6)
          ((Nat.pow_dvd_iff_le_padicValNat (by decide) (by decide)).mpr hval))
      (by decide : 28 + 2 ≤ 30)
    have : (2 ^ 28 - 1) ^ 6 ≤ p ^ 6 := Nat.pow_le_pow_left (by omega) 6
    omega
  · have hv : padicValNat 2 (e + e) ≤ 7 := by
      by_contra! hh
      have hdvd := (Nat.pow_dvd_iff_le_padicValNat (by decide : 2 ≠ 1)
        (by omega : e + e ≠ 0)).mpr hh
      have := Nat.le_of_dvd (by omega : 0 < e + e) hdvd
      omega
    have hlarge := base_bound hp2 ho he hd hv (by decide : 23 + 7 ≤ 30)
    have hbound : (2 ^ 23 - 1) ^ 7 ≤ p ^ e :=
      (Nat.pow_le_pow_left (by omega) 7).trans (Nat.pow_le_pow_right hp.pos (by omega))
    omega

/-- On every smooth length-`2^30` domain, the field order alone implies the
characteristic cutoff throughout the interval `1744830589^5 < q < 2^160`. -/
theorem characteristic {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I]
    (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 2 ^ 30)
    (hl : 1744830589 ^ 5 < Fintype.card F) (hu : Fintype.card F < 2 ^ 160) :
    1744830589 < ringChar F := by
  classical
  obtain ⟨equiv, _⟩ := _root_.ProximityGap.SmoothDomainMcaEquivalence.coset_equiv D
  let H := ReedSolomon.Smooth.H D
  let _ : Fintype H := Fintype.ofEquiv I equiv
  have hd : 2 ^ 30 ∣ Fintype.card F - 1 := by
    rw [← hn, Fintype.card_congr equiv]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using
      Subgroup.card_subgroup_dvd_card H
  obtain ⟨e, hp, hq⟩ := FiniteField.card F (ringChar F)
  rw [hq] at hd hl hu
  have he := degree_le_five hp e.pos hd hu
  by_contra! hc
  exact (not_lt_of_ge ((Nat.pow_le_pow_right hp.pos he).trans (Nat.pow_le_pow_left hc 5))) hl

end ArkLib.ProximityGap.Frontier.SmoothCubicCharacteristic
