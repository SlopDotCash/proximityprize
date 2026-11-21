/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence
import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic

/-! # Field characteristics on a smooth domain of length two to the thirtieth

An order-`2^30` subgroup forces extension degree at most five for `p^e < 2^160`
and at most eight for `p^e < 2^256`.
The two-adic lifting-the-exponent identity bounds the order of `p` modulo
`2^30`. The resulting lower bound for `p` is incompatible with the field-size
bound for all higher degrees. A small factor and congruence certificate then
bounds the characteristic across the sponsor’s entire field-size range. -/

namespace ArkLib.ProximityGap.Frontier.SmoothCubicCharacteristic

/-- A high power of two dividing the multiplicative group forces the
characteristic close to a multiple of a high power of two. -/
private theorem base_dvd {p e a v : ℕ} (hp : 2 ≤ p) (ho : ¬2 ∣ p) (he : 0 < e)
    (hd : 2 ^ 30 ∣ p ^ e - 1) (hv : padicValNat 2 (e + e) ≤ v) (ha : a + v ≤ 30) :
    2 ^ a ∣ p - 1 ∨ 2 ^ a ∣ p + 1 := by
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
  · exact Or.inr ((Nat.pow_dvd_iff_le_padicValNat (by decide : 2 ≠ 1) hs).mpr (by omega))
  · exact Or.inl ((Nat.pow_dvd_iff_le_padicValNat (by decide : 2 ≠ 1) hm).mpr (by omega))

private theorem base_bound {p e a v : ℕ} (hp : 2 ≤ p) (ho : ¬2 ∣ p) (he : 0 < e)
    (hd : 2 ^ 30 ∣ p ^ e - 1) (hv : padicValNat 2 (e + e) ≤ v) (ha : a + v ≤ 30) :
    2 ^ a ≤ p + 1 := by
  rcases base_dvd hp ho he hd hv ha with h | h
  · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
  · exact Nat.le_of_dvd (by omega) h

private theorem odd_characteristic {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hd : 2 ^ 30 ∣ p ^ e - 1) : p ≠ 2 := by
  rintro rfl
  have hpar := dvd_pow_self 2 he.ne'
  have hprev := dvd_trans (by decide : 2 ∣ 2 ^ 30) hd
  have hpos := Nat.pow_pos (by decide : 0 < 2) (n := e)
  omega

/-- Every prime power below `2^160` that admits a multiplicative domain of
order `2^30` has extension degree at most five. -/
theorem degree_le_five {p e : ℕ} (hp : p.Prime) (he : 0 < e) (hd : 2 ^ 30 ∣ p ^ e - 1)
    (hq : p ^ e < 2 ^ 160) : e ≤ 5 := by
  have hp2 := hp.two_le
  have hn := odd_characteristic hp he hd
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

/-- At the sponsor's field-size ceiling, the order of the domain restricts
the extension degree to at most eight. -/
theorem degree_le_eight {p e : ℕ} (hp : p.Prime) (he : 0 < e) (hd : 2 ^ 30 ∣ p ^ e - 1)
    (hq : p ^ e < 2 ^ 256) : e ≤ 8 := by
  have hp2 := hp.two_le
  have hn := odd_characteristic hp he hd
  have ho : ¬2 ∣ p := fun h => hn (hp.eq_one_or_self_of_dvd 2 h |>.resolve_left (by decide)).symm
  have h161 : e ≤ 161 := by
    by_contra! h
    have hl : 3 ^ 162 ≤ p ^ e :=
      (Nat.pow_le_pow_left (by omega : 3 ≤ p) 162).trans (Nat.pow_le_pow_right hp.pos h)
    omega
  by_contra! h9
  by_cases h12 : 12 ≤ e
  · have hv : padicValNat 2 (e + e) ≤ 8 := by
      by_contra! hh
      have hdvd := (Nat.pow_dvd_iff_le_padicValNat (by decide : 2 ≠ 1)
        (by omega : e + e ≠ 0)).mpr hh
      have := Nat.le_of_dvd (by omega : 0 < e + e) hdvd
      omega
    have hlarge := base_bound hp2 ho he hd hv (by decide : 22 + 8 ≤ 30)
    have hbound : (2 ^ 22 - 1) ^ 12 ≤ p ^ e :=
      (Nat.pow_le_pow_left (by omega) 12).trans (Nat.pow_le_pow_right hp.pos h12)
    omega
  · by_cases h10 : e = 10
    · subst e
      have hv : padicValNat 2 (10 + 10) ≤ 2 := by
        by_contra! hh
        exact (by decide : ¬2 ^ 3 ∣ 10 + 10)
          ((Nat.pow_dvd_iff_le_padicValNat (by decide) (by decide)).mpr hh)
      have hlarge := base_bound hp2 ho he hd hv (by decide : 28 + 2 ≤ 30)
      have : (2 ^ 28 - 1) ^ 10 ≤ p ^ 10 := Nat.pow_le_pow_left (by omega) 10
      omega
    · have hv : padicValNat 2 (e + e) ≤ 1 := by
        by_contra! hh
        have h := (Nat.pow_dvd_iff_le_padicValNat (by decide : 2 ≠ 1)
          (by omega : e + e ≠ 0)).mpr hh
        change 4 ∣ e + e at h
        omega
      have hlarge := base_bound hp2 ho he hd hv (by decide : 29 + 1 ≤ 30)
      have hbound : (2 ^ 29 - 1) ^ 9 ≤ p ^ e :=
        (Nat.pow_le_pow_left (by omega) 9).trans (Nat.pow_le_pow_right hp.pos h9)
      omega

private def candidate (plus : Bool) (j : Fin 32) : ℕ :=
  let t := (j.val + 1) * 2 ^ 26
  if plus then t + 1 else t - 1

private def factor (plus : Bool) (j : Fin 32) : ℕ :=
  if plus then #[5, 3, 13, 17, 3, 5, 1, 3, 1093, 23, 3, 7, 2129, 3, 31, 5,
    3, 443, 7, 3, 5, 4271, 3, 79, 29, 3, 1, 11, 3, 1, 5, 3][j]
  else #[3, 7, 1223, 3, 11, 47, 3, 233, 5, 3, 1, 15683, 3, 5, 71, 3,
    19, 137, 3, 17989, 227, 3, 7, 5, 3, 229, 11, 3, 5, 7, 3, 1][j]

-- Each candidate has a proper divisor or fails the necessary congruence at the given degree.
set_option maxRecDepth 4096 in
private theorem candidates_excluded : ∀ plus : Bool, ∀ j : Fin 32, ∀ i : Fin 8,
    let p := candidate plus j
    let d := factor plus j
    (2 ≤ d ∧ d < p ∧ d ∣ p) ∨ ¬2 ^ 30 ∣ p ^ (i.val + 1) - 1 ∨
      2147483647 ≤ p ∨ (2013265921 ≤ p ∧ 5 < i.val + 1) := by decide

/-- At the prize field-size ceiling either the base is at least the Mersenne
prime `2^31-1`, or it is at least `15·2^27+1` and the degree exceeds five. -/
theorem base_lower_bound {p e : ℕ} (hp : p.Prime) (he : 0 < e) (hd : 2 ^ 30 ∣ p ^ e - 1)
    (hq : p ^ e < 2 ^ 256) : 2147483647 ≤ p ∨ (2013265921 ≤ p ∧ 5 < e) := by
  have h8 := degree_le_eight hp he hd hq
  have hn := odd_characteristic hp he hd
  have ho : ¬2 ∣ p := fun h => hn (hp.eq_one_or_self_of_dvd 2 h |>.resolve_left (by decide)).symm
  have hv : padicValNat 2 (e + e) ≤ 4 := by
    by_contra! hlarge
    have h := (Nat.pow_dvd_iff_le_padicValNat (by decide : 2 ≠ 1) (by omega : e + e ≠ 0)).mpr
      hlarge
    have := Nat.le_of_dvd (by omega : 0 < e + e) h
    omega
  have hp2 := hp.two_le
  by_cases hlarge : 2147483647 ≤ p
  · exact Or.inl hlarge
  have hform : ∃ plus : Bool, ∃ j : Fin 32, p = candidate plus j := by
    rcases base_dvd hp2 ho he hd hv (by decide : 26 + 4 ≤ 30) with ⟨t, ht⟩ | ⟨t, ht⟩
    · refine ⟨true, ⟨t - 1, by omega⟩, ?_⟩
      simp only [candidate, ↓reduceIte]
      omega
    · refine ⟨false, ⟨t - 1, by omega⟩, ?_⟩
      simp only [candidate, Bool.false_eq_true, ↓reduceIte]
      omega
  obtain ⟨plus, j, rfl⟩ := hform
  let i : Fin 8 := ⟨e - 1, by omega⟩
  have hi : i.val + 1 = e := by dsimp [i]; omega
  have hcert := candidates_excluded plus j i
  dsimp only at hcert
  rw [hi] at hcert
  rcases hcert with h | h | h
  · exact False.elim ((Nat.not_prime_of_dvd_of_lt h.2.2 h.1 h.2.1) hp)
  · exact False.elim (h hd)
  · exact h

/-- On a smooth domain of length `2^30`, the field-order ceiling alone forces
the characteristic above all degree cutoffs in the terminal cubic argument. -/
theorem characteristic {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I]
    (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 2 ^ 30)
    (hu : Fintype.card F < 2 ^ 256) : 2013265921 ≤ ringChar F := by
  classical
  obtain ⟨equiv, _⟩ := _root_.ProximityGap.SmoothDomainMcaEquivalence.coset_equiv D
  let H := ReedSolomon.Smooth.H D
  let _ : Fintype H := Fintype.ofEquiv I equiv
  have hd : 2 ^ 30 ∣ Fintype.card F - 1 := by
    rw [← hn, Fintype.card_congr equiv]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using
      Subgroup.card_subgroup_dvd_card H
  obtain ⟨e, hp, hq⟩ := FiniteField.card F (ringChar F)
  rw [hq] at hd hu
  rcases base_lower_bound hp e.pos hd hu with h | h <;> omega

end ArkLib.ProximityGap.Frontier.SmoothCubicCharacteristic
