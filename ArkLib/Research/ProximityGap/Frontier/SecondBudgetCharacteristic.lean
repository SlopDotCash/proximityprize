/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence
import Mathlib.FieldTheory.Finite.Basic

/-! # The characteristic in the twice-length 128-bit budget class

Every odd prime power between 2¹⁵⁹ and 2¹⁵⁹ + 2¹²⁸ − 1 has exponent at most five.
For exponents six through one hundred we certify the consecutive odd bases on
either side of the interval. Characteristic two cannot supply an even-size
multiplicative coset. Consequently every smooth prize code in this field band
has characteristic above the degree bound used in the ordinary-polar proof.
-/

namespace ArkLib.ProximityGap.Frontier.SecondBudgetCharacteristic

private abbrev lo := 2 ^ 159
private abbrev hi := 2 ^ 159 + 2 ^ 128

/-- Largest odd base whose indicated power is strictly below the field band. -/
private def lowerOdd (e : ℕ) : ℕ :=
  let initial := #[94906265, 6881471, 961547, 208063, 61147, 22451, 9741, 4805, 2623,
    1551, 979, 653, 455, 329, 247, 189, 149, 119, 97, 81, 69, 59, 51, 43, 39, 33, 31,
    27, 25, 23, 21, 19, 17]
  if e ≤ 38 then initial[e - 6]?.getD 1
  else if e ≤ 40 then 15 else if e ≤ 42 then 13 else if e ≤ 45 then 11
  else if e ≤ 50 then 9 else if e ≤ 56 then 7 else if e ≤ 68 then 5 else 3

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- The certificate checks both endpoints for 95 distinct exponents by kernel reduction.
private theorem power_gaps : ∀ j : Fin 95, let e := j.val + 6
    let a := lowerOdd e
    a % 2 = 1 ∧ a ^ e < lo ∧ hi ≤ (a + 2) ^ e := by decide

/-- At 128-bit tolerance and budget 2³¹ an odd-characteristic field has
extension degree at most five, and its characteristic exceeds the cubic bound. -/
theorem odd_power {p e : ℕ} (hp : p.Prime) (hne : p ≠ 2) (hB : p ^ e / 2 ^ 128 = 2147483648) :
    e ≤ 5 ∧ 1744830589 < p := by
  have hlow : lo ≤ p ^ e :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 2 ^ 128)).mp hB.ge
  have hhigh : p ^ e < hi :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 128)).mp
      (hB.trans_lt (by decide : 2147483648 < 2147483649))
  have hodd := hp.odd_of_ne_two hne
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h100 : e ≤ 100 := by
    by_contra! he
    have H : 3 ^ 101 ≤ p ^ e :=
      (Nat.pow_le_pow_left hp3 101).trans (Nat.pow_le_pow_right hp.pos he)
    exact (not_lt_of_ge ((by decide : hi ≤ 3 ^ 101).trans H)) hhigh
  have h5 : e ≤ 5 := by
    by_contra! h6
    let j : Fin 95 := ⟨e - 6, by omega⟩
    have he : j.val + 6 = e := by dsimp [j]; omega
    have h := power_gaps j
    dsimp only at h
    rw [he] at h
    obtain ⟨ha, hcut, hnext⟩ := h
    by_cases small : p ≤ lowerOdd e
    · exact (not_lt_of_ge hlow) ((Nat.pow_le_pow_left small e).trans_lt hcut)
    · obtain ⟨x, hx⟩ := hodd
      have large : lowerOdd e + 2 ≤ p := by omega
      exact (not_lt_of_ge (hnext.trans (Nat.pow_le_pow_left large e))) hhigh
  refine ⟨h5, ?_⟩
  by_contra! hc
  have h := (Nat.pow_le_pow_right hp.pos h5).trans (Nat.pow_le_pow_left hc 5)
  exact (not_lt_of_ge (hlow.trans h)) (by decide)

/-- An even smooth multiplicative domain cannot occur in characteristic two. -/
theorem ne_two_of_even_smooth {F I : Type} [Field F] [Finite F] [DecidableEq F] [Fintype I]
    (D : I ↪ F) [ReedSolomon.Smooth D] (hn : 2 ∣ Fintype.card I) : ringChar F ≠ 2 := by
  classical
  let _ := Fintype.ofFinite F
  obtain ⟨e, _⟩ := _root_.ProximityGap.SmoothDomainMcaEquivalence.coset_equiv D
  let H := ReedSolomon.Smooth.H D
  let _ : Fintype H := Fintype.ofEquiv I e
  have dvd : Fintype.card I ∣ Fintype.card F - 1 := by
    have h := Subgroup.card_subgroup_dvd_card H
    have hcard : Fintype.card I = Fintype.card H := Fintype.card_congr e
    rw [hcard]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using h
  intro he
  obtain ⟨m, _, hq⟩ := FiniteField.card F (ringChar F)
  rw [he] at hq
  have hpar : 2 ∣ 2 ^ (m : ℕ) := dvd_pow_self 2 m.pos.ne'
  have hpair := hn.trans dvd
  rw [hq] at hpair
  have hpos : 0 < 2 ^ (m : ℕ) := by positivity
  omega

/-- The cubic characteristic bound follows solely from the sponsor domain and integer budget. -/
theorem smooth {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I]
    (D : I ↪ F) [ReedSolomon.Smooth D] (hn : 2 ∣ Fintype.card I)
    (hB : Fintype.card F / 2 ^ 128 = 2147483648) : 1744830589 < ringChar F := by
  obtain ⟨m, hp, hm⟩ := FiniteField.card F (ringChar F)
  rw [hm] at hB
  exact (odd_power hp (ne_two_of_even_smooth D hn) hB).2

#print axioms smooth
end ArkLib.ProximityGap.Frontier.SecondBudgetCharacteristic
