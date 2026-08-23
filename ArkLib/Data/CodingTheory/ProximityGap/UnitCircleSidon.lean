/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCharZeroBound

/-!
# `μ_n` IS A SIDON SET OVER ℂ (#389) — the heart of the small-subgroup δ* pin

The deployed proximity prize lives in the **small-subgroup regime** `n ≪ √p` (NTT length `n`,
field `F_p`, `p = 2¹²⁸`), not the hard Garcia–Voloch regime `t ~ √p`.  There the Garcia–Voloch
object `r(c) = |μ_n ∩ (c − μ_n)|` is governed by additive parallelograms in `μ_n`, and the key
fact is that **`μ_n` is a Sidon set over ℂ**:

> **`unitCircle_sidon`** — for roots of unity `a, b, c, d` (`zⁿ = 1`) with `a + b = c + d ≠ 0`,
> the unordered pairs coincide: `{a,b} = {c,d}`.

This is the elementary heart (conjugation `= inversion` on the unit circle), and is *proven*, not
conjectural.  It is what makes the lifting argument work: a nontrivial additive parallelogram in
`μ_n ⊂ F_p` forces `p ∣ Res(Φ_n, X^i + X^j − X^k − X^l)`, a **nonzero** integer (nonzero *because*
of this lemma), of size `≤ 4^{φ(n)} = 2^n`.  Hence for `p > 2^n` the subgroup `μ_n ⊂ F_p` is Sidon,
`E(μ_n) = 3n² − 3n` exactly, and (via `additiveEnergy_le_of_repCount_le_two`) δ* is pinned to its
char-0 value for every smooth-RS code of length `n < log₂ p`.  No Weil, no Stepanov.  Issue #389.
-/

open Complex

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **The algebraic Sidon core.**  In an integral domain, two unordered pairs with equal sum and
equal product coincide. -/
theorem pair_eq_of_sum_prod_eq {R : Type*} [CommRing R] [IsDomain R] {a b c d : R}
    (hsum : a + b = c + d) (hprod : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have key : (a - c) * (a - d) = 0 := by linear_combination a * hsum - hprod
  rcases mul_eq_zero.mp key with h | h
  · left
    have hac : a = c := by linear_combination h
    exact ⟨hac, by linear_combination hsum - hac⟩
  · right
    have had : a = d := by linear_combination h
    exact ⟨had, by linear_combination hsum - had⟩

/-- **`μ_n` IS SIDON OVER ℂ.**  For `n`-th roots of unity `a, b, c, d` with `a + b = c + d ≠ 0`,
the unordered pairs coincide.  Proof: conjugation is inversion on the unit circle, so conjugating
`a+b=c+d` gives `a⁻¹+b⁻¹ = c⁻¹+d⁻¹`, i.e. `(a+b)/(ab) = (c+d)/(cd)`; cancelling `a+b ≠ 0` yields
`ab = cd`, and equal sum + equal product forces equal pairs. -/
theorem unitCircle_sidon {n : ℕ} (hn : n ≠ 0) {a b c d : ℂ}
    (ha : a ^ n = 1) (hb : b ^ n = 1) (hc : c ^ n = 1) (hd : d ^ n = 1)
    (hsum : a + b = c + d) (hne : a + b ≠ 0) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  -- nonzero: roots of unity
  have ha0 : a ≠ 0 := fun h => by rw [h, zero_pow hn] at ha; exact zero_ne_one ha
  have hb0 : b ≠ 0 := fun h => by rw [h, zero_pow hn] at hb; exact zero_ne_one hb
  have hc0 : c ≠ 0 := fun h => by rw [h, zero_pow hn] at hc; exact zero_ne_one hc
  have hd0 : d ≠ 0 := fun h => by rw [h, zero_pow hn] at hd; exact zero_ne_one hd
  -- conjugation = inversion on the unit circle
  have hai : a * (starRingEnd ℂ) a = 1 := mul_conj_eq_one_of_pow_eq_one hn ha
  have hbi : b * (starRingEnd ℂ) b = 1 := mul_conj_eq_one_of_pow_eq_one hn hb
  have hci : c * (starRingEnd ℂ) c = 1 := mul_conj_eq_one_of_pow_eq_one hn hc
  have hdi : d * (starRingEnd ℂ) d = 1 := mul_conj_eq_one_of_pow_eq_one hn hd
  -- conjugate the sum relation
  have hconj : (starRingEnd ℂ) a + (starRingEnd ℂ) b = (starRingEnd ℂ) c + (starRingEnd ℂ) d := by
    have := congrArg (starRingEnd ℂ) hsum
    simpa [map_add] using this
  -- turn conjugates into inverses: `conj a = a⁻¹`, etc.
  have hcA : (starRingEnd ℂ) a = a⁻¹ := by
    field_simp; linear_combination hai
  have hcB : (starRingEnd ℂ) b = b⁻¹ := by field_simp; linear_combination hbi
  have hcC : (starRingEnd ℂ) c = c⁻¹ := by field_simp; linear_combination hci
  have hcD : (starRingEnd ℂ) d = d⁻¹ := by field_simp; linear_combination hdi
  rw [hcA, hcB, hcC, hcD] at hconj
  -- `a⁻¹+b⁻¹ = c⁻¹+d⁻¹` cross-multiplies to `(a+b)·cd = (c+d)·ab`
  have hcross : (a + b) * (c * d) = (c + d) * (a * b) := by
    field_simp at hconj
    linear_combination hconj
  -- substitute `c+d = a+b` and cancel `a+b ≠ 0` to get `ab = cd`
  have hprod : a * b = c * d := by
    have h2 : (a + b) * (c * d) = (a + b) * (a * b) := by rw [hcross, hsum]
    exact (mul_left_cancel₀ hne h2).symm
  exact pair_eq_of_sum_prod_eq hsum hprod

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.pair_eq_of_sum_prod_eq
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.unitCircle_sidon
