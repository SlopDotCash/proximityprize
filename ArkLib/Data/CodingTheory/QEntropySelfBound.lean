/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.Basic.Entropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# The q-ary entropy strictly exceeds the identity below the mode (list-decoding-capacity gap)

This file proves the analytic fact underlying the **negative side** of the ABF26 Proximity Prize
(#232): for `q ≥ 2` and `0 < x ≤ (q-1)/q`,

  `x < H_q(x)`     (`qEntropy_gt_self`).

Equivalently the list-decoding capacity `H_q⁻¹(1 − ρ)` is **strictly below** the Singleton radius
`1 − ρ`: setting `x = 1 − ρ` (valid when `ρ ≥ 1/q`) gives `H_q(1 − ρ) > 1 − ρ`, so the
capacity-exponent `n·(H_q(1−ρ) − (1−ρ))` is **positive at the Singleton radius** — the engine of the
super-polynomial list-size lower bound that refutes the up-to-capacity list-decoding conjecture
(`ProximityGap.ListDecodingConjectureRefutation`).

## Proof

Reduce to mathlib's binary entropy `Real.binEntropy x = −x·log x − (1−x)·log(1−x)` (natural log):

  `x < H_q(x)  ⟺  x·(log q − log(q−1)) < binEntropy x`     (`binEntropy_gt_linear`).

The right inequality is a **concavity-through-the-origin** argument. With `b := (q-1)/q`:
`binEntropy` is concave on `[0,1]` (`Real.strictConcave_binEntropy`) and vanishes at `0`, so
`binEntropy x ≥ (x/b)·binEntropy b`; and `binEntropy b = b·(log q − log(q−1)) + (1/q)·log q`, whose
slack `(1/q)·log q > 0` (for `q ≥ 2`) makes the inequality strict.

All results are hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

namespace CodingTheory

open Real Set

/-- **The analytic core.** For `q ≥ 2` and `0 < x ≤ (q-1)/q`,
`x·(log q − log (q−1)) < binEntropy x`. Concavity of `binEntropy` through the origin against the
mode point `b = (q-1)/q`, whose slack `(1/q)·log q` is strictly positive. -/
theorem binEntropy_gt_linear (q : ℕ) (hq : 2 ≤ q) (x : ℝ) (hx0 : 0 < x)
    (hxb : x ≤ ((q : ℝ) - 1) / q) :
    x * (Real.log q - Real.log ((q : ℝ) - 1)) < Real.binEntropy x := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  set b : ℝ := ((q : ℝ) - 1) / q with hbdef
  have hb0 : 0 < b := by rw [hbdef]; positivity
  have hb1 : b < 1 := by rw [hbdef, div_lt_one hq0]; linarith
  have hbmem : b ∈ Icc (0:ℝ) 1 := ⟨le_of_lt hb0, le_of_lt hb1⟩
  have h0mem : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have hlogb : Real.log b = Real.log ((q:ℝ) - 1) - Real.log q := by
    rw [hbdef, Real.log_div (by linarith) (by linarith)]
  have h1b : (1 : ℝ) - b = 1 / q := by rw [hbdef]; field_simp; ring
  have hlog1b : Real.log (1 - b) = - Real.log q := by
    rw [h1b, Real.log_div one_ne_zero (by linarith), Real.log_one]; ring
  have hbval : Real.binEntropy b
      = b * (Real.log q - Real.log ((q:ℝ) - 1)) + (1 / q) * Real.log q := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog,
      hlogb, hlog1b, h1b]
    ring
  have ht0 : 0 ≤ x / b := div_nonneg (le_of_lt hx0) (le_of_lt hb0)
  have ht1 : x / b ≤ 1 := by rw [div_le_one hb0]; exact hxb
  have h1t : (0:ℝ) ≤ 1 - x / b := by linarith
  have htb : x / b * b = x := by field_simp
  have hconc := (Real.strictConcave_binEntropy.concaveOn).2 hbmem h0mem ht0 h1t
    (by ring : x / b + (1 - x / b) = 1)
  simp only [smul_eq_mul, Real.binEntropy_zero, mul_zero, add_zero, htb] at hconc
  have hlq : 0 < Real.log q := Real.log_pos (by linarith)
  have hstep : x * (Real.log q - Real.log ((q:ℝ) - 1)) < x / b * Real.binEntropy b := by
    have hextra : 0 < x / b * ((1 / q) * Real.log q) :=
      mul_pos (by positivity) (mul_pos (by positivity) hlq)
    rw [hbval, mul_add, ← mul_assoc, htb]
    linarith
  linarith [hconc]

/-- **The q-ary entropy strictly exceeds the identity below the mode.** For `q ≥ 2` and
`0 < x ≤ (q-1)/q`, `x < H_q(x)`. Equivalently `H_q⁻¹(1 − ρ) < 1 − ρ`: the list-decoding capacity
lies strictly inside the Singleton bound. -/
theorem qEntropy_gt_self (q : ℕ) (hq : 2 ≤ q) (x : ℝ) (hx0 : 0 < x)
    (hxb : x ≤ ((q : ℝ) - 1) / q) :
    x < qEntropy q x := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  have hcore := binEntropy_gt_linear q hq x hx0 hxb
  have hmul : qEntropy q x * Real.log q
      = x * Real.log ((q:ℝ) - 1) + Real.binEntropy x := by
    unfold qEntropy
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog]
    simp only [Real.logb]
    field_simp
    ring
  have h3 : x * Real.log q < qEntropy q x * Real.log q := by
    rw [hmul]; nlinarith [hcore]
  exact lt_of_mul_lt_mul_right h3 (le_of_lt hlogq)

/-- **At the Singleton radius the q-ary entropy exceeds the rate complement.** For `q ≥ 2` and
`1/q ≤ ρ < 1`, `H_q(1 − ρ) > 1 − ρ`. So `n·(H_q(1−ρ) − (1−ρ)) > 0`: the capacity exponent is
strictly positive at the Singleton bound. -/
theorem qEntropy_oneSub_gt (q : ℕ) (hq : 2 ≤ q) (ρ : ℝ) (hρlt : ρ < 1)
    (hρq : 1 / (q : ℝ) ≤ ρ) :
    1 - ρ < qEntropy q (1 - ρ) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  refine qEntropy_gt_self q hq (1 - ρ) (by linarith) ?_
  rw [le_div_iff₀ hq0]
  have h1 : (1 : ℝ) ≤ ρ * q := by
    have h := mul_le_mul_of_nonneg_right hρq (le_of_lt hq0)
    rwa [one_div, inv_mul_cancel₀ (ne_of_gt hq0)] at h
  nlinarith [h1]

/-- **Capacity exponent positive at the Singleton radius (UNCONDITIONAL).** For `q ≥ 2`, `k < n`,
and rate `≥ 1/q` (`n ≤ q·k`), at any radius `δ` whose Hamming-ball mode lands on the Singleton
radius (`⌊δ·n⌋ = n − k`), the capacity exponent

  `n · H_q(⌊δn⌋/n) − (n − k)`

is strictly positive. This is precisely `ProximityGap.ListDecodingConjectureRefutation.capExp`
unfolded, so it discharges that file's open hypothesis at the Singleton radius: the list size lower
bound `q^{capExp}/(n+1)` has a positive exponent there, hence grows — the up-to-capacity
list-decoding bound is impossible. -/
theorem capacityExponent_pos (q n k : ℕ) (hq : 2 ≤ q) (hkn : k < n) (hkq : n ≤ q * k) (δ : ℝ)
    (hδfloor : ⌊δ * (n : ℝ)⌋₊ = n - k) :
    0 < (n : ℝ) * qEntropy q ((⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ)) - ((n : ℝ) - (k : ℝ)) := by
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hkn
  have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hkR : (k : ℝ) < n := by exact_mod_cast hkn
  have hkqR : (n : ℝ) ≤ q * k := by exact_mod_cast hkq
  set x : ℝ := ((n : ℝ) - k) / n with hx
  have hxe : ((⌊δ * (n : ℝ)⌋₊ : ℝ)) / (n : ℝ) = x := by
    rw [hδfloor, hx, Nat.cast_sub (le_of_lt hkn)]
  have hx0 : 0 < x := by rw [hx]; exact div_pos (by linarith) hn0R
  have hxb : x ≤ ((q : ℝ) - 1) / q := by
    rw [hx, le_div_iff₀ hq0, div_mul_eq_mul_div, div_le_iff₀ hn0R]; nlinarith [hkqR]
  have hgt := qEntropy_gt_self q hq x hx0 hxb
  have hnx : (n : ℝ) * x = (n : ℝ) - k := by rw [hx]; field_simp
  rw [hxe]
  nlinarith [mul_lt_mul_of_pos_left hgt hn0R, hnx]

#print axioms binEntropy_gt_linear
#print axioms qEntropy_gt_self
#print axioms qEntropy_oneSub_gt
#print axioms capacityExponent_pos

end CodingTheory
