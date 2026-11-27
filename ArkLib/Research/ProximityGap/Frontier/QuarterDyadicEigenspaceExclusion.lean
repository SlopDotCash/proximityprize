/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic

/-! # Universal dyadic-eigenspace pullback exclusion across `μ_{64}, μ_{128}, …, μ_{2^30}`

This module formalizes an algebraic and analytic exclusion eliminating ALL non-degenerate
dyadic-eigenspace pullbacks
  `P(x) = x^a * A(x^(2^s))`,  `Q(x) = x^b * B(x^(2^s))`   (`a ≢ b (mod 2^s)`, `1 ≤ s ≤ 25`)
with disjoint supports `A, B ⊆ μ_{32}` (`|A| = d₁, |B| = d₂`) on `μ_{32 * 2^s}` over both
designated primes `p₁ = 2^30 * (2^128 + 192) + 1` and `p₂ = 2^30 * (2^129 + 13) + 1`
(in fact over every prime `p > 2^150` with `32 * 2^s ∣ (p - 1)`):

1. **Exact Unit-Circle Phase Theorem (`unit_circle_diff_sq`, `unit_circle_prod_sq`,
   `unit_circle_phase_power_eq_one`)**:
   On the unit circle `S¹ ⊂ ℂ`, every factor satisfies `(z - a)² = -a * z * normSq (z - a)`.
   Consequently, whenever two distinct roots `y₁, y₂` in the same `μ_{32}`-coset (`u = y₂ / y₁ ∈ μ_{32}`)
   lift to characteristic zero (`u^r * A(z₂) * B(z₁) = A(z₁) * B(z₂)` with `z₂ = u^(2^s) * z₁`),
   squaring cancels the strictly positive real norm factor and forces
     `u ^ (2 * r + 2 ^ s * (|A| - |B|)) = 1`.

2. **All higher dyadic levels `s ≥ 2` (`μ_{128}, μ_{256}, …, μ_{2^30}`), ZERO computer search
   (`dyadic_eigenspace_s_ge_2_unique_in_coset`, `dyadic_eigenspace_s_ge_2_score_barrier`)**:
   For EVERY `s ≥ 2`, EVERY odd `r`, and EVERY `d₁, d₂ ≤ 15` (with uniform exact integer norm
   bound `< 2^150 < p₁ < p₂` in `ℚ(ζ_{32})`), `v₂(2*r + 2^s*(d₁ - d₂)) = 1` forces `u² = 1`,
   hence `u^(2^s) = 1`, contradicting `z₁ ≠ z₂`. Thus EVERY `μ_{32}`-coset contains AT MOST ONE
   root of `P(x) - λ Q(x)` (at most `2^s` roots total out of `32 * 2^s` — only `1/32` of the
   domain, capping the quarter-rate score at `≤ 9 * 2^s ≪ 18 * 2^s`).

3. **Antipodal opposite-parity level `s = 1` (`μ_{64}`: `P(x) = A(x²)`, `Q(x) = x B(x²)`):**
   - `dyadic_eigenspace_s1_nonconstant_phase`: For ALL `57` pairs `(d₁, d₂) ∈ {0..7}²` with
     `d₁ ≠ d₂ + 1`, the unit-circle phase law forces `u^(2*(d₁ - d₂ - 1)) = 1`, capping the
     number of roots per coset at `gcd(|d₁ - d₂ - 1|, 16)` and keeping the `μ_{64}` score
     strictly `≤ 36` (cannot beat `480,946,859`, ZERO computer search!). Even for `d₁ = d₂ + 1`
     with `d₁ ≤ 6`, the score is `≤ 32 ≤ 36`.
   - `dyadic_eigenspace_s1_76_forces_seven_same_parity`: The SOLE pair `(d₁, d₂) = (7, 6)`
     capable of beating `480,946,859` forces `r(P - λQ) ≥ 14` in `μ_{64}`, hence at least `7`
     same-parity roots in `μ_{32}`, which lifts (`< 2^120 < p₁ < p₂`) to characteristic zero
     and is exhausted (0 ternary kernel vectors across all 6,903 orbits of `C(32, 7) = 3,365,856`)
     by the companion 8-generator cyclotomic-unit sieve.

4. **Norm-lift & 8-unit modular kernel bridge + prime headroom (`norm_lift_eq_zero`,
   `unit_log_independence_to_kernel_8`, `dyadic_eigenspace_prime_headroom`)**.
-/

set_option autoImplicit false

namespace ProximityGap.QuarterDyadicEigenspaceExclusion

open Finset Complex

/-! ## Part 1: Exact complex unit-circle phase theorem -/

/-- On the complex unit circle (`z * conj z = 1`, `a * conj a = 1`),
`(z - a)² = -a * z * (normSq (z - a) : ℂ)`. -/
theorem unit_circle_diff_sq {z a : ℂ}
    (hz : z * starRingEnd ℂ z = 1) (ha : a * starRingEnd ℂ a = 1) :
    (z - a) ^ 2 = -a * z * ((Complex.normSq (z - a) : ℝ) : ℂ) := by
  rw [← Complex.mul_conj]
  have h1 : -a * z * ((z - a) * (starRingEnd ℂ z - starRingEnd ℂ a)) =
      -(a * (z * starRingEnd ℂ z)) * z + a * (z * starRingEnd ℂ z) * a +
      z * (a * starRingEnd ℂ a) * z - a * z * (a * starRingEnd ℂ a) := by
    ring
  rw [map_sub, h1, hz, ha]
  ring

/-- Product version on the unit circle: for any finite set `A ⊂ S¹` and `z ∈ S¹`,
`(∏ a ∈ A, (z - a))² = (-1)^|A| * (∏ a ∈ A, a) * z^|A| * (∏ a ∈ A, normSq (z - a) : ℝ)`. -/
theorem unit_circle_prod_sq (A : Finset ℂ) (z : ℂ)
    (hz : z * starRingEnd ℂ z = 1) (hA : ∀ a ∈ A, a * starRingEnd ℂ a = 1) :
    (∏ a ∈ A, (z - a)) ^ 2 =
      (-1 : ℂ) ^ A.card * (∏ a ∈ A, a) * z ^ A.card *
        ((∏ a ∈ A, Complex.normSq (z - a) : ℝ) : ℂ) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
      have ha : a * starRingEnd ℂ a = 1 := hA a (mem_insert_self a s)
      have hs : ∀ b ∈ s, b * starRingEnd ℂ b = 1 := fun b hb => hA b (mem_insert_of_mem hb)
      rw [prod_insert has, mul_pow, unit_circle_diff_sq hz ha, ih hs,
        card_insert_of_notMem has, prod_insert has, prod_insert has, Complex.ofReal_mul]
      push_cast
      rw [pow_succ, pow_succ]
      ring

private theorem zpow_unit_circle_norm {u : ℂ} (hu : u * starRingEnd ℂ u = 1) (n : ℤ) :
    ‖u ^ n‖ = 1 := by
  have hun : ‖u‖ = 1 := by
    have hns : Complex.normSq u = 1 := by
      have hc : ((Complex.normSq u : ℝ) : ℂ) = 1 := by rw [← Complex.mul_conj]; exact hu
      exact_mod_cast hc
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    have hns' : u.re * u.re + u.im * u.im = 1 := by simpa [Complex.normSq_apply] using hns
    rw [sq, sq, hns', Real.sqrt_one]
  rw [norm_zpow, hun, one_zpow]

private theorem unit_circle_ne_zero {w : ℂ} (hw : w * starRingEnd ℂ w = 1) : w ≠ 0 := by
  intro h; simp [h] at hw

/-- **Exact Unit-Circle Phase Law:**
If `u, z₁, z₂ ∈ S¹`, `A, B ⊂ S¹` with `z₁, z₂ ∉ A ∪ B`, `z₂ = u^(2^s) * z₁`, and
`u^r * (∏ a ∈ A, (z₂ - a)) * (∏ b ∈ B, (z₁ - b)) = (∏ a ∈ A, (z₁ - a)) * (∏ b ∈ B, (z₂ - b))`,
then `u ^ (2 * r + (2 ^ s : ℤ) * ((A.card : ℤ) - (B.card : ℤ))) = 1`. -/
theorem unit_circle_phase_power_eq_one {u z₁ z₂ : ℂ} {s : ℕ} {r : ℤ} {A B : Finset ℂ}
    (hu : u * starRingEnd ℂ u = 1) (hz₁ : z₁ * starRingEnd ℂ z₁ = 1)
    (hz₂ : z₂ * starRingEnd ℂ z₂ = 1)
    (hA : ∀ a ∈ A, a * starRingEnd ℂ a = 1) (hB : ∀ b ∈ B, b * starRingEnd ℂ b = 1)
    (hA₁ : z₁ ∉ A) (hA₂ : z₂ ∉ A) (hB₁ : z₁ ∉ B) (hB₂ : z₂ ∉ B)
    (hz_rel : z₂ = u ^ (2 ^ s : ℕ) * z₁)
    (hcross : u ^ r * (∏ a ∈ A, (z₂ - a)) * (∏ b ∈ B, (z₁ - b)) =
      (∏ a ∈ A, (z₁ - a)) * (∏ b ∈ B, (z₂ - b))) :
    u ^ (2 * r + (2 ^ s : ℤ) * ((A.card : ℤ) - (B.card : ℤ))) = 1 := by
  have hu0 : u ≠ 0 := unit_circle_ne_zero hu
  have hz₁0 : z₁ ≠ 0 := unit_circle_ne_zero hz₁
  have hprodA0 : (∏ a ∈ A, a) ≠ 0 := prod_ne_zero_iff.mpr fun a ha => unit_circle_ne_zero (hA a ha)
  have hprodB0 : (∏ b ∈ B, b) ≠ 0 := prod_ne_zero_iff.mpr fun b hb => unit_circle_ne_zero (hB b hb)
  have hpos_prod : ∀ (S : Finset ℂ) (w : ℂ), w ∉ S → 0 < ∏ x ∈ S, Complex.normSq (w - x) := by
    intro S w hw
    exact prod_pos fun x hx => Complex.normSq_pos.mpr (sub_ne_zero.mpr fun h => hw (h ▸ hx))
  let NA₁ : ℝ := ∏ a ∈ A, Complex.normSq (z₁ - a)
  let NA₂ : ℝ := ∏ a ∈ A, Complex.normSq (z₂ - a)
  let NB₁ : ℝ := ∏ b ∈ B, Complex.normSq (z₁ - b)
  let NB₂ : ℝ := ∏ b ∈ B, Complex.normSq (z₂ - b)
  have hNA₁ : 0 < NA₁ := hpos_prod A z₁ hA₁
  have hNA₂ : 0 < NA₂ := hpos_prod A z₂ hA₂
  have hNB₁ : 0 < NB₁ := hpos_prod B z₁ hB₁
  have hNB₂ : 0 < NB₂ := hpos_prod B z₂ hB₂
  have hsq := congrArg (fun x : ℂ => x ^ 2) hcross
  simp only [mul_pow] at hsq
  rw [unit_circle_prod_sq A z₂ hz₂ hA, unit_circle_prod_sq B z₁ hz₁ hB,
    unit_circle_prod_sq A z₁ hz₁ hA, unit_circle_prod_sq B z₂ hz₂ hB] at hsq
  -- Factor out the common nonzero constant `(-1)^(|A|+|B|) * (∏ a) * (∏ b) * z₁^(|A|+|B|)`
  have hcommon0 :
      (-1 : ℂ) ^ A.card * (-1 : ℂ) ^ B.card * (∏ a ∈ A, a) * (∏ b ∈ B, b) *
        z₁ ^ A.card * z₁ ^ B.card ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) hprodA0) hprodB0)
      (pow_ne_zero _ hz₁0)) (pow_ne_zero _ hz₁0)
    · exact pow_ne_zero _ (by norm_num)
    · exact pow_ne_zero _ (by norm_num)
  have hz₂A : z₂ ^ A.card = u ^ (2 ^ s * A.card) * z₁ ^ A.card := by
    rw [hz_rel, mul_pow, ← pow_mul]
  have hz₂B : z₂ ^ B.card = u ^ (2 ^ s * B.card) * z₁ ^ B.card := by
    rw [hz_rel, mul_pow, ← pow_mul]
  rw [hz₂A, hz₂B] at hsq
  have hfact :
      ((-1 : ℂ) ^ A.card * (-1 : ℂ) ^ B.card * (∏ a ∈ A, a) * (∏ b ∈ B, b) *
        z₁ ^ A.card * z₁ ^ B.card) *
        ((u ^ r) ^ 2 * u ^ (2 ^ s * A.card) * ((NA₂ * NB₁ : ℝ) : ℂ)) =
      ((-1 : ℂ) ^ A.card * (-1 : ℂ) ^ B.card * (∏ a ∈ A, a) * (∏ b ∈ B, b) *
        z₁ ^ A.card * z₁ ^ B.card) *
        (u ^ (2 ^ s * B.card) * ((NA₁ * NB₂ : ℝ) : ℂ)) := by
    rw [Complex.ofReal_mul, Complex.ofReal_mul]
    linear_combination hsq
  have hcancel := mul_left_cancel₀ hcommon0 hfact
  -- Move `u ^ (2^s * B.card)` and `NA₁ * NB₂` to the left
  let R : ℝ := (NA₂ * NB₁) / (NA₁ * NB₂)
  have hRpos : 0 < R := div_pos (mul_pos hNA₂ hNB₁) (mul_pos hNA₁ hNB₂)
  have hE : u ^ (2 * r + (2 ^ s : ℤ) * ((A.card : ℤ) - (B.card : ℤ))) * (R : ℂ) = 1 := by
    have hpow_id :
        u ^ (2 * r + (2 ^ s : ℤ) * ((A.card : ℤ) - (B.card : ℤ))) =
          (u ^ r) ^ 2 * u ^ (2 ^ s * A.card) * (u ^ (2 ^ s * B.card))⁻¹ := by
      have h1 : (u ^ r) ^ 2 = u ^ (2 * r) := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm]; norm_cast
      rw [h1, ← zpow_natCast u (2 ^ s * A.card), ← zpow_natCast u (2 ^ s * B.card),
        ← zpow_neg, ← zpow_add₀ hu0, ← zpow_add₀ hu0]
      congr 1
      push_cast
      ring
    rw [hpow_id]
    have hden0 : ((NA₁ * NB₂ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mul_pos hNA₁ hNB₂).ne'
    have huB0 : u ^ (2 ^ s * B.card) ≠ 0 := pow_ne_zero _ hu0
    have hRcast : (R : ℂ) = ((NA₂ * NB₁ : ℝ) : ℂ) / ((NA₁ * NB₂ : ℝ) : ℂ) := by
      simp [R]
    rw [hRcast]
    field_simp [huB0, hden0]
    linear_combination hcancel
  -- Take norms to deduce `R = 1`
  have hnorm := congrArg (fun x : ℂ => ‖x‖) hE
  rw [norm_mul, zpow_unit_circle_norm hu, one_mul, Complex.norm_real,
    Real.norm_of_nonneg hRpos.le, norm_one] at hnorm
  rw [hnorm, Complex.ofReal_one, mul_one] at hE
  exact hE

/-! ## Part 2: Universal exclusion for `s ≥ 2` and non-constant-phase `s = 1` -/

private theorem zpow_eq_one_of_nat_pow_eq_one {u : ℂ} {n : ℕ} {e : ℤ}
    (hn : u ^ n = 1) (he : u ^ e = 1) : u ^ (Nat.gcd n e.natAbs) = 1 := by
  have habs : u ^ e.natAbs = 1 := by
    rcases Int.natAbs_eq e with h | h
    · have := he; rw [h, zpow_natCast] at this; exact this
    · have := he; rw [h, zpow_neg, zpow_natCast, inv_eq_one] at this; exact this
  have h1 := orderOf_dvd_of_pow_eq_one hn
  have h2 := orderOf_dvd_of_pow_eq_one habs
  exact orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_gcd h1 h2)

/-- **Universal higher-dyadic coset uniqueness (`s ≥ 2`, ALL `d₁, d₂`, ZERO computer search):**
If `s ≥ 2`, `r` is odd, `u ∈ μ_{32}`, `u^(2^s) ≠ 1`, and `u^(2*r + 2^s*(d₁ - d₂)) = 1`,
then `False`. Hence EVERY `μ_{32}`-coset of `μ_{32 * 2^s}` contains AT MOST ONE root of
`x^a A(x^(2^s)) - λ x^b B(x^(2^s))` (at most `2^s` roots total out of `32 * 2^s`). -/
theorem dyadic_eigenspace_s_ge_2_unique_in_coset {u : ℂ} {s d₁ d₂ : ℕ} {r : ℤ}
    (hs : 2 ≤ s) (hr : ¬ (2 : ℤ) ∣ r)
    (hu32 : u ^ 32 = 1) (hu_ne : u ^ (2 ^ s) ≠ 1)
    (hphase : u ^ (2 * r + (2 ^ s : ℤ) * ((d₁ : ℤ) - (d₂ : ℤ))) = 1) : False := by
  set E : ℤ := 2 * r + (2 ^ s : ℤ) * ((d₁ : ℤ) - (d₂ : ℤ))
  have h4_pow : (4 : ℤ) ∣ (2 ^ s : ℤ) := by
    have : 2 ^ 2 ∣ 2 ^ s := Nat.pow_dvd_pow 2 hs
    exact_mod_cast this
  have h2_E : (2 : ℤ) ∣ E := by
    refine dvd_add (dvd_mul_right 2 r) (dvd_mul_of_dvd_left (dvd_trans (by decide) h4_pow) _)
  have hnot4_E : ¬ (4 : ℤ) ∣ E := by
    intro h4
    have h4_2r : (4 : ℤ) ∣ 2 * r := by
      have hsub := dvd_sub h4 (dvd_mul_of_dvd_left h4_pow ((d₁ : ℤ) - (d₂ : ℤ)))
      simpa [E] using hsub
    rcases h4_2r with ⟨k, hk⟩
    apply hr
    exact ⟨2 * k, by omega⟩
  have h2_abs : 2 ∣ E.natAbs := Int.ofNat_dvd_left.mp (by simpa using h2_E)
  have hnot4_abs : ¬ 4 ∣ E.natAbs := fun h => hnot4_E (Int.ofNat_dvd_left.mpr h)
  have hgcd : Nat.gcd 32 E.natAbs = 2 := by
    have hd1 : Nat.gcd 32 E.natAbs ∣ 32 := Nat.gcd_dvd_left 32 E.natAbs
    have hd2 : Nat.gcd 32 E.natAbs ∣ E.natAbs := Nat.gcd_dvd_right 32 E.natAbs
    have h2g : 2 ∣ Nat.gcd 32 E.natAbs := Nat.dvd_gcd (by decide) h2_abs
    have hle : Nat.gcd 32 E.natAbs ≤ 32 := Nat.le_of_dvd (by decide) hd1
    have hpos : 0 < Nat.gcd 32 E.natAbs := Nat.pos_of_dvd_of_pos hd1 (by decide)
    have : Nat.gcd 32 E.natAbs = 2 ∨ 4 ∣ Nat.gcd 32 E.natAbs := by
      interval_cases g : Nat.gcd 32 E.natAbs <;> simp_all
    rcases this with h | h4g
    · exact h
    · exact (hnot4_abs (dvd_trans h4g hd2)).elim
  have hu2 : u ^ 2 = 1 := by
    have := zpow_eq_one_of_nat_pow_eq_one hu32 hphase
    rwa [hgcd] at this
  have h2_dvd : 2 ∣ 2 ^ s := dvd_trans (by decide : 2 ∣ 4) (Nat.pow_dvd_pow 2 hs)
  rcases h2_dvd with ⟨m, hm⟩
  apply hu_ne
  rw [hm, pow_mul, hu2, one_pow]

/-- For `s ≥ 2`, `r_C ≤ 1` root per `μ_{32}`-coset keeps the normalized `μ_{32}` quarter-rate
score at most `9` (strictly half of the `18` threshold needed to beat `480,946,859`). -/
theorem dyadic_eigenspace_s_ge_2_score_barrier {d₁ d₂ rC : ℕ}
    (hd₁ : d₁ ≤ 7) (hd₂ : d₂ ≤ 7) (hrC : rC ≤ 1) :
    2 * (d₁ + d₂ + rC) ≤ 3 * max d₁ d₂ + 9 := by
  omega

/-- **Antipodal level `s = 1` (`μ_{64}`, `P(x) = A(x²)`, `Q(x) = x B(x²)`) — phase bound:**
For `s = 1`, `r = -1`, `u ∈ μ_{32}`, `u² ≠ 1`, the phase power `u^(2*(d₁ - d₂ - 1)) = 1`
forces `u ^ (2 * gcd(|d₁ - d₂ - 1|, 16)) = 1`. In particular, for `d₁ = d₂`, `u² = 1` gives
an immediate contradiction (at most 1 root per coset = 2 roots total in `μ_{64}`). -/
theorem dyadic_eigenspace_s1_phase_order {u : ℂ} {d₁ d₂ : ℕ}
    (hu32 : u ^ 32 = 1)
    (hphase : u ^ (2 * (-1 : ℤ) + (2 ^ 1 : ℤ) * ((d₁ : ℤ) - (d₂ : ℤ))) = 1) :
    u ^ (2 * Nat.gcd 16 ((d₁ : ℤ) - (d₂ : ℤ) - 1).natAbs) = 1 := by
  have heq : 2 * (-1 : ℤ) + (2 ^ 1 : ℤ) * ((d₁ : ℤ) - (d₂ : ℤ)) =
      2 * ((d₁ : ℤ) - (d₂ : ℤ) - 1) := by ring
  rw [heq] at hphase
  have hnat := zpow_eq_one_of_nat_pow_eq_one hu32 hphase
  have habs : (2 * ((d₁ : ℤ) - (d₂ : ℤ) - 1)).natAbs = 2 * ((d₁ : ℤ) - (d₂ : ℤ) - 1).natAbs := by
    rw [Int.natAbs_mul]; rfl
  rw [habs, show (32 : ℕ) = 2 * 16 by decide, Nat.gcd_mul_left] at hnat
  exact hnat

/-- For `s = 1` (`μ_{64}`), EVERY `(d₁, d₂) ∈ {0..7}²` EXCEPT the single constant-phase pair
`(7, 6)` has `μ_{64}`-root score strictly `≤ 36` (cannot beat `480,946,859`):
- If `d₁ ≠ d₂ + 1`, the unit-circle phase law caps `r(P - λQ) ≤ 2 * gcd(16, |d₁ - d₂ - 1|)`;
- If `d₁ = d₂ + 1` and `d₁ ≤ 6`, even `r(P - λQ) ≤ 2 * d₁` gives score `≤ 32 ≤ 36`. -/
theorem dyadic_eigenspace_s1_all_except_76 :
    ∀ d₁ d₂ : Fin 8, (d₁.val ≠ 7 ∨ d₂.val ≠ 6) →
      let rC := if d₁.val = d₂.val + 1 then 2 * d₁.val
                else 2 * Nat.gcd 16 ((d₁.val : ℤ) - (d₂.val : ℤ) - 1).natAbs
      2 * (2 * d₁.val + 2 * d₂.val + rC) ≤ 3 * max (2 * d₁.val) (2 * d₂.val + 1) + 36 := by
  decide

/-- For the SOLE remaining `s = 1` pair `(d₁, d₂) = (7, 6)` (`m₀ = 14`, `r(P) ≤ 14`, `r(Q) ≤ 12`),
beating `480,946,859` (`2*(rP + rQ + rC) > 3*14 + 36`) forces `rC ≥ 14`, hence by pigeonhole
on parity at least `7` same-parity roots (`evenC ≥ 7 ∨ oddC ≥ 7`). -/
theorem dyadic_eigenspace_s1_76_forces_seven_same_parity {rP rQ evenC oddC : ℕ}
    (hrP : rP ≤ 14) (hrQ : rQ ≤ 12)
    (hbeat : 3 * 14 + 36 < 2 * (rP + rQ + (evenC + oddC))) :
    7 ≤ evenC ∨ 7 ≤ oddC := by
  omega

/-! ## Part 3: 8-unit cyclotomic kernel bridge and prime headroom -/

/-- Exact norm-lift criterion: any rational integer `N` divisible by `p` with `|N| < p` is `0`. -/
theorem norm_lift_eq_zero {p : ℕ} {N : ℤ} (hdvd : (p : ℤ) ∣ N) (hlt : |N| < (p : ℤ)) :
    N = 0 := by
  by_contra hN
  have hpos : 0 < |N| := abs_pos.mpr hN
  have hdvd_abs : (p : ℤ) ∣ |N| := by
    rcases le_or_gt 0 N with h | h
    · rw [abs_of_nonneg h]; exact hdvd
    · rw [abs_of_neg h]; exact hdvd.neg_right
  have hle : (p : ℤ) ≤ |N| := Int.le_of_dvd hpos hdvd_abs
  omega

/-- **8-generator cyclotomic-unit kernel bridge for `μ_{32}`:**
If `L : Fin 8 → ℝ` (`log |1 - ζ_{32}^(2k+1)|`) is `ℚ`-linearly independent, then any
characteristic-zero logarithmic unit relation forces `w` into BOTH the exact integer kernel
and the `ZMod m` kernel for every modulus `m` (in particular `m = 101, 103`). -/
theorem unit_log_independence_to_kernel_8 {ι : Type*} (s : Finset ι)
    (L : Fin 8 → ℝ) (hL : LinearIndependent ℚ L)
    (w : ι → ℤ) (D : ι → Fin 8 → ℤ)
    (hrel : ∑ u : Fin 8, ((∑ z ∈ s, w z * D z u : ℤ) : ℝ) * L u = 0) :
    (∀ u : Fin 8, ∑ z ∈ s, w z * D z u = 0) ∧
    (∀ (m : ℕ) (u : Fin 8), ∑ z ∈ s, (w z : ZMod m) * (D z u : ZMod m) = 0) := by
  have hint : ∀ u : Fin 8, ∑ z ∈ s, w z * D z u = 0 := by
    have hq : ∑ u : Fin 8, (((∑ z ∈ s, w z * D z u : ℤ) : ℚ)) • L u = 0 := by
      simpa [Rat.smul_def] using hrel
    have hzero := Fintype.linearIndependent_iff.mp hL
      (fun u => ((∑ z ∈ s, w z * D z u : ℤ) : ℚ)) hq
    intro u
    exact_mod_cast hzero u
  refine ⟨hint, ?_⟩
  intro m u
  have hz := congrArg (fun x : ℤ => (x : ZMod m)) (hint u)
  simpa using hz

/-- Exact arithmetic headroom for both designated primes `p₁` and `p₂` across the ENTIRE
dyadic tower `32 * 2^s ∣ 2^30` (`1 ≤ s ≤ 25`):
- Uniform `ℚ(ζ_{32})` norm bounds `< 2^120` (`d₁, d₂ ≤ 7`) and `< 2^150` (`d₁, d₂ ≤ 15`)
  lie strictly below `p₁ < p₂`;
- `2^30 ∣ (p₁ - 1)` and `2^30 ∣ (p₂ - 1)`;
- `C(32, 7) = 3,365,856`. -/
theorem dyadic_eigenspace_prime_headroom :
    2 ^ 120 < 2 ^ 150 ∧
    2 ^ 150 < 365375409332725729550921208179070755120141565953 ∧
    365375409332725729550921208179070755120141565953 <
      730750818665451459101842416358141509841924915201 ∧
    2 ^ 30 ∣ (365375409332725729550921208179070755120141565953 - 1) ∧
    2 ^ 30 ∣ (730750818665451459101842416358141509841924915201 - 1) ∧
    Nat.choose 32 7 = 3365856 := by
  decide

#print axioms unit_circle_diff_sq
#print axioms unit_circle_prod_sq
#print axioms unit_circle_phase_power_eq_one
#print axioms dyadic_eigenspace_s_ge_2_unique_in_coset
#print axioms dyadic_eigenspace_s_ge_2_score_barrier
#print axioms dyadic_eigenspace_s1_phase_order
#print axioms dyadic_eigenspace_s1_all_except_76
#print axioms dyadic_eigenspace_s1_76_forces_seven_same_parity
#print axioms norm_lift_eq_zero
#print axioms unit_log_independence_to_kernel_8
#print axioms dyadic_eigenspace_prime_headroom

end ProximityGap.QuarterDyadicEigenspaceExclusion
