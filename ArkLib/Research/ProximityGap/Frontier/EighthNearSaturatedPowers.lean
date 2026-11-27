/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! # Near-saturated four-head power-slope obstructions at 671,088,640 errors

At length `n = 2^30`, dimension `k = 2^27`, degree `d = k - 1 = 134,217,727`, and error
count `e = 5k = 671,088,640`, any overrun on the second designated prime requires four
rich heads with no three collinear and sorted fresh-site deficits `(1, 1, 1, q)` with
`1 ≤ q ≤ 5` and core-incidence slack `0 ≤ s ≤ q - 1 ≤ 4`.

Previously (`saturated-power-translations.md` / `PowerSlopeCoincidences.lean`), power-slope
exclusions were established only at exact saturation `s = 0` (`q = 1`). This module extends
those obstructions across **all five** exceptional profiles `(1, 1, 1, 1)` through `(1, 1, 1, 5)`
(`0 ≤ s ≤ 4`):

1. **Optimal head-zero selection & exact near-saturated slack bounds** (`exists_optimal_head`,
   `near_saturated_bounds`): choosing a base head `0` with `3 * z₃ ≤ y₃` forces the reduced
   direction degrees `(m₁, m₂, m₃)` to satisfy `d - 5 ≤ m₁ + m₂ + m₃ ≤ d + s` and every
   unsigned pair coincidence `eⱼₖ` to lose at most `8` sites from `mⱼ + mₖ`.
2. **Constant-edge exclusion** (`no_constant_edge_q_ge_two`, `no_constant_edge_q_one`):
   no pair of heads among the four can have constant projective direction (`mᵢ ≥ 1`) for any
   `1 ≤ q ≤ 5`.
3. **Quartic-factorization exclusion** (`no_quartic_direction_triple`): if all three reduced
   direction maps from head `0` factor through `X^4`, the quartet produces at most
   `14k + 34 = 1,879,048,226` distinct labels, fitting far below `2n` even with the full
   `20,607,410` residual allowance.
4. **Arithmetic classification of three Möbius-of-power slopes for all `0 ≤ s ≤ 4`**
   (`near_saturated_power_triples`): after removing `4 ∣ (a, b, c)` and applying the cyclic
   Möbius graph bound on `H` (`gcd = 1`) or `H²` (`gcd = 2`), only six explicit boundary
   triples survive:
   - Family I: `(2^26 + k, 2^26 - k, k)` for `k ∈ {1, 2, 3}`,
   - Family II: `(2^27 - k, k, k)` for `k ∈ {1, 2, 3}`.
5. **Polynomial coset-sparsity refutations** (`family_one_coset_obstruction`,
   `family_two_coset_obstruction`): over any field `F`, Family II forces `L₀₂` to have at
   most `8 * (k - 1 + deg R) ≤ 80` roots in `H = μ_{2^30}`, and Family I forces `L₀₁` and
   `L₀₂` to share all `≥ 2^26 - 8` roots of `(X^{2^26} - ω₀) / R` in `H`, contradicting
   `x₃ + x₄ ≤ 8`.
6. **One power slope + two arbitrary companions** (`eighth_near_saturated_companion`):
   across all `0 ≤ s ≤ 4`, at least one companion has degree at least `7,479,697`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.EighthNearSaturatedPowers

open Finset Polynomial

abbrev n : ℕ := 1073741824
abbrev k : ℕ := 134217728
abbrev d : ℕ := 134217727
abbrev e : ℕ := 671088640

/-! ## Section 1: Near-saturated incidence & direction-degree bounds (`0 ≤ s ≤ 4`) -/

/-- Among four heads, some head is omitted by at most a quarter of the triple-owned sites. -/
theorem exists_optimal_head (z : Fin 4 → ℕ) :
    ∃ i : Fin 4, 3 * z i ≤ (∑ j : Fin 4, z j) - z i := by
  have hsum : ∑ j : Fin 4, z j = z 0 + z 1 + z 2 + z 3 := by
    simp [Fin.sum_univ_four, add_assoc]
  by_cases h0 : 4 * z 0 ≤ z 0 + z 1 + z 2 + z 3
  · exact ⟨0, by omega⟩
  by_cases h1 : 4 * z 1 ≤ z 0 + z 1 + z 2 + z 3
  · exact ⟨1, by omega⟩
  by_cases h2 : 4 * z 2 ≤ z 0 + z 1 + z 2 + z 3
  · exact ⟨2, by omega⟩
  exact ⟨3, by omega⟩

/-- Exact near-saturated slack bounds for `0 ≤ s ≤ 4` when head `0` is chosen with
`3 * z₃ ≤ y₃` (where `y₃` counts triple sites containing head `0` and `z₃` counts
triple sites omitting head `0`). -/
theorem near_saturated_bounds
    {s x₀ x₂ y₃ z₃ x₄ e₀₁ e₀₂ e₀₃ e₁₂ e₁₃ e₂₃ m₁ m₂ m₃ : ℕ}
    (hs : s ≤ 4)
    (hopt : 3 * z₃ ≤ y₃)
    (hinc : x₂ + 2 * (y₃ + z₃) + 3 * x₄ + s = 4 * d + x₀)
    (htri_all : 2 * x₂ + 5 * (y₃ + z₃) + 8 * x₄ ≤ 8 * d)
    (hx₂ : e₀₁ + e₀₂ + e₀₃ + e₁₂ + e₁₃ + e₂₃ = x₂)
    (htri123 : e₁₂ + e₁₃ + e₂₃ + y₃ + 2 * z₃ + 2 * x₄ ≤ 2 * d)
    (htri0 : 2 * (e₀₁ + e₀₂ + e₀₃) + (e₁₂ + e₁₃ + e₂₃) + 4 * y₃ + 3 * z₃ + 6 * x₄ ≤ 6 * d)
    (hm_sum : m₁ + m₂ + m₃ + (e₀₁ + e₀₂ + e₀₃ + 2 * y₃ + 3 * x₄) ≤ 3 * d)
    (he₁₂ : e₁₂ ≤ m₁ + m₂) (he₁₃ : e₁₃ ≤ m₁ + m₃) (he₂₃ : e₂₃ ≤ m₂ + m₃) :
    y₃ + z₃ + 2 * x₄ + 2 * x₀ ≤ 2 * s ∧
    z₃ ≤ 2 ∧
    d - 5 ≤ m₁ + m₂ + m₃ ∧
    m₁ + m₂ + m₃ ≤ d + s ∧
    (m₁ + m₂ - e₁₂) + (m₁ + m₃ - e₁₃) + (m₂ + m₃ - e₂₃) ≤ 8 ∧
    m₁ + m₂ ≤ e₁₂ + 8 ∧ m₁ + m₃ ≤ e₁₃ + 8 ∧ m₂ + m₃ ≤ e₂₃ + 8 ∧
    2 * d ≤ e₁₂ + e₁₃ + e₂₃ + 10 ∧
    2 * d ≤ e₀₁ + e₀₂ + e₀₃ + 16 := by
  simp only [d] at *
  have h1 : y₃ + z₃ + 2 * x₄ + 2 * x₀ ≤ 2 * s := by
    clear hopt hx₂ htri123 htri0 hm_sum he₁₂ he₁₃ he₂₃
    omega
  have h2 : z₃ ≤ 2 := by
    clear hinc htri_all hx₂ htri123 htri0 hm_sum he₁₂ he₁₃ he₂₃
    omega
  have h3 : 2 * 134217727 ≤ e₁₂ + e₁₃ + e₂₃ + 10 := by
    clear htri_all htri123 hm_sum he₁₂ he₁₃ he₂₃ h1
    omega
  have h4 : 134217727 - 5 ≤ m₁ + m₂ + m₃ := by
    clear hs hopt hinc htri_all hx₂ htri123 htri0 hm_sum h1 h2
    omega
  have h5 : m₁ + m₂ + m₃ ≤ 134217727 + s := by
    clear hs hopt htri_all htri0 he₁₂ he₁₃ he₂₃ h1 h2 h3 h4
    omega
  have h6 : 2 * (m₁ + m₂ + m₃) ≤ e₁₂ + e₁₃ + e₂₃ + 8 := by
    clear htri_all htri0 he₁₂ he₁₃ he₂₃ h3 h4 h5
    omega
  have h7 : (m₁ + m₂ - e₁₂) + (m₁ + m₃ - e₁₃) + (m₂ + m₃ - e₂₃) ≤ 8 := by
    clear hs hopt hinc htri_all hx₂ htri123 htri0 hm_sum h1 h2 h3 h4 h5
    omega
  have h8 : 2 * 134217727 ≤ e₀₁ + e₀₂ + e₀₃ + 16 := by
    clear hopt htri_all htri0 hm_sum he₁₂ he₁₃ he₂₃ h2 h3 h4 h5 h6 h7
    omega
  refine ⟨h1, h2, h4, h5, h7, ?_, ?_, ?_, h3, h8⟩ <;>
    (clear hs hopt hinc htri_all hx₂ htri123 htri0 hm_sum h1 h2 h3 h4 h5 h6 h8; omega)

/-- Concrete `e₀₁` and `e₀₂` root-count lower bounds in Families I and II directly from
the near-saturated slack bounds (`e₀₁ + e₀₂ + e₀₃ ≥ 2d - 16` and `mᵢ + e₀ᵢ ≤ d`). -/
theorem near_saturated_family_root_floors
    {m₁ m₂ m₃ e₀₁ e₀₂ e₀₃ kk : ℕ}
    (hsum : 2 * d ≤ e₀₁ + e₀₂ + e₀₃ + 16)
    (hm₁ : m₁ + e₀₁ ≤ d) (hm₂ : m₂ + e₀₂ ≤ d) (hm₃ : m₃ + e₀₃ ≤ d) :
    ((m₁ = 67108864 + kk ∧ m₂ = 67108864 - kk ∧ m₃ = kk ∧ 1 ≤ kk ∧ kk ≤ 3) →
      67108848 ≤ e₀₁) ∧
    ((m₁ = 134217728 - kk ∧ m₂ = kk ∧ m₃ = kk ∧ 1 ≤ kk ∧ kk ≤ 3) →
      134217712 ≤ e₀₂) := by
  simp only [d] at *
  constructor <;> intro h <;> omega

/-! ## Section 2: Constant-edge and quartic-direction-triple exclusions for all `1 ≤ q ≤ 5` -/

/-- For `q ≥ 2` at `e = 671,088,640`, a single constant projective direction on one edge
loses at least `4k - 5` fresh slots across its two endpoints, forcing the quartet far
below `2n` even with the full `20,607,410` residual allowance. -/
theorem no_constant_edge_q_ge_two {q L₁ L₂ L₃ L₄ c₁ c₂ lost other : ℕ}
    (hq : 2 ≤ q)
    (h3 : L₃ ≤ 1 + e / 1)
    (h4 : L₄ ≤ 1 + e / q)
    (hc1 : 3 * k - 5 ≤ c₁) (hc2 : 3 * k - 1 ≤ c₂)
    (hlost : c₁ + c₂ - 2 * d - 1 ≤ lost)
    (hpair : L₁ + L₂ + lost ≤ 2 * (1 + e / 1))
    (hother : other ≤ 20607410) :
    L₁ + L₂ + L₃ + L₄ + other ≤ 1832546747 := by
  have h4' : L₄ ≤ 1 + e / 2 := h4.trans (Nat.add_le_add_left (Nat.div_le_div_left hq (by decide)) 1)
  simp only [e, k, d] at *
  omega

/-- For `q = 1` (`s = 0`), a constant projective direction on one edge forces its opposite
edge to have constant projective direction too (by the constant nonsingular form), losing
at least `8k - 2` slots in total. -/
theorem no_constant_edge_q_one {L₁ L₂ L₃ L₄ lost₁ lost₂ other : ℕ}
    (hl1 : 4 * k - 1 ≤ lost₁) (hl2 : 4 * k - 1 ≤ lost₂)
    (hpair1 : L₁ + L₂ + lost₁ ≤ 2 * (1 + e / 1))
    (hpair2 : L₃ + L₄ + lost₂ ≤ 2 * (1 + e / 1))
    (hother : other ≤ 20607410) :
    L₁ + L₂ + L₃ + L₄ + other ≤ 1631220152 := by
  simp only [e, k] at *
  omega

/-- If all three reduced direction maps from head `0` factor through `X^4` on `H`,
their combined image has size at most `3 * (n / 4) = 6k`, and the remaining off-`C₀`
fresh slots among `{1, 2, 3}` contribute at most `8k + 34`, putting the full label count
far below `2n` across all `0 ≤ s ≤ 4`. -/
theorem no_quartic_direction_triple {c₀ x₀ e₁₂ e₁₃ e₂₃ inUnion offZero other : ℕ}
    (hc₀ : 3 * k - 5 ≤ c₀)
    (hx₀ : x₀ ≤ 4)
    (hdoubles : 2 * d ≤ e₁₂ + e₁₃ + e₂₃ + 10)
    (hUnion : inUnion ≤ 3 * (n / 4))
    (hOff : offZero ≤ 2 * (n - c₀) - (e₁₂ + e₁₃ + e₂₃) + 3 * x₀)
    (hother : other ≤ 20607410) :
    inUnion + offZero + other ≤ 1899655636 := by
  simp only [n, k, d] at *
  omega

/-! ## Section 3: Exact arithmetic classification of three power slopes for `0 ≤ s ≤ 4` -/

/-- Cyclic Möbius graph cutoff on `H` (`n = 2^30`, `gcd = 1`) with up to 8 missing sites. -/
theorem mobius_cutoff_H {u v hit : ℕ}
    (hloss : u + v ≤ hit + 8)
    (hbound : hit * hit ≤ hit + (n - 1) * 2) :
    u + v ≤ 46349 := by
  have h1 : hit ≤ 46341 := by
    by_contra! hh
    have hge : 46342 ≤ hit := by omega
    have hmul := Nat.mul_le_mul hge (by omega : 46341 ≤ hit - 1)
    have hsub : hit * (hit - 1) + hit = hit * hit := by cases hit <;> simp [Nat.mul_succ]
    simp only [n] at hbound
    omega
  omega

/-- Cyclic Möbius graph cutoff on `H²` (`n/2 = 2^29`, `gcd = 2`) with up to 4 missing
quotient sites. -/
theorem mobius_cutoff_H2 {u v hit : ℕ}
    (hloss : u + v ≤ hit + 4)
    (hbound : hit * hit ≤ hit + (n / 2 - 1) * 2) :
    u + v ≤ 32772 := by
  have h1 : hit ≤ 32768 := by
    by_contra! hh
    have hge : 32769 ≤ hit := by omega
    have hmul := Nat.mul_le_mul hge (by omega : 32768 ≤ hit - 1)
    have hsub : hit * (hit - 1) + hit = hit * hit := by cases hit <;> simp [Nat.mul_succ]
    simp only [n] at hbound
    omega
  omega

/-- An integer `m > 46349` with `gcd(m, 2^30) ≥ m - 8` must be an exact power of two. -/
theorem eq_pow_two_of_near_gcd {m : ℕ} (hlarge : 46349 < m) (hgcd : m ≤ Nat.gcd m n + 8) :
    ∃ r : ℕ, m = 2 ^ r := by
  have hdv : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
  have hdv2 : Nat.gcd m n ∣ 2 ^ 30 := Nat.gcd_dvd_right m n
  obtain ⟨q, hq⟩ := hdv
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | h
    · simp at hq; omega
    · exact h
  have hq1 : q = 1 := by
    by_contra hne
    have hq2 : 2 ≤ q := by omega
    have hmul : Nat.gcd m n * 2 ≤ m := by
      have h' := Nat.mul_le_mul_left (Nat.gcd m n) hq2
      linarith
    omega
  rw [hq1, mul_one] at hq
  rw [hq]
  obtain ⟨r, _, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdv2
  exact ⟨r, hr⟩

/-- Same power-of-two forcing on `H²` (`m > 32772`, `gcd(m, 2^29) ≥ m - 4`). -/
theorem eq_pow_two_of_near_gcd_H2 {m : ℕ} (hlarge : 32772 < m)
    (hgcd : m ≤ Nat.gcd m (n / 2) + 4) :
    ∃ r : ℕ, m = 2 ^ r := by
  have hdv : Nat.gcd m (n / 2) ∣ m := Nat.gcd_dvd_left m (n / 2)
  have hdv2 : Nat.gcd m (n / 2) ∣ 2 ^ 29 := Nat.gcd_dvd_right m (n / 2)
  obtain ⟨q, hq⟩ := hdv
  have hq1 : q = 1 := by
    by_contra hne
    rcases Nat.eq_zero_or_pos q with rfl | hpos
    · simp at hq; omega
    · have hmul : Nat.gcd m (n / 2) * 2 ≤ m := by
        have h' := Nat.mul_le_mul_left (Nat.gcd m (n / 2)) (by omega : 2 ≤ q)
        linarith
      omega
  rw [hq1, mul_one] at hq
  rw [hq]
  obtain ⟨r, _, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdv2
  exact ⟨r, hr⟩

/-- A power of two in `[2^25 + 1, 2^28 - 1]` is `2^26` or `2^27`. -/
private lemma pow_two_in_band {x : ℕ} (hlo : 33554432 < x) (hhi : x < 268435456)
    (hpow : ∃ r : ℕ, x = 2 ^ r) :
    x = 67108864 ∨ x = 134217728 := by
  obtain ⟨r, rfl⟩ := hpow
  have rlo : 26 ≤ r := by
    by_contra! h
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : r ≤ 25)
    norm_num at this; omega
  have rhi : r ≤ 27 := by
    by_contra! h
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 28 ≤ r)
    norm_num at this; omega
  interval_cases r <;> norm_num

/-- A power of two in `[2^24 + 1, 2^27 - 1]` is `2^25` or `2^26`. -/
private lemma pow_two_in_band_H2 {x : ℕ} (hlo : 16777216 < x) (hhi : x < 134217728)
    (hpow : ∃ r : ℕ, x = 2 ^ r) :
    x = 33554432 ∨ x = 67108864 := by
  obtain ⟨r, rfl⟩ := hpow
  have rlo : 25 ≤ r := by
    by_contra! h
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : r ≤ 24)
    norm_num at this; omega
  have rhi : r ≤ 26 := by
    by_contra! h
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 27 ≤ r)
    norm_num at this; omega
  interval_cases r <;> norm_num

/-- An odd number greater than `1` cannot be a power of two. -/
private lemma odd_gt_one_not_pow_two {x : ℕ} (hodd : x % 2 = 1) (hgt : 1 < x)
    (hpow : ∃ r : ℕ, x = 2 ^ r) : False := by
  obtain ⟨r, rfl⟩ := hpow
  cases r with
  | zero => norm_num at hgt
  | succ r => simp [pow_succ] at hodd

/-- Complete classification of ordered triples `(a, b, c)` of positive power-slope degrees
with `d - 5 ≤ a + b + c ≤ d + 4`, `a ≤ d`, not all three even, obeying the toric alternative
on every odd-`gcd` pair. Only the four `r = 0` boundary triples survive. -/
theorem near_saturated_power_triples_odd {a b c : ℕ}
    (ha_le : a ≤ d) (hba : b ≤ a) (hcb : c ≤ b) (hc : 1 ≤ c)
    (hsum_lo : d - 5 ≤ a + b + c) (hsum_hi : a + b + c ≤ d + 4)
    (hnot_even : a % 2 = 1 ∨ b % 2 = 1 ∨ c % 2 = 1)
    (hab : a % 2 = 1 ∨ b % 2 = 1 →
      (∃ r, a + b = 2 ^ r) ∨ (b ≤ 4 ∧ ∃ r, a - b = 2 ^ r))
    (hac : a % 2 = 1 ∨ c % 2 = 1 →
      (∃ r, a + c = 2 ^ r) ∨ (c ≤ 4 ∧ ∃ r, a - c = 2 ^ r)) :
    (a = 67108865 ∧ b = 67108863 ∧ c = 1) ∨
    (a = 67108867 ∧ b = 67108861 ∧ c = 3) ∨
    (a = 134217727 ∧ b = 1 ∧ c = 1) ∨
    (a = 134217725 ∧ b = 3 ∧ c = 3) := by
  simp only [d] at *
  by_cases ha_odd : a % 2 = 1
  · have hb_alt := hab (.inl ha_odd)
    have hc_alt := hac (.inl ha_odd)
    rcases hb_alt with hb_add | ⟨hb4, hb_sub⟩
    · have hb_val := pow_two_in_band (by omega) (by omega) hb_add
      rcases hc_alt with hc_add | ⟨hc4, hc_sub⟩
      · have hc_val := pow_two_in_band (by omega) (by omega) hc_add
        rcases hb_val with h1 | h1 <;> rcases hc_val with h2 | h2
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · have hc13 : c = 1 ∨ c = 3 := by omega
          rcases hc13 with rfl | rfl
          · right; right; left; omega
          · right; right; right; omega
      · have hc_val := pow_two_in_band (by omega) (by omega) hc_sub
        rcases hb_val with h1 | h1 <;> rcases hc_val with h2 | h2
        · exfalso; omega
        · exfalso; omega
        · have hc13 : c = 1 ∨ c = 3 := by omega
          rcases hc13 with rfl | rfl
          · left; omega
          · right; left; omega
        · exfalso; omega
    · exfalso
      have hb_val := pow_two_in_band (by omega) (by omega) hb_sub
      rcases hb_val with h1 | h1 <;> omega
  · exfalso
    have ha_even : a % 2 = 0 := by omega
    rcases hnot_even with h | hb_odd | hc_odd
    · omega
    · rcases hab (.inr hb_odd) with h | ⟨_, h⟩
      · exact odd_gt_one_not_pow_two (by omega) (by omega) h
      · exact odd_gt_one_not_pow_two (by omega) (by omega) h
    · rcases hac (.inr hc_odd) with h | ⟨_, h⟩
      · exact odd_gt_one_not_pow_two (by omega) (by omega) h
      · exact odd_gt_one_not_pow_two (by omega) (by omega) h

/-- Complete classification when `2 ∣ a, b, c` but `¬ (4 ∣ a ∧ 4 ∣ b ∧ 4 ∣ c)`, applying
the toric alternative on `H²`. Only the two `r = 1` boundary triples survive. -/
theorem near_saturated_power_triples_even {a b c : ℕ}
    (ha_le : a ≤ d) (hba : b ≤ a) (hcb : c ≤ b) (hc : 1 ≤ c)
    (hsum_lo : d - 5 ≤ a + b + c) (hsum_hi : a + b + c ≤ d + 4)
    (heven : a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0)
    (hnot4 : (a / 2) % 2 = 1 ∨ (b / 2) % 2 = 1 ∨ (c / 2) % 2 = 1)
    (hab : (a / 2) % 2 = 1 ∨ (b / 2) % 2 = 1 →
      (∃ r, a / 2 + b / 2 = 2 ^ r) ∨ (b / 2 ≤ 2 ∧ ∃ r, a / 2 - b / 2 = 2 ^ r))
    (hac : (a / 2) % 2 = 1 ∨ (c / 2) % 2 = 1 →
      (∃ r, a / 2 + c / 2 = 2 ^ r) ∨ (c / 2 ≤ 2 ∧ ∃ r, a / 2 - c / 2 = 2 ^ r)) :
    (a = 67108866 ∧ b = 67108862 ∧ c = 2) ∨
    (a = 134217726 ∧ b = 2 ∧ c = 2) := by
  simp only [d] at *
  set a' := a / 2
  set b' := b / 2
  set c' := c / 2
  have ha2 : a = 2 * a' := by omega
  have hb2 : b = 2 * b' := by omega
  have hc2 : c = 2 * c' := by omega
  by_cases ha_odd : a' % 2 = 1
  · have hb_alt := hab (.inl ha_odd)
    have hc_alt := hac (.inl ha_odd)
    rcases hb_alt with hb_add | ⟨hb2', hb_sub⟩
    · have hb_val := pow_two_in_band_H2 (by omega) (by omega) hb_add
      rcases hc_alt with hc_add | ⟨hc2', hc_sub⟩
      · have hc_val := pow_two_in_band_H2 (by omega) (by omega) hc_add
        rcases hb_val with h1 | h1 <;> rcases hc_val with h2 | h2
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · right; omega
      · have hc_val := pow_two_in_band_H2 (by omega) (by omega) hc_sub
        rcases hb_val with h1 | h1 <;> rcases hc_val with h2 | h2
        · exfalso; omega
        · exfalso; omega
        · left; omega
        · exfalso; omega
    · exfalso
      have hb_val := pow_two_in_band_H2 (by omega) (by omega) hb_sub
      rcases hb_val with h1 | h1 <;> omega
  · exfalso
    rcases hnot4 with h | hb_odd | hc_odd
    · omega
    · rcases hab (.inr hb_odd) with h | ⟨_, h⟩
      · exact odd_gt_one_not_pow_two (by omega) (by omega) h
      · exact odd_gt_one_not_pow_two (by omega) (by omega) h
    · rcases hac (.inr hc_odd) with h | ⟨_, h⟩
      · exact odd_gt_one_not_pow_two (by omega) (by omega) h
      · exact odd_gt_one_not_pow_two (by omega) (by omega) h

/-- Combined classification: if three positive power-slope degrees `(a, b, c)` with
`a ≥ b ≥ c ≥ 1`, `a ≤ d`, `d - 5 ≤ a + b + c ≤ d + 4` are not all divisible by `4`,
and obey the cyclic Möbius toric alternative on `H` (when not all even) or `H²` (when all
even), then `(a, b, c)` is one of the six boundary triples in Families I and II. -/
theorem near_saturated_power_triples {a b c : ℕ}
    (ha_le : a ≤ d) (hba : b ≤ a) (hcb : c ≤ b) (hc : 1 ≤ c)
    (hsum_lo : d - 5 ≤ a + b + c) (hsum_hi : a + b + c ≤ d + 4)
    (hnot4 : ¬ (4 ∣ a ∧ 4 ∣ b ∧ 4 ∣ c))
    (hab_odd : a % 2 = 1 ∨ b % 2 = 1 →
      (∃ r, a + b = 2 ^ r) ∨ (b ≤ 4 ∧ ∃ r, a - b = 2 ^ r))
    (hac_odd : a % 2 = 1 ∨ c % 2 = 1 →
      (∃ r, a + c = 2 ^ r) ∨ (c ≤ 4 ∧ ∃ r, a - c = 2 ^ r))
    (hab_even : a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 →
      (a / 2) % 2 = 1 ∨ (b / 2) % 2 = 1 →
      (∃ r, a / 2 + b / 2 = 2 ^ r) ∨ (b / 2 ≤ 2 ∧ ∃ r, a / 2 - b / 2 = 2 ^ r))
    (hac_even : a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 →
      (a / 2) % 2 = 1 ∨ (c / 2) % 2 = 1 →
      (∃ r, a / 2 + c / 2 = 2 ^ r) ∨ (c / 2 ≤ 2 ∧ ∃ r, a / 2 - c / 2 = 2 ^ r)) :
    (∃ kk : ℕ, 1 ≤ kk ∧ kk ≤ 3 ∧ a = 67108864 + kk ∧ b = 67108864 - kk ∧ c = kk) ∨
    (∃ kk : ℕ, 1 ≤ kk ∧ kk ≤ 3 ∧ a = 134217728 - kk ∧ b = kk ∧ c = kk) := by
  by_cases hall_even : a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0
  · have hnot4' : (a / 2) % 2 = 1 ∨ (b / 2) % 2 = 1 ∨ (c / 2) % 2 = 1 := by
      by_contra h
      apply hnot4
      omega
    rcases near_saturated_power_triples_even ha_le hba hcb hc hsum_lo hsum_hi hall_even hnot4'
        (hab_even hall_even) (hac_even hall_even) with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨2, by omega, by omega, rfl, rfl, rfl⟩
    · exact Or.inr ⟨2, by omega, by omega, rfl, rfl, rfl⟩
  · have hnot_even : a % 2 = 1 ∨ b % 2 = 1 ∨ c % 2 = 1 := by omega
    rcases near_saturated_power_triples_odd ha_le hba hcb hc hsum_lo hsum_hi hnot_even
        hab_odd hac_odd with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨1, by omega, by omega, rfl, rfl, rfl⟩
    · exact Or.inl ⟨3, by omega, by omega, rfl, rfl, rfl⟩
    · exact Or.inr ⟨1, by omega, by omega, rfl, rfl, rfl⟩
    · exact Or.inr ⟨3, by omega, by omega, rfl, rfl, rfl⟩

/-! ## Section 4: Polynomial coset-sparsity refutation of Families I and II -/

section CosetSparsity

variable {F : Type*} [Field F] [DecidableEq F]

/-- Counting roots of a polynomial inside a finite set `S` by its degree. -/
private lemma card_filter_eval_eq_zero_le {P : F[X]} (hP : P ≠ 0) (S : Finset F) :
    (S.filter fun x => P.eval x = 0).card ≤ P.natDegree := by
  have hsub : S.filter (fun x => P.eval x = 0) ⊆ P.roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr ((mem_roots hP).mpr (mem_filter.mp hx).2)
  exact (card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans (card_roots' P))

/-- **Family II coset-sparsity obstruction** (`(2^27 - k, k, k)` for `k ∈ {1, 2, 3}`):
If `X^k * L₀₂ * R = L₀₁ * R + (C lam - X^Q) * U` with `L₀₁ ≠ 0`, `R ≠ 0`, and
`U = 0 ∨ U.natDegree < R.natDegree`, then on every coset `X^Q = ω` (`ω ∈ Ω`), the specialized
polynomial `L₀₁ * R + C (lam - ω) * U` is nonzero of degree at most `L₀₁.natDegree + R.natDegree`.
Consequently `L₀₂` has at most `Ω.card * (L₀₁.natDegree + R.natDegree)` roots in `H`.
For `Ω.card = 8`, `L₀₁.natDegree ≤ 2`, `R.natDegree ≤ 8`, this caps `e₀₂ ≤ 80`, contradicting
`e₀₂ ≥ 134,217,712`. -/
theorem family_two_coset_obstruction
    (H Ω : Finset F) (Q kk : ℕ) (lam : F)
    (hH_pow : ∀ x ∈ H, x ^ Q ∈ Ω)
    (L₀₁ L₀₂ R U : F[X])
    (hL01 : L₀₁ ≠ 0)
    (hR : R ≠ 0)
    (hU : U = 0 ∨ U.natDegree < R.natDegree)
    (heq : X ^ kk * L₀₂ * R = L₀₁ * R + (C lam - X ^ Q) * U) :
    (H.filter fun x => L₀₂.eval x = 0).card ≤
      Ω.card * (L₀₁.natDegree + R.natDegree) := by
  classical
  let fiber (ω : F) : Finset F := (H.filter fun x => L₀₂.eval x = 0).filter fun x => x ^ Q = ω
  have hcover : (H.filter fun x => L₀₂.eval x = 0) ⊆ Ω.biUnion fiber := by
    intro x hx
    exact mem_biUnion.mpr ⟨x ^ Q, hH_pow x (mem_filter.mp hx).1, mem_filter.mpr ⟨hx, rfl⟩⟩
  have hfiber (ω : F) : (fiber ω).card ≤ L₀₁.natDegree + R.natDegree := by
    let P := L₀₁ * R + C (lam - ω) * U
    have hdegLR : (L₀₁ * R).natDegree = L₀₁.natDegree + R.natDegree := natDegree_mul hL01 hR
    have hdegU : U = 0 ∨ (C (lam - ω) * U).natDegree < (L₀₁ * R).natDegree := by
      rcases hU with rfl | hlt
      · exact Or.inl rfl
      · right
        have h1 : (C (lam - ω) * U).natDegree ≤ U.natDegree := natDegree_C_mul_le _ _
        omega
    have hPne : P ≠ 0 := by
      intro h0
      have heq' : L₀₁ * R = -(C (lam - ω) * U) := eq_neg_of_add_eq_zero_left h0
      rcases hdegU with rfl | hlt
      · simp at heq'
        exact heq'.elim hL01 hR
      · have hd := congrArg Polynomial.natDegree heq'
        rw [natDegree_neg] at hd
        omega
    have hPdeg : P.natDegree ≤ L₀₁.natDegree + R.natDegree := by
      apply (natDegree_add_le _ _).trans (max_le hdegLR.le ?_)
      rcases hdegU with rfl | hlt
      · simp
      · omega
    have hvan : ∀ x ∈ fiber ω, P.eval x = 0 := by
      intro x hx
      have hL2 : L₀₂.eval x = 0 := (mem_filter.mp (mem_filter.mp hx).1).2
      have hpow : x ^ Q = ω := (mem_filter.mp hx).2
      have hv := congrArg (Polynomial.eval x) heq
      simp only [eval_mul, eval_add, eval_sub, eval_pow, eval_X, eval_C, hL2, hpow,
        mul_zero, zero_mul] at hv
      simpa [P, eval_add, eval_mul, eval_C] using hv.symm
    have hsub : fiber ω ⊆ (fiber ω).filter (fun x => P.eval x = 0) :=
      fun x hx => mem_filter.mpr ⟨hx, hvan x hx⟩
    exact (card_le_card hsub).trans ((card_filter_eval_eq_zero_le hPne (fiber ω)).trans hPdeg)
  calc
    (H.filter fun x => L₀₂.eval x = 0).card ≤ (Ω.biUnion fiber).card := card_le_card hcover
    _ ≤ ∑ ω ∈ Ω, (fiber ω).card := card_biUnion_le
    _ ≤ ∑ _ω ∈ Ω, (L₀₁.natDegree + R.natDegree) := sum_le_sum fun ω _ => hfiber ω
    _ = Ω.card * (L₀₁.natDegree + R.natDegree) := by simp

omit [DecidableEq F] in
/-- Split any polynomial `P` at exponent `M` into `P = A + X^M * B` where `A` is supported on
`< M` and `B.coeff j = P.coeff (j + M)`. -/
private lemma split_poly_at (P : F[X]) (M : ℕ) :
    ∃ A B : F[X], (∀ j, M ≤ j → A.coeff j = 0) ∧
      (∀ j, B.coeff j = P.coeff (j + M)) ∧ P = A + X ^ M * B := by
  classical
  let A : F[X] := ∑ j ∈ range M, monomial j (P.coeff j)
  let B : F[X] := ∑ j ∈ range (P.natDegree + 1), monomial j (P.coeff (j + M))
  have hAcoeff (j : ℕ) : A.coeff j = if j < M then P.coeff j else 0 := by
    simp only [A, finsetSum_coeff, coeff_monomial]
    by_cases hj : j < M
    · simp only [hj, ↓reduceIte]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi; simp [hi]
      · intro hnot; exact absurd (mem_range.mpr hj) hnot
    · simp only [hj, ↓reduceIte]
      rw [Finset.sum_eq_zero]
      intro i hi; simp only [mem_range] at hi; simp [show i ≠ j by omega]
  have hBcoeff (j : ℕ) : B.coeff j = P.coeff (j + M) := by
    simp only [B, finsetSum_coeff, coeff_monomial]
    by_cases hj : j < P.natDegree + 1
    · rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi; simp [hi]
      · intro hnot; exact absurd (mem_range.mpr hj) hnot
    · rw [Finset.sum_eq_zero]
      · symm; exact coeff_eq_zero_of_natDegree_lt (by omega)
      · intro i hi; simp only [mem_range] at hi; simp [show i ≠ j by omega]
  refine ⟨A, B, fun j hj => by rw [hAcoeff]; simp [show ¬ j < M by omega], hBcoeff, ?_⟩
  ext j
  rw [coeff_add, hAcoeff, coeff_X_pow_mul']
  by_cases hj : j < M
  · simp [hj, show ¬ M ≤ j by omega]
  · simp [hj, show M ≤ j by omega, hBcoeff, Nat.sub_add_cancel (by omega : M ≤ j)]

/-- **Family I coset-sparsity obstruction** (`(2^26 + k, 2^26 - k, k)` for `k ∈ {1, 2, 3}`):
Suppose `(L₀₁ - X^{Q-k} * L₀₂) * R = (X^{2Q} - C lam) * U` with `L₀₁ ≠ 0`, `R ≠ 0`, `lam ≠ 0`,
`deg L₀₁ ≤ Q - 1 - k`, `deg L₀₂ ≤ Q - 1 + k`, `deg R + k < Q`, and `R` has at least
`R.natDegree` roots in `H` (e.g. `R` is squarefree and splits in `H`). If `L₀₁` has more than
`Ω.card * (k + R.natDegree)` roots in `H`, then there exists `ω₀ ∈ Ω` such that `L₀₁` and `L₀₂`
simultaneously vanish at every point of the coset `x^Q = ω₀` in `H` outside the roots of `R`,
forcing at least `Q - R.natDegree` common roots of `L₀₁` and `L₀₂` in `H`.
For `Q = 2^26`, `Ω.card = 16`, `k ≤ 3`, `R.natDegree ≤ 8`, this forces `≥ 67,108,856` common
roots, contradicting `y₃ + x₄ ≤ 8`. -/
theorem family_one_coset_obstruction
    (H Ω : Finset F) (Q kk : ℕ) (lam : F)
    (hH_ne : ∀ x ∈ H, x ≠ 0)
    (hH_pow : ∀ x ∈ H, x ^ Q ∈ Ω)
    (hfiber_lo : ∀ ω ∈ Ω, Q ≤ (H.filter fun x => x ^ Q = ω).card)
    (L₀₁ L₀₂ R U : F[X])
    (hL01 : L₀₁ ≠ 0) (hR : R ≠ 0) (hlam : lam ≠ 0)
    (hdegL01 : L₀₁.natDegree + kk + 1 ≤ Q)
    (hdegL02 : L₀₂.natDegree + 1 ≤ Q + kk)
    (hdegR : R.natDegree + kk < Q)
    (hR_roots : R.natDegree ≤ (H.filter fun x => R.eval x = 0).card)
    (heq : (L₀₁ - X ^ (Q - kk) * L₀₂) * R = (X ^ (2 * Q) - C lam) * U)
    (hL01_many : Ω.card * (kk + R.natDegree) < (H.filter fun x => L₀₁.eval x = 0).card) :
    Q - R.natDegree ≤ (H.filter fun x => L₀₁.eval x = 0 ∧ L₀₂.eval x = 0).card := by
  classical
  -- Step 1: `U ≠ 0` and `U.natDegree < R.natDegree`.
  have hU_ne : U ≠ 0 := by
    intro hU0
    rw [hU0, mul_zero] at heq
    have hsub0 : L₀₁ - X ^ (Q - kk) * L₀₂ = 0 := (mul_eq_zero.mp heq).resolve_right hR
    have hL12 : L₀₁ = X ^ (Q - kk) * L₀₂ := sub_eq_zero.mp hsub0
    have hL02_ne : L₀₂ ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hL12; exact hL01 hL12
    have hdeg := congrArg Polynomial.natDegree hL12
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hL02_ne, natDegree_X_pow] at hdeg
    omega
  have hQ_pos : 0 < Q := by omega
  have hX2Q_deg : (X ^ (2 * Q) - C lam : F[X]).natDegree = 2 * Q := by
    rw [natDegree_sub_C, natDegree_X_pow]
  have hX2Q_ne : (X ^ (2 * Q) - C lam : F[X]) ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hX2Q_deg; omega
  have hU_lt_R : U.natDegree < R.natDegree := by
    have hLHS_deg : ((L₀₁ - X ^ (Q - kk) * L₀₂) * R).natDegree ≤ 2 * Q - 1 + R.natDegree := by
      have h1 : (X ^ (Q - kk) * L₀₂).natDegree ≤ 2 * Q - 1 := by
        apply natDegree_mul_le.trans
        rw [natDegree_X_pow]; omega
      have h2 : (L₀₁ - X ^ (Q - kk) * L₀₂).natDegree ≤ 2 * Q - 1 :=
        (natDegree_sub_le _ _).trans (max_le (by omega) h1)
      exact natDegree_mul_le.trans (by omega)
    have hRHS_deg : ((X ^ (2 * Q) - C lam) * U).natDegree = 2 * Q + U.natDegree := by
      rw [natDegree_mul hX2Q_ne hU_ne, hX2Q_deg]
    rw [heq, hRHS_deg] at hLHS_deg
    omega
  -- Step 2: Split `L₀₁ * R` at `Q - kk` to isolate `B` with `B.natDegree < R.natDegree`.
  obtain ⟨A, B, hA_hi, hB_coeff, hsplit⟩ := split_poly_at (L₀₁ * R) (Q - kk)
  have hpow_add : X ^ (Q - kk) * X ^ (Q + kk) = (X ^ (2 * Q) : F[X]) := by
    rw [← pow_add]; congr 1; omega
  have hrearr : A + C lam * U = X ^ (Q - kk) * (L₀₂ * R + X ^ (Q + kk) * U - B) := by
    have h1 : (L₀₁ * R) + C lam * U = X ^ (Q - kk) * (L₀₂ * R + X ^ (Q + kk) * U) := by
      calc
        L₀₁ * R + C lam * U = (L₀₁ - X ^ (Q - kk) * L₀₂) * R + X ^ (Q - kk) * L₀₂ * R + C lam * U := by ring
        _ = (X ^ (2 * Q) - C lam) * U + X ^ (Q - kk) * L₀₂ * R + C lam * U := by rw [heq]
        _ = X ^ (Q - kk) * L₀₂ * R + X ^ (2 * Q) * U := by ring
        _ = X ^ (Q - kk) * L₀₂ * R + (X ^ (Q - kk) * X ^ (Q + kk)) * U := by rw [hpow_add]
        _ = X ^ (Q - kk) * (L₀₂ * R + X ^ (Q + kk) * U) := by ring
    rw [hsplit] at h1
    linear_combination h1
  have hA_eq : A + C lam * U = 0 := by
    ext j
    rw [coeff_zero]
    by_cases hj : j < Q - kk
    · rw [hrearr, coeff_X_pow_mul']; simp [show ¬ Q - kk ≤ j by omega]
    · rw [coeff_add, hA_hi j (by omega), zero_add]
      apply coeff_eq_zero_of_natDegree_lt
      exact (natDegree_C_mul_le lam U).trans_lt (by omega)
  have hB_eq : L₀₂ * R + X ^ (Q + kk) * U - B = 0 := by
    rw [hA_eq] at hrearr
    exact (mul_eq_zero.mp hrearr.symm).resolve_left (pow_ne_zero _ X_ne_zero)
  have hL01_eq : L₀₁ * R = X ^ (Q - kk) * B - C lam * U := by
    have hA' : A = -(C lam * U) := eq_neg_of_add_eq_zero_left hA_eq
    rw [hsplit, hA']; ring
  have hL02_eq : L₀₂ * R = B - X ^ (Q + kk) * U := by
    linear_combination hB_eq
  have hB_ne : B ≠ 0 := by
    intro hB0
    rw [hB0, mul_zero, zero_sub] at hL01_eq
    have hd := congrArg Polynomial.natDegree hL01_eq
    rw [natDegree_mul hL01 hR, natDegree_neg] at hd
    have hcu : (C lam * U).natDegree ≤ U.natDegree := natDegree_C_mul_le _ _
    omega
  have hB_lt_R : B.natDegree < R.natDegree := by
    apply (natDegree_lt_iff_degree_lt hB_ne).mpr
    rw [degree_lt_iff_coeff_zero]
    intro j hj
    rw [hB_coeff]
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_mul hL01 hR]
    omega
  -- Step 3: Coset counting for `L₀₁` forces a unique `ω₀ ∈ Ω` with `C ω₀ * B = C lam * X^kk * U`.
  have hpow_Q : X ^ kk * X ^ (Q - kk) = (X ^ Q : F[X]) := by
    rw [← pow_add]; congr 1; omega
  have hmul_Xk : X ^ kk * (L₀₁ * R) = X ^ Q * B - C lam * X ^ kk * U := by
    calc
      X ^ kk * (L₀₁ * R) = X ^ kk * (X ^ (Q - kk) * B - C lam * U) := by rw [hL01_eq]
      _ = (X ^ kk * X ^ (Q - kk)) * B - C lam * X ^ kk * U := by ring
      _ = X ^ Q * B - C lam * X ^ kk * U := by rw [hpow_Q]
  have hex_omega : ∃ ω₀ ∈ Ω, C ω₀ * B - C lam * X ^ kk * U = 0 := by
    by_contra hall_ne
    push Not at hall_ne
    let fiber (ω : F) : Finset F :=
      (H.filter fun x => L₀₁.eval x = 0).filter fun x => x ^ Q = ω
    have hcover : (H.filter fun x => L₀₁.eval x = 0) ⊆ Ω.biUnion fiber := by
      intro x hx
      exact mem_biUnion.mpr ⟨x ^ Q, hH_pow x (mem_filter.mp hx).1, mem_filter.mpr ⟨hx, rfl⟩⟩
    have hfiber (ω : F) (hω : ω ∈ Ω) : (fiber ω).card ≤ kk + R.natDegree := by
      let P := C ω * B - C lam * X ^ kk * U
      have hPne : P ≠ 0 := hall_ne ω hω
      have hPdeg : P.natDegree ≤ kk + R.natDegree := by
        apply (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · exact (natDegree_C_mul_le _ _).trans (by omega)
        · have h1 : (C lam * X ^ kk).natDegree ≤ kk := natDegree_C_mul_X_pow_le lam kk
          exact natDegree_mul_le.trans (by omega)
      have hvan : ∀ x ∈ fiber ω, P.eval x = 0 := by
        intro x hx
        have hL1 : L₀₁.eval x = 0 := (mem_filter.mp (mem_filter.mp hx).1).2
        have hpow : x ^ Q = ω := (mem_filter.mp hx).2
        have hv := congrArg (Polynomial.eval x) hmul_Xk
        simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, hL1, hpow,
          zero_mul, mul_zero] at hv
        simpa [P, eval_sub, eval_mul, eval_pow, eval_X, eval_C] using hv.symm
      have hsub : fiber ω ⊆ (fiber ω).filter (fun x => P.eval x = 0) :=
        fun x hx => mem_filter.mpr ⟨hx, hvan x hx⟩
      exact (card_le_card hsub).trans ((card_filter_eval_eq_zero_le hPne (fiber ω)).trans hPdeg)
    have hcard_le : (H.filter fun x => L₀₁.eval x = 0).card ≤ Ω.card * (kk + R.natDegree) := by
      calc
        (H.filter fun x => L₀₁.eval x = 0).card ≤ (Ω.biUnion fiber).card := card_le_card hcover
        _ ≤ ∑ ω ∈ Ω, (fiber ω).card := card_biUnion_le
        _ ≤ ∑ _ω ∈ Ω, (kk + R.natDegree) := sum_le_sum fun ω hω => hfiber ω hω
        _ = Ω.card * (kk + R.natDegree) := by simp
    omega
  obtain ⟨ω₀, hω₀_mem, hrel0⟩ := hex_omega
  have hrel : C ω₀ * B = C lam * X ^ kk * U := sub_eq_zero.mp hrel0
  have hω₀_ne : ω₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hrel
    have hCU_ne : C lam * X ^ kk * U ≠ 0 :=
      mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hlam) (pow_ne_zero _ X_ne_zero)) hU_ne
    exact hCU_ne hrel.symm
  -- Step 4: Substitute `B = C (lam * ω₀⁻¹) * X^kk * U` into both `L₀₁ * R` and `L₀₂ * R`.
  have hB_sub : B = C (lam * ω₀⁻¹) * X ^ kk * U := by
    have h1 : C ω₀⁻¹ * (C ω₀ * B) = C ω₀⁻¹ * (C lam * X ^ kk * U) :=
      congrArg (C ω₀⁻¹ * ·) hrel
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hω₀_ne, map_one, one_mul] at h1
    rw [h1, C_mul]; ring
  have hL01_fac : L₀₁ * R = C (lam * ω₀⁻¹) * (X ^ Q - C ω₀) * U := by
    have hlam_eq : lam * ω₀⁻¹ * ω₀ = lam := by
      rw [mul_assoc, inv_mul_cancel₀ hω₀_ne, mul_one]
    calc
      L₀₁ * R = X ^ (Q - kk) * (C (lam * ω₀⁻¹) * X ^ kk * U) - C lam * U := by
        rw [hL01_eq, hB_sub]
      _ = C (lam * ω₀⁻¹) * (X ^ kk * X ^ (Q - kk)) * U - C (lam * ω₀⁻¹) * C ω₀ * U := by
        rw [← C_mul, hlam_eq]; ring
      _ = C (lam * ω₀⁻¹) * (X ^ Q - C ω₀) * U := by rw [hpow_Q]; ring
  have hL02_fac : L₀₂ * R = -C ω₀⁻¹ * X ^ kk * (C ω₀ * X ^ Q - C lam) * U := by
    have hpow_Q2 : X ^ kk * X ^ Q = (X ^ (Q + kk) : F[X]) := by
      rw [← pow_add]; congr 1; omega
    calc
      L₀₂ * R = C (lam * ω₀⁻¹) * X ^ kk * U - X ^ (Q + kk) * U := by rw [hL02_eq, hB_sub]
      _ = C (lam * ω₀⁻¹) * X ^ kk * U - (X ^ kk * X ^ Q) * U := by rw [hpow_Q2]
      _ = C ω₀⁻¹ * C lam * X ^ kk * U - (C ω₀⁻¹ * C ω₀) * X ^ kk * X ^ Q * U := by
        rw [← C_mul, ← C_mul, inv_mul_cancel₀ hω₀_ne, map_one, one_mul, mul_comm lam ω₀⁻¹]
      _ = -C ω₀⁻¹ * X ^ kk * (C ω₀ * X ^ Q - C lam) * U := by ring
  -- Step 5: Pick a root `r₀ ∈ H` of `R` with `U.eval r₀ ≠ 0` to deduce `ω₀ ^ 2 = lam`.
  have hex_r0 : ∃ r₀ ∈ H, R.eval r₀ = 0 ∧ U.eval r₀ ≠ 0 := by
    by_contra hno
    push Not at hno
    have hsub : (H.filter fun x => R.eval x = 0) ⊆ H.filter fun x => U.eval x = 0 := by
      intro x hx
      obtain ⟨hxH, hxR⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hxH, hno x hxH hxR⟩
    have h1 := (hR_roots.trans (card_le_card hsub)).trans (card_filter_eval_eq_zero_le hU_ne H)
    omega
  obtain ⟨r₀, hr₀_H, hr₀_R, hr₀_U⟩ := hex_r0
  have hr₀_ne : r₀ ≠ 0 := hH_ne r₀ hr₀_H
  have hr₀_pow : r₀ ^ Q = ω₀ := by
    have hv := congrArg (Polynomial.eval r₀) hL01_fac
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, hr₀_R, mul_zero] at hv
    have hfac_ne : lam * ω₀⁻¹ ≠ 0 := mul_ne_zero hlam (inv_ne_zero hω₀_ne)
    have hsub0 : r₀ ^ Q - ω₀ = 0 := by
      have h1 := (mul_eq_zero.mp hv.symm).resolve_right hr₀_U
      exact (mul_eq_zero.mp h1).resolve_left hfac_ne
    exact sub_eq_zero.mp hsub0
  have hlam_sq : ω₀ * ω₀ = lam := by
    have hv := congrArg (Polynomial.eval r₀) hL02_fac
    simp only [eval_mul, eval_neg, eval_sub, eval_pow, eval_X, eval_C, hr₀_R, hr₀_pow,
      mul_zero] at hv
    have hfac_ne : -(ω₀⁻¹) * r₀ ^ kk ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hω₀_ne)) (pow_ne_zero _ hr₀_ne)
    have hsub0 : ω₀ * ω₀ - lam = 0 := by
      have h1 := (mul_eq_zero.mp hv.symm).resolve_right hr₀_U
      exact (mul_eq_zero.mp h1).resolve_left hfac_ne
    exact sub_eq_zero.mp hsub0
  -- Step 6: Every `x ∈ H` with `x^Q = ω₀` and `R.eval x ≠ 0` is a common root of `L₀₁` and `L₀₂`.
  let S_coset := H.filter fun x => x ^ Q = ω₀
  let S_bad := S_coset.filter fun x => R.eval x = 0
  let S_good := S_coset \ S_bad
  have hgood_sub : S_good ⊆ H.filter fun x => L₀₁.eval x = 0 ∧ L₀₂.eval x = 0 := by
    intro x hx
    obtain ⟨hxc, hxnot⟩ := mem_sdiff.mp hx
    have hxR : R.eval x ≠ 0 := fun h0 => hxnot (mem_filter.mpr ⟨hxc, h0⟩)
    obtain ⟨hxH, hxpow⟩ := mem_filter.mp hxc
    refine mem_filter.mpr ⟨hxH, ?_, ?_⟩
    · have hv := congrArg (Polynomial.eval x) hL01_fac
      simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, hxpow, sub_self,
        mul_zero, zero_mul] at hv
      exact (mul_eq_zero.mp hv).resolve_right hxR
    · have hv := congrArg (Polynomial.eval x) hL02_fac
      simp only [eval_mul, eval_neg, eval_sub, eval_pow, eval_X, eval_C, hxpow, hlam_sq,
        sub_self, mul_zero, zero_mul] at hv
      exact (mul_eq_zero.mp hv).resolve_right hxR
  have hbad_le : S_bad.card ≤ R.natDegree :=
    card_filter_eval_eq_zero_le hR S_coset
  have hpart : S_good.card + S_bad.card = S_coset.card :=
    card_sdiff_add_card_eq_card (filter_subset _ S_coset)
  have hcoset_lo : Q ≤ S_coset.card := hfiber_lo ω₀ hω₀_mem
  have hgood_lo : Q - R.natDegree ≤ S_good.card := by omega
  exact hgood_lo.trans (card_le_card hgood_sub)

/-- Concrete arithmetic contradictions closing Families I and II at `n = 2^30`, `d = 2^27 - 1`. -/
theorem family_one_and_two_concrete_contradictions :
    (∀ (e₀₁ common Rdeg kk : ℕ), 67108848 ≤ e₀₁ → kk ≤ 3 → Rdeg ≤ 8 → common ≤ 8 →
      (16 * (kk + Rdeg) < e₀₁ ∧ 67108864 - Rdeg ≤ common → False)) ∧
    (∀ (e₀₂ L01deg Rdeg : ℕ), 134217712 ≤ e₀₂ → L01deg ≤ 2 → Rdeg ≤ 8 →
      (e₀₂ ≤ 8 * (L01deg + Rdeg) → False)) := by
  constructor <;> intros <;> omega

end CosetSparsity

/-! ## Section 5: Nonscalar antipode exact saturation & one-power companion floor (`0 ≤ s ≤ 4`) -/

/-- In the nonscalar antipode (`r = 0, s = 4, d' = 2^26 - 1 = 67,108,863`), the four lifted
quotient triangle determinants of degree `2 * d'` on `H²` have combined root budget at most
`16 * d' = 8 * d - 8`. Matching `x₂ + 2 * x₃ + 3 * x₄ + 4 = 4 * d + x₀` forces zero uncovered,
triple, or quadruple sites (`x₀ = x₃ = x₄ = 0`) and exact saturation `x₂ = 8 * d'` on `H²`. -/
theorem nonscalar_antipode_exact_saturation {x₀ x₂ x₃ x₄ : ℕ}
    (hinc : x₂ + 2 * x₃ + 3 * x₄ + 4 = 4 * d + x₀)
    (htri_quot : 2 * x₂ + 5 * x₃ + 8 * x₄ ≤ 16 * 67108863) :
    x₀ = 0 ∧ x₃ = 0 ∧ x₄ = 0 ∧ x₂ = 8 * 67108863 := by
  simp only [d] at *
  omega

/-- Direct `H`-branch companion degree floor for one Möbius-of-power slope plus two arbitrary
companions across all `0 ≤ s ≤ 4`: since `m₁ + m₂ + m₃ ≥ d - 5` and each pair loses at most
`8` sites, a companion obeying the multiplicative translation bound on `H` has
`hit ≥ d - 13 - B` and forces `7,479,697 ≤ B`. -/
theorem eighth_near_saturated_companion_direct {B hit : ℕ}
    (hsum : d - 13 ≤ hit + B)
    (hhits : hit * hit ≤ hit + (n - 1) * (2 * B)) :
    7479697 ≤ B := by
  by_contra! hsmall
  simp only [d, n] at *
  have hlo : 126738018 ≤ hit := by omega
  have hmul := Nat.mul_le_mul hlo (by omega : 126738017 ≤ hit - 1)
  have hsub : hit * (hit - 1) + hit = hit * hit := by cases hit <;> simp [Nat.mul_succ]
  omega

/-- Quotient `H²`-branch companion degree floor: when both companions fail the translation
bound on `H` with `a` odd, the quartet enters the nonscalar antipode (`s = 4`), whose
quotient on `H²` (`|H²| = 2^29`, `d' = 2^26 - 1`) is exactly saturated. A companion downstairs
of degree at most `B'` (with `2 * B' ≤ B + 1`) satisfies `hit' ≥ d' - B'` and forces
`3,739,849 ≤ B'`, hence again `7,479,697 ≤ B`. -/
theorem eighth_near_saturated_companion_quotient {B B' hit' : ℕ}
    (hdeg : 2 * B' ≤ B + 1)
    (hsum : 67108863 ≤ hit' + B')
    (hhits : hit' * hit' ≤ hit' + (n / 2 - 1) * (2 * B')) :
    3739849 ≤ B' ∧ 7479697 ≤ B := by
  have hBp : 3739849 ≤ B' := by
    by_contra! hsmall
    simp only [n] at *
    have hlo : 63369015 ≤ hit' := by omega
    have hmul := Nat.mul_le_mul hlo (by omega : 63369014 ≤ hit' - 1)
    have hsub : hit' * (hit' - 1) + hit' = hit' * hit' := by cases hit' <;> simp [Nat.mul_succ]
    omega
  exact ⟨hBp, by omega⟩

/-- Unified companion degree floor across all five open profiles `(1,1,1,1)` through `(1,1,1,5)`
(`0 ≤ s ≤ 4`): whether one companion obeys the translation bound directly on `H` or both fail
and descend to the exactly saturated nonscalar-antipode quotient on `H²`, the larger companion
has degree at least `7,479,697`. -/
theorem eighth_near_saturated_companion {B : ℕ}
    (hbranch :
      (∃ hit : ℕ, d - 13 ≤ hit + B ∧ hit * hit ≤ hit + (n - 1) * (2 * B)) ∨
      (∃ B' hit' : ℕ, 2 * B' ≤ B + 1 ∧ 67108863 ≤ hit' + B' ∧
        hit' * hit' ≤ hit' + (n / 2 - 1) * (2 * B'))) :
    7479697 ≤ B := by
  rcases hbranch with ⟨hit, hs, hh⟩ | ⟨B', hit', hd, hs, hh⟩
  · exact eighth_near_saturated_companion_direct hs hh
  · exact (eighth_near_saturated_companion_quotient hd hs hh).2

#print axioms exists_optimal_head
#print axioms near_saturated_bounds
#print axioms near_saturated_family_root_floors
#print axioms no_constant_edge_q_ge_two
#print axioms no_constant_edge_q_one
#print axioms no_quartic_direction_triple
#print axioms mobius_cutoff_H
#print axioms mobius_cutoff_H2
#print axioms eq_pow_two_of_near_gcd
#print axioms eq_pow_two_of_near_gcd_H2
#print axioms near_saturated_power_triples_odd
#print axioms near_saturated_power_triples_even
#print axioms near_saturated_power_triples
#print axioms family_two_coset_obstruction
#print axioms family_one_coset_obstruction
#print axioms family_one_and_two_concrete_contradictions
#print axioms nonscalar_antipode_exact_saturation
#print axioms eighth_near_saturated_companion_direct
#print axioms eighth_near_saturated_companion_quotient
#print axioms eighth_near_saturated_companion

end ArkLib.ProximityGap.Frontier.EighthNearSaturatedPowers
