/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # Kummer determinant height floor and Wronskian pullback exclusions across the 33.55M quarter-rate interval

This module proves two general algebraic obstructions for three-head quarter-rate attacks on
`μ_{2^30}` across the entire 33,554,431-error open interval `[447,392,428, 480,946,858]`:

1. **Kummer determinant height floor** (`kummer_height_floor_of_sym`, `kummer_height_floor_of_deg`):
   For any multiplicatively independent curve component `X` of bidegree `(a, a)` with Kummer cover
   `X → X'` of degree `c = [K(X) : K(x^n, y^n)]` (where `n = 2^e` and `p ∤ n`), divisibility of
   all `2 × 2` valuation determinants `e_u(q₁) e_v(q₂) - e_u(q₂) e_v(q₁)` by the primitive Kummer
   exponent modulus `N' = n / d ≥ n / √c` forces
     `4 * c * H_u² * H_v² ≥ n²`.
   In particular, when `H_u = H_v = H` and `c ≤ q * n`:
   - `4 * q * H⁴ ≥ n` (giving `H ≥ 108` for `q ≤ 2`, removing the last Corvaja–Zannier Theorem 2
     dependency from the full split-pencil suborbit theory; `H ≥ 4` for `q ≤ 2^21`; `H ≥ 3` for
     `q ≤ 2^23`), and
   - `4 * a * H³ ≥ n` unconditionally (without any symmetry bound).

2. **Uniform Wronskian inner-degree floors across `[447,392,428, 480,946,858]`**:
   Using the exact AM-GM score identity `W² / (3m) ≥ 2W - 3m = S` and our large-characteristic
   Wronskian bound (`QuarterSplitWronskianSuborbits`) with `(h, k) ∈ {(3, 3), (4, 2), (2, 2)}`,
   every non-dihedral inner factor `T` (`deg T = d_aut * w` with `d_aut = 2^r` and `w ≥ 2`) of:
   - ANY three-head attack beating `480,946,859` (`S ≥ 603,979,777`) satisfies `deg T ≥ 12,463,075`;
   - ANY unrestricted attack through `469,762,048` (`S ≥ 671,088,641`) satisfies `deg T ≥ 19,173,962`.
-/

set_option autoImplicit false

namespace ProximityGap.QuarterIntervalWronskianPullbacks

open Finset

/-! ## Part 1: Kummer determinant height floor -/

/-- If `r'` or `s'` is odd and `2^j` divides `r' * eu(q) + s' * ev(q)` for all `q`, then `2^j`
divides every `2 × 2` valuation determinant `eu(q₁) * ev(q₂) - eu(q₂) * ev(q₁)`. -/
theorem two_pow_dvd_det_of_congruence {S : Type*} {j : ℕ} {r' s' : ℤ}
    (hprim : ¬ (2 : ℤ) ∣ r' ∨ ¬ (2 : ℤ) ∣ s')
    (eu ev : S → ℤ)
    (hcong : ∀ q : S, ((2 ^ j : ℕ) : ℤ) ∣ r' * eu q + s' * ev q)
    (q₁ q₂ : S) :
    ((2 ^ j : ℕ) : ℤ) ∣ eu q₁ * ev q₂ - eu q₂ * ev q₁ := by
  have h1 := hcong q₁
  have h2 := hcong q₂
  have hr : ((2 ^ j : ℕ) : ℤ) ∣ r' * (eu q₁ * ev q₂ - eu q₂ * ev q₁) := by
    have hid : r' * (eu q₁ * ev q₂ - eu q₂ * ev q₁) =
        (r' * eu q₁ + s' * ev q₁) * ev q₂ - (r' * eu q₂ + s' * ev q₂) * ev q₁ := by ring
    rw [hid]
    exact dvd_sub (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _)
  have hs : ((2 ^ j : ℕ) : ℤ) ∣ s' * (eu q₁ * ev q₂ - eu q₂ * ev q₁) := by
    have hid : s' * (eu q₁ * ev q₂ - eu q₂ * ev q₁) =
        (r' * eu q₂ + s' * ev q₂) * eu q₁ - (r' * eu q₁ + s' * ev q₁) * eu q₂ := by ring
    rw [hid]
    exact dvd_sub (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_left h1 _)
  have cop_of_odd : ∀ x : ℤ, ¬ (2 : ℤ) ∣ x → IsCoprime ((2 ^ j : ℕ) : ℤ) x := by
    intro x hx
    have h2cop : IsCoprime (2 : ℤ) x := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hdvd : (Int.gcd 2 x : ℕ) ∣ 2 := Nat.gcd_dvd_left 2 x.natAbs
      have hcases : Int.gcd 2 x = 1 ∨ Int.gcd 2 x = 2 := (Nat.dvd_prime Nat.prime_two).mp hdvd
      rcases hcases with h | h
      · exact h
      · exfalso
        apply hx
        have h2x : (2 : ℕ) ∣ x.natAbs := h ▸ Nat.gcd_dvd_right 2 x.natAbs
        exact Int.ofNat_dvd_left.mpr h2x
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h2cop.pow_left (m := j)
  rcases hprim with hr_odd | hs_odd
  · exact (cop_of_odd r' hr_odd).dvd_of_dvd_mul_left hr
  · exact (cop_of_odd s' hs_odd).dvd_of_dvd_mul_left hs

/-- Non-proportional bounded valuation vectors cannot have every `2 × 2` determinant divisible by
`N' > 2 * Hu * Hv`. -/
theorem mod_le_two_mul_heights {S : Type*} {N' Hu Hv : ℕ}
    (eu ev : S → ℤ)
    (hbu : ∀ q, |eu q| ≤ Hu) (hbv : ∀ q, |ev q| ≤ Hv)
    (hnonprop : ∃ q₁ q₂, eu q₁ * ev q₂ ≠ eu q₂ * ev q₁)
    (hdvd : ∀ q₁ q₂, (N' : ℤ) ∣ eu q₁ * ev q₂ - eu q₂ * ev q₁) :
    N' ≤ 2 * Hu * Hv := by
  obtain ⟨q₁, q₂, hne⟩ := hnonprop
  let Δ : ℤ := eu q₁ * ev q₂ - eu q₂ * ev q₁
  have hΔ_ne : Δ ≠ 0 := sub_ne_zero.mpr hne
  have hΔ_pos : 0 < |Δ| := abs_pos.mpr hΔ_ne
  have hdvd_abs : (N' : ℤ) ∣ |Δ| := by
    rcases le_or_gt 0 Δ with h | h
    · rw [abs_of_nonneg h]; exact hdvd q₁ q₂
    · rw [abs_of_neg h]; exact (hdvd q₁ q₂).neg_right
  have hle_abs : (N' : ℤ) ≤ |Δ| := Int.le_of_dvd hΔ_pos hdvd_abs
  have habs_le : |Δ| ≤ 2 * (Hu : ℤ) * (Hv : ℤ) := by
    have htri : |Δ| ≤ |eu q₁ * ev q₂| + |eu q₂ * ev q₁| := abs_sub _ _
    have hp1 : |eu q₁ * ev q₂| ≤ (Hu : ℤ) * (Hv : ℤ) := by
      rw [abs_mul]
      exact mul_le_mul (hbu q₁) (hbv q₂) (abs_nonneg _) (Nat.cast_nonneg _)
    have hp2 : |eu q₂ * ev q₁| ≤ (Hu : ℤ) * (Hv : ℤ) := by
      rw [abs_mul]
      exact mul_le_mul (hbu q₂) (hbv q₁) (abs_nonneg _) (Nat.cast_nonneg _)
    linarith
  exact_mod_cast le_trans hle_abs habs_le

/-- Cardinality bound for multiples of `2^v` in `ZMod (2^e)`: every element divisible by `2^v`
lies in the image of `Fin (2^(e - v))` under multiplication by `2^v`, so any subset of
`(2^v • ZMod (2^e))²` has cardinality at most `(2^(e - v))²`. -/
theorem card_two_pow_multiple_pairs_le {e v : ℕ}
    (K : Finset (ZMod (2 ^ e) × ZMod (2 ^ e)))
    (hdiv : ∀ p ∈ K, ∃ a b : Fin (2 ^ (e - v)),
      p = (((2 ^ v * a.val : ℕ) : ZMod (2 ^ e)), ((2 ^ v * b.val : ℕ) : ZMod (2 ^ e)))) :
    K.card ≤ (2 ^ (e - v)) ^ 2 := by
  classical
  let f : Fin (2 ^ (e - v)) × Fin (2 ^ (e - v)) → ZMod (2 ^ e) × ZMod (2 ^ e) :=
    fun ab => (((2 ^ v * ab.1.val : ℕ) : ZMod (2 ^ e)), ((2 ^ v * ab.2.val : ℕ) : ZMod (2 ^ e)))
  have hsub : K ⊆ univ.image f := by
    intro p hp
    obtain ⟨a, b, rfl⟩ := hdiv p hp
    exact mem_image.mpr ⟨(a, b), mem_univ _, rfl⟩
  calc
    K.card ≤ (univ.image f).card := card_le_card hsub
    _ ≤ (univ : Finset (Fin (2 ^ (e - v)) × Fin (2 ^ (e - v)))).card := card_image_le
    _ = (2 ^ (e - v)) ^ 2 := by simp [sq]

/-- Combining the Kummer kernel size `|ker| * c = n²`, the packing bound `|ker| ≤ N'²`, and the
determinant ceiling `N' ≤ 2 * Hu * Hv` gives `n² ≤ 4 * c * Hu² * Hv²`. -/
theorem kummer_determinant_floor {n c N' Hu Hv : ℕ}
    (hker : n ^ 2 ≤ c * N' ^ 2) (hdet : N' ≤ 2 * Hu * Hv) :
    n ^ 2 ≤ 4 * c * Hu ^ 2 * Hv ^ 2 := by
  have hsq : N' ^ 2 ≤ 4 * Hu ^ 2 * Hv ^ 2 := by
    have h1 : N' ^ 2 ≤ (2 * Hu * Hv) ^ 2 := Nat.pow_le_pow_left hdet 2
    calc
      N' ^ 2 ≤ (2 * Hu * Hv) ^ 2 := h1
      _ = 4 * Hu ^ 2 * Hv ^ 2 := by ring
  calc
    n ^ 2 ≤ c * N' ^ 2 := hker
    _ ≤ c * (4 * Hu ^ 2 * Hv ^ 2) := Nat.mul_le_mul_left c hsq
    _ = 4 * c * Hu ^ 2 * Hv ^ 2 := by ring

/-- When `Hu = Hv = H` and `c ≤ q * n`, the Kummer determinant floor yields `n ≤ 4 * q * H⁴`. -/
theorem kummer_height_floor_of_sym {n c q H : ℕ} (hn : 0 < n)
    (hc : c ≤ q * n) (hfloor : n ^ 2 ≤ 4 * c * H ^ 2 * H ^ 2) :
    n ≤ 4 * q * H ^ 4 := by
  have h1 : n * n ≤ n * (4 * q * H ^ 4) := by
    calc
      n * n = n ^ 2 := (sq n).symm
      _ ≤ 4 * c * H ^ 2 * H ^ 2 := hfloor
      _ ≤ 4 * (q * n) * H ^ 2 * H ^ 2 := by gcongr
      _ = n * (4 * q * H ^ 4) := by ring
  exact Nat.le_of_mul_le_mul_left h1 hn

/-- Without ANY symmetry bound on `q`, `c * H = n * a` and `n² ≤ 4 * c * H⁴` yield `n ≤ 4 * a * H³`. -/
theorem kummer_height_floor_of_deg {n c a H : ℕ} (hn : 0 < n)
    (hdeg : c * H = n * a) (hfloor : n ^ 2 ≤ 4 * c * H ^ 2 * H ^ 2) :
    n ≤ 4 * a * H ^ 3 := by
  have h1 : n * n ≤ n * (4 * a * H ^ 3) := by
    calc
      n * n = n ^ 2 := (sq n).symm
      _ ≤ 4 * c * H ^ 2 * H ^ 2 := hfloor
      _ = 4 * (c * H) * H ^ 3 := by ring
      _ = 4 * (n * a) * H ^ 3 := by rw [hdeg]
      _ = n * (4 * a * H ^ 3) := by ring
  exact Nat.le_of_mul_le_mul_left h1 hn

/-- Production height floors at `n = 2^30`:
- `q ≤ 2` forces `H ≥ 108` (eliminating `H < 2` for every suborbit degree `a ≥ 1` without
  Corvaja–Zannier Theorem 2),
- `q ≤ 2^21` forces `H ≥ 4` (justifying `(h, k) = (3, 3)`),
- `q ≤ 2^23` forces `H ≥ 3` (justifying `(h, k) = (4, 2)` and `(2, 2)`). -/
theorem production_kummer_height_floors {q H : ℕ} (hfloor : 2 ^ 30 ≤ 4 * q * H ^ 4) :
    (q ≤ 2 → 108 ≤ H) ∧
    (q ≤ 2 ^ 21 → 4 ≤ H) ∧
    (q ≤ 2 ^ 23 → 3 ≤ H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hq
    by_contra! hlt
    have h1 : H ^ 4 ≤ 107 ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h2 : 4 * q * H ^ 4 ≤ 4 * 2 * 107 ^ 4 := by gcongr
    omega
  · intro hq
    by_contra! hlt
    have h1 : H ^ 4 ≤ 3 ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h2 : 4 * q * H ^ 4 ≤ 4 * 2 ^ 21 * 3 ^ 4 := by gcongr
    omega
  · intro hq
    by_contra! hlt
    have h1 : H ^ 4 ≤ 2 ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h2 : 4 * q * H ^ 4 ≤ 4 * 2 ^ 23 * 2 ^ 4 := by gcongr
    omega

/-! ## Part 2: Exact AM-GM pair-count lower bounds for partial three-head pencils -/

/-- Exact score monotonicity: for `w ≥ 2`, `m > 0`, `Smin ≥ 0`, and `2W - 3m ≥ Smin`, the function
`W ↦ (W² / (3m)) * w - W` is minimized at `W₀ = (Smin + 3m) / 2`. -/
theorem pair_count_score_mono {W m w Smin : ℝ}
    (hm : 0 < m) (hw : 2 ≤ w) (hS : 0 ≤ Smin) (hscore : Smin ≤ 2 * W - 3 * m) :
    ((Smin + 3 * m) / 2) ^ 2 / (3 * m) * w - (Smin + 3 * m) / 2 ≤
      W ^ 2 / (3 * m) * w - W := by
  let W0 : ℝ := (Smin + 3 * m) / 2
  have hW0_ge : 3 * m / 2 ≤ W0 := by dsimp [W0]; linarith
  have hW_ge : W0 ≤ W := by dsimp [W0]; linarith
  have hdiff : W ^ 2 / (3 * m) * w - W - (W0 ^ 2 / (3 * m) * w - W0) =
      (W - W0) * (w * (W + W0) - 3 * m) / (3 * m) := by
    field_simp
    ring
  rw [← sub_nonneg, hdiff]
  apply div_nonneg _ (by positivity)
  apply mul_nonneg (by linarith)
  have hsum : 3 * m ≤ W + W0 := by linarith
  nlinarith

/-- For `w = 2` and `0 < m ≤ D`, the exact score lower bound satisfies
`Smin² / (6 D) + Smin / 2 ≤ ((Smin + 3m)/2)² / (3m) * 2 - (Smin + 3m)/2`. -/
theorem pair_count_w2 {m D Smin : ℝ} (hm : 0 < m) (hmD : m ≤ D) :
    Smin ^ 2 / (6 * D) + Smin / 2 ≤
      ((Smin + 3 * m) / 2) ^ 2 / (3 * m) * 2 - (Smin + 3 * m) / 2 := by
  have hD : 0 < D := lt_of_lt_of_le hm hmD
  have hid : ((Smin + 3 * m) / 2) ^ 2 / (3 * m) * 2 - (Smin + 3 * m) / 2 =
      Smin ^ 2 / (6 * m) + Smin / 2 := by
    field_simp
    ring
  rw [hid]
  have hfrac : Smin ^ 2 / (6 * D) ≤ Smin ^ 2 / (6 * m) :=
    div_le_div_of_nonneg_left (sq_nonneg Smin) (by positivity) (by linarith)
  linarith

/-- For `w ≥ 3` and `0 < m ≤ D`, the exact AM-GM score identity gives the linear lower bound
`Smin * (w - 1) - (3D - Smin) / 2`. -/
theorem pair_count_wge3 {m D w Smin : ℝ} (hm : 0 < m) (hmD : m ≤ D) (hw : 3 ≤ w) :
    Smin * (w - 1) - (3 * D - Smin) / 2 ≤
      ((Smin + 3 * m) / 2) ^ 2 / (3 * m) * w - (Smin + 3 * m) / 2 := by
  have h1 : Smin * w - (Smin + 3 * m) / 2 ≤
      ((Smin + 3 * m) / 2) ^ 2 / (3 * m) * w - (Smin + 3 * m) / 2 := by
    have hdiff : ((Smin + 3 * m) / 2) ^ 2 / (3 * m) * w - Smin * w =
        (Smin - 3 * m) ^ 2 * w / (12 * m) := by
      field_simp
      ring
    linarith [show 0 ≤ (Smin - 3 * m) ^ 2 * w / (12 * m) by positivity]
  linarith

/-- Concave-quadratic elimination for `w ≥ 3`: whenever `0 ≤ loss` and `0 ≤ slope - (3/2) * loss`,
the Wronskian inequality `d_aut * (Smin * (w - 1) - loss) ≤ alpha_n * d_aut * (w - 1) + two_beta * (d_aut * (w - 1))²`
forces `slope ≤ two_beta * (d_aut * w)` uniformly for ALL `d_aut > 0` and ALL `w ≥ 3`. -/
theorem uniform_degree_floor_wge3 {d_aut w slope loss two_beta : ℝ}
    (hw : 3 ≤ w) (hloss : 0 ≤ loss) (hmargin : 0 ≤ slope - 3 / 2 * loss)
    (hbound : slope * (w - 1) - loss ≤ two_beta * d_aut * (w - 1) ^ 2) :
    slope ≤ two_beta * (d_aut * w) := by
  have hw1 : 0 < w - 1 := by linarith
  have hw2 : 2 ≤ w - 1 := by linarith
  have hstep : slope * (w - 1) ^ 2 ≤ w * (slope * (w - 1) - loss) := by
    have hid : w * (slope * (w - 1) - loss) - slope * (w - 1) ^ 2 =
        (slope - loss) * (w - 1) - loss := by ring
    rw [← sub_nonneg, hid]
    have h1 : 2 * (slope - 3 / 2 * loss) ≤ (slope - loss) * (w - 1) - loss := by
      have hloss_le : 0 ≤ slope - loss := by linarith
      nlinarith
    linarith
  have hmul : w * (slope * (w - 1) - loss) ≤ w * (two_beta * d_aut * (w - 1) ^ 2) :=
    mul_le_mul_of_nonneg_left hbound (by linarith)
  have hcomb : slope * (w - 1) ^ 2 ≤ (two_beta * (d_aut * w)) * (w - 1) ^ 2 := by
    calc
      slope * (w - 1) ^ 2 ≤ w * (slope * (w - 1) - loss) := hstep
      _ ≤ w * (two_beta * d_aut * (w - 1) ^ 2) := hmul
      _ = (two_beta * (d_aut * w)) * (w - 1) ^ 2 := by ring
  exact le_of_mul_le_mul_right hcomb (sq_pos_of_pos hw1)

/-! ## Part 3: Concrete inner-degree exclusions across `[447,392,428, 480,946,858]` -/

/-- **Unconditional non-dihedral inner-degree floor across the ENTIRE 33.55M-error interval
`[447,392,428, 480,946,858]`.**
For ANY three-head attack beating `480,946,859` (`S ≥ 603,979,777 = 9n/16 + 1`), any inner factor
`T` of degree `t = d_aut * w` (`d_aut = 2^r`, `w ≥ 2`) satisfies `12,463,075 ≤ t`.
Uses `(h, k) = (3, 3)` (`M = 15`) when `r ≤ 21` and `(h, k) = (4, 2)` (`M = 14`) when `r = 22`
(justified by `production_kummer_height_floors`), and `2^23 * 2 = 16,777,216` when `r ≥ 23`. -/
theorem non_dihedral_floor_beat_480M {r w : ℕ} (hw : 2 ≤ w)
    (hwr33 : r ≤ 21 →
      let da : ℝ := (2 ^ r : ℕ)
      (if w = 2 then (603979777 : ℝ) ^ 2 / (6 * 268435454) + 603979777 / 2
       else 603979777 * ((w : ℝ) - 1) - (3 * 268435454 - 603979777) / 2) ≤
      (2 / 5 : ℝ) * 1073741824 * ((w : ℝ) - 1) + 14 * da * ((w : ℝ) - 1) ^ 2)
    (hwr42 : r = 22 → w = 2 →
      (603979777 : ℝ) ^ 2 / (6 * 268435454) + 603979777 / 2 ≤
      (3 / 7 : ℝ) * 1073741824 + 13 * ((2 ^ 22 : ℕ) : ℝ)) :
    12463075 ≤ 2 ^ r * w := by
  by_cases hr23 : 23 ≤ r
  · have hpow : 2 ^ 23 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) hr23
    have hmul : 2 ^ 23 * 2 ≤ 2 ^ r * w := Nat.mul_le_mul hpow hw
    omega
  · by_cases hr22 : r = 22
    · subst hr22
      by_cases hw2 : w = 2
      · exfalso
        have hb := hwr42 rfl hw2
        norm_num at hb
      · have hw3 : 3 ≤ w := by omega
        have hmul : 2 ^ 22 * 3 ≤ 2 ^ 22 * w := Nat.mul_le_mul_left _ hw3
        omega
    · have hr21 : r ≤ 21 := by omega
      have hb := hwr33 hr21
      by_cases hw2 : w = 2
      · subst hw2
        simp only [↓reduceIte, Nat.cast_ofNat] at hb
        have hda : (7070398 : ℝ) < (2 ^ r : ℕ) := by linarith
        have hda_nat : 7070399 ≤ 2 ^ r := by
          have : (7070398 : ℕ) < 2 ^ r := by exact_mod_cast hda
          omega
        omega
      · have hw3 : 3 ≤ w := by omega
        simp only [hw2, ↓reduceIte] at hb
        have hslope_bound : (603979777 - (2 / 5 : ℝ) * 1073741824) * ((w : ℝ) - 1) -
            (3 * 268435454 - 603979777) / 2 ≤ 14 * ((2 ^ r : ℕ) : ℝ) * ((w : ℝ) - 1) ^ 2 := by
          linarith
        have hfloor := uniform_degree_floor_wge3
          (d_aut := ((2 ^ r : ℕ) : ℝ)) (w := (w : ℝ))
          (slope := 603979777 - (2 / 5 : ℝ) * 1073741824)
          (loss := (3 * 268435454 - 603979777) / 2) (two_beta := 14)
          (by exact_mod_cast hw3) (by norm_num) (by norm_num) hslope_bound
        have hreal : (12463074 : ℝ) < ((2 ^ r * w : ℕ) : ℝ) := by
          push_cast at hfloor ⊢
          linarith
        have hnat : 12463074 < 2 ^ r * w := by exact_mod_cast hreal
        omega

/-- **Unconditional non-dihedral inner-degree floor for EVERY unrestricted attack through
`469,762,048` errors (`S ≥ 671,088,641 = 5n/8 + 1`).**
Every non-dihedral inner factor `T` (`deg T = 2^r * w`, `w ≥ 2`) satisfies `19,173,962 ≤ 2^r * w`.
Uses `(h, k) = (2, 2)` (`M = 8`) for all `r ≤ 23` (justified by `production_kummer_height_floors`
giving `H ≥ 3 > 2`) and `2^24 * 2 = 33,554,432` for `r ≥ 24`. -/
theorem non_dihedral_floor_unrestricted_469M {r w : ℕ} (hw : 2 ≤ w)
    (hwr22 : r ≤ 23 →
      let da : ℝ := (2 ^ r : ℕ)
      (if w = 2 then (671088641 : ℝ) ^ 2 / (6 * 268435454) + 671088641 / 2
       else 671088641 * ((w : ℝ) - 1) - (3 * 268435454 - 671088641) / 2) ≤
      (1 / 2 : ℝ) * 1073741824 * ((w : ℝ) - 1) + 7 * da * ((w : ℝ) - 1) ^ 2) :
    19173962 ≤ 2 ^ r * w := by
  by_cases hr24 : 24 ≤ r
  · have hpow : 2 ^ 24 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) hr24
    have hmul : 2 ^ 24 * 2 ≤ 2 ^ r * w := Nat.mul_le_mul hpow hw
    omega
  · have hr23 : r ≤ 23 := by omega
    have hb := hwr22 hr23
    by_cases hw2 : w = 2
    · subst hw2
      simp only [↓reduceIte, Nat.cast_ofNat] at hb
      have hda : (11184811 : ℝ) < (2 ^ r : ℕ) := by linarith
      have hda_nat : 11184812 ≤ 2 ^ r := by
        have : (11184811 : ℕ) < 2 ^ r := by exact_mod_cast hda
        omega
      omega
    · have hw3 : 3 ≤ w := by omega
      simp only [hw2, ↓reduceIte] at hb
      have hslope_bound : (671088641 - (1 / 2 : ℝ) * 1073741824) * ((w : ℝ) - 1) -
          (3 * 268435454 - 671088641) / 2 ≤ 7 * ((2 ^ r : ℕ) : ℝ) * ((w : ℝ) - 1) ^ 2 := by
        linarith
      have hfloor := uniform_degree_floor_wge3
        (d_aut := ((2 ^ r : ℕ) : ℝ)) (w := (w : ℝ))
        (slope := 671088641 - (1 / 2 : ℝ) * 1073741824)
        (loss := (3 * 268435454 - 671088641) / 2) (two_beta := 7)
        (by exact_mod_cast hw3) (by norm_num) (by norm_num) hslope_bound
      have hreal : (19173961 : ℝ) < ((2 ^ r * w : ℕ) : ℝ) := by
        push_cast at hfloor ⊢
        linarith
      have hnat : 19173961 < 2 ^ r * w := by exact_mod_cast hreal
      omega

/-- Characteristic headroom for `(h, k) ∈ {(3, 3), (4, 2), (2, 2)}` on both designated primes:
`(h + k) * n * D ≤ 6 * n * D < 2^61 < p₁ < p₂`. -/
theorem characteristic_headroom_interval :
    6 * 1073741824 * 268435454 < 2 ^ 61 ∧
    2 ^ 61 < 365375409332725729550921208179070755120141565953 ∧
    2 ^ 61 < 730750818665451459101842416358141509841924915201 := by
  decide

#print axioms two_pow_dvd_det_of_congruence
#print axioms mod_le_two_mul_heights
#print axioms card_two_pow_multiple_pairs_le
#print axioms kummer_determinant_floor
#print axioms kummer_height_floor_of_sym
#print axioms kummer_height_floor_of_deg
#print axioms production_kummer_height_floors
#print axioms pair_count_score_mono
#print axioms pair_count_w2
#print axioms pair_count_wge3
#print axioms uniform_degree_floor_wge3
#print axioms non_dihedral_floor_beat_480M
#print axioms non_dihedral_floor_unrestricted_469M
#print axioms characteristic_headroom_interval

end ProximityGap.QuarterIntervalWronskianPullbacks
