/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Dyadic-tower squaring and antipodal-pairing laws for Paley sums on `μ_{2^m}`

Smooth evaluation domains in the proximity-gap grand challenges are dyadic multiplicative
subgroups `H = μ_{2^m} ⊆ Fˣ` with `m ≥ 2` (so `-1 ∈ H` and `χ(-1) = 1`). Unlike generic
multiplicative subgroups, `H` carries the exact antipodal pairing `x ↔ -x` and the squaring
homomorphism `x ↦ x²` onto `H² = μ_{2^{m-1}}`, satisfying `(a - x)(a + x) = a² - x²`.

This file proves the exact algebraic consequences of the dyadic tower, axiom-clean:

* `abs_antipodal_pair_eq`: for every `a ∈ F` and `x ≠ 0` (any odd-characteristic `F`),
  `|χ(a - x) + χ(a + x)| = 1 + χ(a² - x²)`.
* `sq_antipodal_pair_eq`: `(χ(a - x) + χ(a + x))² = 2 - 1_{a² = x²} + 2 χ(a² - x²)`.
* `dyadic_row_L1_eq`: summing over `H² = H.image (· ^ 2)` (for a subgroup `H` with `-1 ∈ H`),
  `∑ y ∈ H², |χ(a - x_y) + χ(a + x_y)| = |H|/2 + W_{H²}(a²)`, and in particular the
  **dyadic row descent inequality** `|W_H(a)| ≤ |H|/2 + W_{H²}(a²)`.
* `dyadic_rectangle_descent`: for any prescribed `A ⊆ F`,
  `|S(A, H)| ≤ |A|·|H|/2 + ∑ a ∈ A, W_{H²}(a²)`.
* `dyadic_autocorrelation_half`: for a cyclic subgroup `H = ⟨g⟩` of even order `2m` with `g^m = -1`,
  the half-shift autocorrelation of `c_j = χ(1 - g^j)` equals **twice** the row sum of `H²`:
  `∑ j < 2m, c_j c_{j+m} = 2 ∑ y ∈ H², χ(1 - y)` (recovering the exact production identities
  `-65858 = 2 · (-32929)` and `-2882 = 2 · (-1441)`).
* `dyadic_autocorrelation_descent`: for every shift `h`,
  `|R_h(H)| ≤ m + R_h(H²) + 2`.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ProximityGap.PaleyDyadicTower

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. Pointwise antipodal-squaring identities -/

omit [Fintype F] [DecidableEq F] in
private theorem two_ne_zero_of_ringChar (hF : ringChar F ≠ 2) : (2 : F) ≠ 0 := by
  intro h2
  have hdvd : ringChar F ∣ 2 := (CharP.cast_eq_zero_iff F (ringChar F) 2).mp (by simpa using h2)
  rcases CharP.char_is_prime_or_zero F (ringChar F) with hprime | h0
  · have hle : ringChar F ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    have hge : 2 ≤ ringChar F := hprime.two_le
    omega
  · rw [h0, zero_dvd_iff] at hdvd
    omega

/-- `χ(a - x) * χ(a + x) = χ(a² - x²)`. -/
theorem char_antipodal_mul (a x : F) :
    quadraticChar F (a - x) * quadraticChar F (a + x) = quadraticChar F (a ^ 2 - x ^ 2) := by
  rw [← map_mul, show (a - x) * (a + x) = a ^ 2 - x ^ 2 by ring]

/-- **Exact pointwise `L¹` antipodal-pairing identity**:
when `ringChar F ≠ 2` and `x ≠ 0`,
`|χ(a - x) + χ(a + x)| = 1 + χ(a² - x²)` for EVERY `a ∈ F` (including `a = ±x` and `a = 0`). -/
theorem abs_antipodal_pair_eq (hF : ringChar F ≠ 2)
    (a : F) {x : F} (hx : x ≠ 0) :
    |quadraticChar F (a - x) + quadraticChar F (a + x)| = 1 + quadraticChar F (a ^ 2 - x ^ 2) := by
  have h2ne : (2 : F) ≠ 0 := two_ne_zero_of_ringChar hF
  rw [← char_antipodal_mul]
  by_cases h1 : a - x = 0
  · have hax : a = x := sub_eq_zero.mp h1
    rw [hax]
    have h2x : x + x ≠ 0 := by rw [← two_mul]; exact mul_ne_zero h2ne hx
    rw [sub_self, MulChar.map_zero, zero_add, zero_mul, add_zero]
    rcases quadraticChar_dichotomy h2x with h | h <;> rw [h] <;> decide
  · by_cases h2 : a + x = 0
    · have hax : a = -x := eq_neg_of_add_eq_zero_left h2
      rw [hax]
      have h2x : -x - x ≠ 0 := by
        rw [show -x - x = -(2 * x) by ring]
        exact neg_ne_zero.mpr (mul_ne_zero h2ne hx)
      rw [neg_add_cancel, MulChar.map_zero, add_zero, mul_zero, add_zero]
      rcases quadraticChar_dichotomy h2x with h | h <;> rw [h] <;> decide
    · rcases quadraticChar_dichotomy h1 with ha | ha <;>
        rcases quadraticChar_dichotomy h2 with hb | hb <;>
        rw [ha, hb] <;> decide

/-- **Exact pointwise `L²` antipodal-pairing identity**:
when `ringChar F ≠ 2` and `x ≠ 0`,
`(χ(a - x) + χ(a + x))² = 2 - (if a² = x² then 1 else 0) + 2 * χ(a² - x²)`. -/
theorem sq_antipodal_pair_eq (hF : ringChar F ≠ 2) (a : F) {x : F} (hx : x ≠ 0) :
    (quadraticChar F (a - x) + quadraticChar F (a + x)) ^ 2 =
      2 - (if a ^ 2 = x ^ 2 then (1 : ℤ) else 0) + 2 * quadraticChar F (a ^ 2 - x ^ 2) := by
  have h2ne : (2 : F) ≠ 0 := two_ne_zero_of_ringChar hF
  rw [← char_antipodal_mul]
  by_cases hsq : a ^ 2 = x ^ 2
  · simp only [hsq, ↓reduceIte]
    have hfac : (a - x) * (a + x) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h1 | h2
    · have hax : a = x := sub_eq_zero.mp h1
      rw [hax]
      have h2x : x + x ≠ 0 := by rw [← two_mul]; exact mul_ne_zero h2ne hx
      rw [sub_self, MulChar.map_zero, zero_add, zero_mul, mul_zero, add_zero]
      rcases quadraticChar_dichotomy h2x with h | h <;> rw [h] <;> decide
    · have hax : a = -x := eq_neg_of_add_eq_zero_left h2
      rw [hax]
      have h2x : -x - x ≠ 0 := by
        rw [show -x - x = -(2 * x) by ring]
        exact neg_ne_zero.mpr (mul_ne_zero h2ne hx)
      rw [neg_add_cancel, MulChar.map_zero, add_zero, mul_zero, mul_zero, add_zero]
      rcases quadraticChar_dichotomy h2x with h | h <;> rw [h] <;> decide
  · simp only [hsq, ↓reduceIte]
    have h1 : a - x ≠ 0 := fun h => hsq (by linear_combination (a + x) * h)
    have h2 : a + x ≠ 0 := fun h => hsq (by linear_combination (a - x) * h)
    rcases quadraticChar_dichotomy h1 with ha | ha <;>
      rcases quadraticChar_dichotomy h2 with hb | hb <;>
      rw [ha, hb] <;> decide

/-! ## 2. Exact antipodal-pairing and dyadic descent on any `-1`-closed subset -/

/-- Row sum `W_S(a) = ∑ x ∈ S, χ(a - x)`. -/
def rowSum (S : Finset F) (a : F) : ℤ :=
  ∑ x ∈ S, quadraticChar F (a - x)

/-- **Exact sum of antipodal pair magnitudes on a `-1`-closed nonzero set `H`**:
`∑ x ∈ H, |χ(a - x) + χ(a + x)| = |H| + ∑ x ∈ H, χ(a² - x²)`.
Since each `y = x² ∈ H²` has two preimages `±x ∈ H`, both sides equal `2` times the sum over `H²`. -/
theorem sum_abs_antipodal_eq (hF : ringChar F ≠ 2)
    (H : Finset F) (h0 : (0 : F) ∉ H) (a : F) :
    ∑ x ∈ H, |quadraticChar F (a - x) + quadraticChar F (a + x)| =
      (H.card : ℤ) + ∑ x ∈ H, quadraticChar F (a ^ 2 - x ^ 2) := by
  have hpt : ∀ x ∈ H, |quadraticChar F (a - x) + quadraticChar F (a + x)| =
      1 + quadraticChar F (a ^ 2 - x ^ 2) := fun x hx =>
    abs_antipodal_pair_eq hF a (fun h => h0 (h ▸ hx))
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
  simp

/-- **Exact `L²` antipodal-pairing identity on a `-1`-closed nonzero set `H`**:
`∑ x ∈ H, (χ(a - x) + χ(a + x))² = 2|H| - 2·1_{a ∈ H} + 2 ∑ x ∈ H, χ(a² - x²)`. -/
theorem sum_sq_antipodal_eq (hF : ringChar F ≠ 2)
    (H : Finset F) (h0 : (0 : F) ∉ H) (hnegH : ∀ x ∈ H, -x ∈ H) (a : F) :
    ∑ x ∈ H, (quadraticChar F (a - x) + quadraticChar F (a + x)) ^ 2 =
      2 * (H.card : ℤ) - (if a ∈ H then (2 : ℤ) else 0) +
        2 * ∑ x ∈ H, quadraticChar F (a ^ 2 - x ^ 2) := by
  have h2ne : (2 : F) ≠ 0 := two_ne_zero_of_ringChar hF
  have hpt : ∀ x ∈ H, (quadraticChar F (a - x) + quadraticChar F (a + x)) ^ 2 =
      2 - (if a ^ 2 = x ^ 2 then (1 : ℤ) else 0) + 2 * quadraticChar F (a ^ 2 - x ^ 2) :=
    fun x hx => sq_antipodal_pair_eq hF a (fun h => h0 (h ▸ hx))
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hind : (∑ x ∈ H, if a ^ 2 = x ^ 2 then (1 : ℤ) else 0) = if a ∈ H then 2 else 0 := by
    by_cases ha : a ∈ H
    · simp only [ha, ↓reduceIte]
      have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
      have hne : a ≠ -a := fun h => by
        have : 2 * a = 0 := by linear_combination h
        exact mul_ne_zero h2ne ha0 this
      have hfilt : H.filter (fun x => a ^ 2 = x ^ 2) = {a, -a} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨_, hsq⟩
          have hfac : (x - a) * (x + a) = 0 := by linear_combination -hsq
          rcases mul_eq_zero.mp hfac with h1 | h2
          · exact Or.inl (sub_eq_zero.mp h1)
          · exact Or.inr (eq_neg_of_add_eq_zero_left h2)
        · rintro (rfl | rfl)
          · exact ⟨ha, rfl⟩
          · exact ⟨hnegH a ha, by ring⟩
      rw [← Finset.sum_filter, hfilt, Finset.sum_pair hne]
      norm_num
    · simp only [ha, ↓reduceIte]
      refine Finset.sum_eq_zero fun x hx => ?_
      have hne : a ^ 2 ≠ x ^ 2 := by
        intro hsq
        have hfac : (a - x) * (a + x) = 0 := by linear_combination hsq
        rcases mul_eq_zero.mp hfac with h1 | h2
        · exact ha (sub_eq_zero.mp h1 ▸ hx)
        · have : a = -x := eq_neg_of_add_eq_zero_left h2
          exact ha (this ▸ hnegH x hx)
      simp only [hne, ↓reduceIte]
  rw [hind]
  simp [mul_comm]

/-- For a `-1`-closed nonzero set `H`, every square `y ∈ H.image (· ^ 2)` has exactly two
preimages `±x` in `H`, so summing any function of `x²` over `H` equals `2` times the sum
over `H² = H.image (· ^ 2)`. -/
theorem sum_sq_eq_two_mul_sum_image (hF : ringChar F ≠ 2)
    (H : Finset F) (h0 : (0 : F) ∉ H) (hnegH : ∀ x ∈ H, -x ∈ H) (g : F → ℤ) :
    ∑ x ∈ H, g (x ^ 2) = 2 * ∑ y ∈ H.image (· ^ 2), g y := by
  classical
  have h2ne : (2 : F) ≠ 0 := two_ne_zero_of_ringChar hF
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : F => x ^ 2) (t := H.image (· ^ 2))
    (fun x hx => Finset.mem_image_of_mem _ hx), Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hy
  have hx0_ne : x0 ≠ 0 := fun h => h0 (h ▸ hx0)
  have hne : x0 ≠ -x0 := fun h => by
    have : 2 * x0 = 0 := by linear_combination h
    exact mul_ne_zero h2ne hx0_ne this
  have hfilt : H.filter (fun x => x ^ 2 = x0 ^ 2) = {x0, -x0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hsq⟩
      have hfac : (x - x0) * (x + x0) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hfac with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h2)
    · rintro (rfl | rfl)
      · exact ⟨hx0, rfl⟩
      · exact ⟨hnegH x0 hx0, by ring⟩
  rw [hfilt, Finset.sum_pair hne]
  have : (-x0) ^ 2 = x0 ^ 2 := by ring
  rw [this]; ring

theorem card_eq_two_mul_card_sq_image (hF : ringChar F ≠ 2)
    (H : Finset F) (h0 : (0 : F) ∉ H) (hnegH : ∀ x ∈ H, -x ∈ H) :
    H.card = 2 * (H.image (· ^ 2)).card := by
  have h := sum_sq_eq_two_mul_sum_image hF H h0 hnegH (fun _ => (1 : ℤ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- **Dyadic row-sum descent inequality**: for any `-1`-closed nonzero set `H` (in particular
any dyadic subgroup `μ_{2^m}`, `m ≥ 2`) over any odd-characteristic finite field,
`2 * |W_H(a)| ≤ |H| + 2 * W_{H²}(a²)`, i.e., `|W_H(a)| ≤ |H|/2 + W_{H²}(a²)`. -/
theorem dyadic_row_descent (hF : ringChar F ≠ 2)
    (H : Finset F) (h0 : (0 : F) ∉ H) (hnegH : ∀ x ∈ H, -x ∈ H) (a : F) :
    2 * |rowSum H a| ≤ (H.card : ℤ) + 2 * rowSum (H.image (· ^ 2)) (a ^ 2) := by
  have h2W : 2 * rowSum H a = ∑ x ∈ H, (quadraticChar F (a - x) + quadraticChar F (a + x)) := by
    rw [Finset.sum_add_distrib]
    have hflip : ∑ x ∈ H, quadraticChar F (a + x) = ∑ x ∈ H, quadraticChar F (a - x) := by
      refine Finset.sum_nbij' (fun x => -x) (fun x => -x) (fun x hx => hnegH x hx)
        (fun x hx => hnegH x hx) (fun _ _ => neg_neg _) (fun _ _ => neg_neg _) ?_
      intro x _; simp [sub_eq_add_neg]
    rw [hflip, rowSum]; ring
  calc 2 * |rowSum H a|
      = |2 * rowSum H a| := by rw [abs_mul, abs_of_pos (by decide : (0 : ℤ) < 2)]
    _ = |∑ x ∈ H, (quadraticChar F (a - x) + quadraticChar F (a + x))| := by rw [h2W]
    _ ≤ ∑ x ∈ H, |quadraticChar F (a - x) + quadraticChar F (a + x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = (H.card : ℤ) + ∑ x ∈ H, quadraticChar F (a ^ 2 - x ^ 2) :=
        sum_abs_antipodal_eq hF H h0 a
    _ = (H.card : ℤ) + 2 * rowSum (H.image (· ^ 2)) (a ^ 2) := by
        rw [sum_sq_eq_two_mul_sum_image hF H h0 hnegH (fun y => quadraticChar F (a ^ 2 - y))]
        rfl

/-- **Dyadic rectangle descent**: for any prescribed `A ⊆ F` and any `-1`-closed nonzero `H`,
`2 * |S(A, H)| ≤ |A|·|H| + 2 ∑ a ∈ A, W_{H²}(a²)`. -/
theorem dyadic_rectangle_descent (hF : ringChar F ≠ 2)
    (A H : Finset F) (h0 : (0 : F) ∉ H) (hnegH : ∀ x ∈ H, -x ∈ H) :
    2 * |∑ a ∈ A, rowSum H a| ≤
      (A.card : ℤ) * H.card + 2 * ∑ a ∈ A, rowSum (H.image (· ^ 2)) (a ^ 2) := by
  calc 2 * |∑ a ∈ A, rowSum H a|
      ≤ 2 * ∑ a ∈ A, |rowSum H a| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by decide)
    _ = ∑ a ∈ A, 2 * |rowSum H a| := Finset.mul_sum _ _ _
    _ ≤ ∑ a ∈ A, ((H.card : ℤ) + 2 * rowSum (H.image (· ^ 2)) (a ^ 2)) :=
        Finset.sum_le_sum fun a _ => dyadic_row_descent hF H h0 hnegH a
    _ = (A.card : ℤ) * H.card + 2 * ∑ a ∈ A, rowSum (H.image (· ^ 2)) (a ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]

/-! ## 3. Exact cyclic half-shift autocorrelation and shift descent on `⟨g⟩` -/

/-- Cyclic Paley sign sequence `c_j = χ(1 - g^j)` on a cyclic group of order `n`. -/
def cyclicSign (g : F) (j : ℕ) : ℤ :=
  quadraticChar F (1 - g ^ j)

/-- Cyclic autocorrelation `R_h = ∑_{j < n} c_j * c_{(j + h) % n}`. -/
def cyclicAuto (g : F) (n h : ℕ) : ℤ :=
  ∑ j ∈ Finset.range n, cyclicSign g j * cyclicSign g ((j + h) % n)

/-- **Exact half-shift autocorrelation identity on any even-order cyclic subgroup**:
if `g^m = -1` (so `g` has order `2m`), then the half-shift autocorrelation `R_m` equals
twice the row sum of the squared subgroup `⟨g²⟩`:
`R_m(g, 2m) = 2 * ∑ j < m, χ(1 - (g²)^j)`.
This explains the exact production identities `-65858 = 2 · (-32929)` and `-2882 = 2 · (-1441)`. -/
theorem cyclicAuto_half_eq (g : F) (m : ℕ) (hgm : g ^ m = -1) :
    cyclicAuto g (2 * m) m = 2 * ∑ j ∈ Finset.range m, cyclicSign (g ^ 2) j := by
  have hg2m : g ^ (2 * m) = 1 := by
    rw [show 2 * m = m + m by omega, pow_add, hgm]; ring
  have hshift : ∀ j, g ^ (j + m) = -g ^ j := fun j => by rw [pow_add, hgm, mul_neg_one]
  have hmod : ∀ j ∈ Finset.range (2 * m), g ^ ((j + m) % (2 * m)) = -g ^ j := by
    intro j hj
    have hjlt : j < 2 * m := Finset.mem_range.mp hj
    rcases lt_or_ge j m with hjm | hjm
    · rw [Nat.mod_eq_of_lt (by omega), hshift]
    · have hmod_eq : (j + m) % (2 * m) = j - m := by
        have : j + m = (j - m) + 2 * m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod_eq]
      have : g ^ j = g ^ (j - m) * g ^ m := by
        rw [← pow_add, Nat.sub_add_cancel hjm]
      rw [this, hgm, mul_neg_one, neg_neg]
  have hpair : ∀ j ∈ Finset.range (2 * m),
      cyclicSign g j * cyclicSign g ((j + m) % (2 * m)) =
        cyclicSign (g ^ 2) (j % m) := by
    intro j hj
    unfold cyclicSign
    rw [hmod j hj, sub_neg_eq_add, ← map_mul,
      show (1 - g ^ j) * (1 + g ^ j) = 1 - (g ^ 2) ^ j by ring]
    congr 2
    have hdiv : (g ^ 2) ^ m = 1 := by rw [← pow_mul, hg2m]
    conv_lhs => rw [← Nat.div_add_mod j m]
    rw [pow_add, pow_mul, hdiv, one_pow, one_mul]
  rw [cyclicAuto, Finset.sum_congr rfl hpair]
  have hsplit : ∑ j ∈ Finset.range (2 * m), cyclicSign (g ^ 2) (j % m) =
      ∑ j ∈ Finset.range m, cyclicSign (g ^ 2) j +
        ∑ j ∈ Finset.range m, cyclicSign (g ^ 2) j := by
    rw [show 2 * m = m + m by omega, Finset.sum_range_add]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => by
        rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
    · refine Finset.sum_congr rfl fun j hj => by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
  rw [hsplit]; ring

/-- **Dyadic autocorrelation descent inequality**:
for any even-order cyclic subgroup `g^m = -1` and any shift `h`,
`|R_h(g, 2m)| ≤ m + R_h(g², m) + 2` (with the `+ 2` accounting for the at most two indices where
the `2m`-cycle hits `0` or `m`). -/
theorem cyclicAuto_descent (g : F) (m h : ℕ) (hgm : g ^ m = -1) :
    |cyclicAuto g (2 * m) h| ≤ (m : ℤ) + cyclicAuto (g ^ 2) m h + 2 := by
  have hg2m : g ^ (2 * m) = 1 := by
    rw [show 2 * m = m + m by omega, pow_add, hgm]; ring
  have hpow_mod : ∀ k, g ^ (k % (2 * m)) = g ^ k := fun k => by
    conv_rhs => rw [← Nat.div_add_mod k (2 * m)]
    rw [pow_add, pow_mul, hg2m, one_pow, one_mul]
  have hpow2_mod : ∀ k, (g ^ 2) ^ (k % m) = (g ^ 2) ^ k := fun k => by
    have hgm2 : (g ^ 2) ^ m = 1 := by rw [← pow_mul, hg2m]
    conv_rhs => rw [← Nat.div_add_mod k m]
    rw [pow_add, pow_mul, hgm2, one_pow, one_mul]
  have hfold : ∀ k, cyclicSign g k * cyclicSign g (k + m) = cyclicSign (g ^ 2) k := fun k => by
    unfold cyclicSign
    rw [pow_add, hgm, mul_neg_one, sub_neg_eq_add, ← map_mul]
    congr 1; ring
  have hsplit : cyclicAuto g (2 * m) h =
      ∑ j ∈ Finset.range m,
        (cyclicSign g j * cyclicSign g ((j + h) % (2 * m)) +
          cyclicSign g (j + m) * cyclicSign g ((j + m + h) % (2 * m))) := by
    unfold cyclicAuto
    rw [show 2 * m = m + m by omega, Finset.sum_range_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by
      simp only [Nat.add_comm m j]
  have hpair_bound : ∀ j ∈ Finset.range m,
      |cyclicSign g j * cyclicSign g ((j + h) % (2 * m)) +
          cyclicSign g (j + m) * cyclicSign g ((j + m + h) % (2 * m))| ≤
        1 + cyclicSign (g ^ 2) j * cyclicSign (g ^ 2) ((j + h) % m) +
          (if j = 0 then (1 : ℤ) else 0) + (if (j + h) % m = 0 then (1 : ℤ) else 0) := by
    intro j _
    set u := cyclicSign g j * cyclicSign g ((j + h) % (2 * m))
    set v := cyclicSign g (j + m) * cyclicSign g ((j + m + h) % (2 * m))
    have huv : u * v = cyclicSign (g ^ 2) j * cyclicSign (g ^ 2) ((j + h) % m) := by
      have h1 : cyclicSign g ((j + h) % (2 * m)) = cyclicSign g (j + h) := by
        unfold cyclicSign; rw [hpow_mod]
      have h2 : cyclicSign g ((j + m + h) % (2 * m)) = cyclicSign g (j + h + m) := by
        unfold cyclicSign; rw [hpow_mod, show j + m + h = j + h + m by omega]
      have h3 : cyclicSign (g ^ 2) ((j + h) % m) = cyclicSign (g ^ 2) (j + h) := by
        unfold cyclicSign; rw [hpow2_mod]
      dsimp only [u, v]
      rw [h1, h2, h3]
      calc (cyclicSign g j * cyclicSign g (j + h)) * (cyclicSign g (j + m) * cyclicSign g (j + h + m))
          = (cyclicSign g j * cyclicSign g (j + m)) *
              (cyclicSign g (j + h) * cyclicSign g (j + h + m)) := by ring
        _ = cyclicSign (g ^ 2) j * cyclicSign (g ^ 2) (j + h) := by rw [hfold, hfold]
    rw [← huv]
    have hu_val : u = 0 ∨ u = 1 ∨ u = -1 := by
      dsimp only [u, cyclicSign]
      rcases (quadraticChar_isQuadratic F) (1 - g ^ j) with ha | ha | ha <;>
        rcases (quadraticChar_isQuadratic F) (1 - g ^ ((j + h) % (2 * m))) with hb | hb | hb <;>
        simp [ha, hb]
    have hv_val : v = 0 ∨ v = 1 ∨ v = -1 := by
      dsimp only [v, cyclicSign]
      rcases (quadraticChar_isQuadratic F) (1 - g ^ (j + m)) with ha | ha | ha <;>
        rcases (quadraticChar_isQuadratic F) (1 - g ^ ((j + m + h) % (2 * m))) with hb | hb | hb <;>
        simp [ha, hb]
    have hnonneg : 0 ≤ (if j = 0 then (1 : ℤ) else 0) + (if (j + h) % m = 0 then (1 : ℤ) else 0) := by
      split_ifs <;> decide
    rcases hu_val with hu | hu | hu <;> rcases hv_val with hv | hv | hv <;>
      rw [hu, hv] <;> norm_num <;> linarith
  have hsum_j0 : (∑ j ∈ Finset.range m, if j = 0 then (1 : ℤ) else 0) ≤ 1 := by
    by_cases hm0 : m = 0
    · simp [hm0]
    · rw [Finset.sum_ite_eq' (Finset.range m) 0 (fun _ => (1 : ℤ))]
      simp [Nat.pos_of_ne_zero hm0]
  have hsum_jh0 : (∑ j ∈ Finset.range m, if (j + h) % m = 0 then (1 : ℤ) else 0) ≤ 1 := by
    by_cases hm0 : m = 0
    · simp [hm0]
    · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
      set j0 := (m - h % m) % m
      have huniq : ∀ j ∈ Finset.range m, (j + h) % m = 0 → j = j0 := by
        intro j hj hdiv
        have hjlt : j < m := Finset.mem_range.mp hj
        have h1 : (j + h % m) % m = 0 := by rwa [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have hhm : h % m < m := Nat.mod_lt h hm_pos
        dsimp [j0]
        by_cases hh0 : h % m = 0
        · rw [hh0] at h1 ⊢
          rw [add_zero, Nat.mod_eq_of_lt hjlt] at h1
          rw [Nat.sub_zero, Nat.mod_self]; exact h1
        · have hsum_pos : 0 < j + h % m := by omega
          have hsum_lt : j + h % m < 2 * m := by omega
          have hsum_eq : j + h % m = m := by
            have := Nat.dvd_of_mod_eq_zero h1
            obtain ⟨q, hq⟩ := this
            rcases q with _ | _ | q
            · omega
            · omega
            · nlinarith
          rw [show m - h % m = j by omega, Nat.mod_eq_of_lt hjlt]
      calc ∑ j ∈ Finset.range m, (if (j + h) % m = 0 then (1 : ℤ) else 0)
          ≤ ∑ j ∈ Finset.range m, (if j = j0 then (1 : ℤ) else 0) :=
            Finset.sum_le_sum fun j hj => by
              split_ifs with hc hj0
              · exact le_refl _
              · exact absurd (huniq j hj hc) hj0
              · decide
              · exact le_refl _
        _ ≤ 1 := by
            rw [Finset.sum_ite_eq' (Finset.range m) j0]
            split_ifs <;> decide
  calc |cyclicAuto g (2 * m) h|
      ≤ ∑ j ∈ Finset.range m,
          |cyclicSign g j * cyclicSign g ((j + h) % (2 * m)) +
            cyclicSign g (j + m) * cyclicSign g ((j + m + h) % (2 * m))| := by
        rw [hsplit]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range m,
          (1 + cyclicSign (g ^ 2) j * cyclicSign (g ^ 2) ((j + h) % m) +
            (if j = 0 then (1 : ℤ) else 0) + (if (j + h) % m = 0 then (1 : ℤ) else 0)) :=
        Finset.sum_le_sum hpair_bound
    _ = (m : ℤ) + cyclicAuto (g ^ 2) m h +
          (∑ j ∈ Finset.range m, if j = 0 then (1 : ℤ) else 0) +
          (∑ j ∈ Finset.range m, if (j + h) % m = 0 then (1 : ℤ) else 0) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          mul_one, cyclicAuto]
    _ ≤ (m : ℤ) + cyclicAuto (g ^ 2) m h + 2 := by linarith

end ProximityGap.PaleyDyadicTower

#print axioms ProximityGap.PaleyDyadicTower.abs_antipodal_pair_eq
#print axioms ProximityGap.PaleyDyadicTower.sq_antipodal_pair_eq
#print axioms ProximityGap.PaleyDyadicTower.sum_abs_antipodal_eq
#print axioms ProximityGap.PaleyDyadicTower.sum_sq_antipodal_eq
#print axioms ProximityGap.PaleyDyadicTower.dyadic_row_descent
#print axioms ProximityGap.PaleyDyadicTower.dyadic_rectangle_descent
#print axioms ProximityGap.PaleyDyadicTower.cyclicAuto_half_eq
#print axioms ProximityGap.PaleyDyadicTower.cyclicAuto_descent
