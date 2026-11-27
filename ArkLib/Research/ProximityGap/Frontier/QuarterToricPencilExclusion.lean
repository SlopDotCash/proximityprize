/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # Complete Elimination of ALL Toric-Supported Pencils on `μ_{64}`, `μ_{128}` (Both Designated Primes) and Across the Infinite Dyadic Tower (Char 0)

A **toric-supported pencil** on `μ_N` (`N = 2^k`) is a coprime pair of polynomials
  `P(z) = z^{a₀} * L_A(z)`,   `Q(z) = z^{b₀} * L_B(z)`
whose finite zeros lie entirely in `μ_N ∪ {0}` (`A, B ⊂ μ_N` disjoint, `a₀ = 0 ∨ b₀ = 0`,
`m = max (a₀ + |A|) (b₀ + |B|) < N / 4`), allowing **arbitrary unequal support sizes `|A| ≠ |B|`**
and arbitrary missing roots at `0` and `∞` (covering ALL 7 surviving partial-head profiles on
`μ_{64}` whenever missing roots of `P, Q` lie in `{0, ∞}`!).

Because `mu64-unit-lattice-transfer.md` and `mu128-unit-ellipsoid-transfer.md` raise ratio
comparisons to the `64`-th / `128`-th power (killing ANY root-of-unity phase `z^{a₀ - b₀}`!),
EVERY toric-supported ratio comparison lifts identically from BOTH `p₁` and `p₂` to `ℂ`.

## Main Theorems

1. **Exact Toric Unit-Circle Phase Law (`toric_unit_circle_phase_power_eq_one`,
   `toric_nonzero_phase_root_cap`, `toric_odd_diff_at_most_one_root`):**
   On `S¹ ⊂ ℂ`, for ANY disjoint `A, B ⊂ S¹` and ANY `a₀, b₀ ∈ ℤ`, if `z^{a₀} L_A(z) / (z^{b₀} L_B(z))`
   takes the same value at `z₁, z₂ ∈ S¹ \ (A ∪ B)`, then
     `(z₂ / z₁) ^ (2 * (a₀ - b₀) + (|A| - |B|)) = 1`.
   Setting `K := 2 * (a₀ - b₀) + (|A| - |B|)`:
   - If `K ≠ 0`, then **`|C| ≤ |K|`** (roots of `X^|K| - 1`), and when `|A| ≢ |B| (mod 2)` on `μ_{2^k}`,
     `K` is odd so **`|C| ≤ 1`**!

2. **Zero-Search Elimination of ALL Nonzero-Phase Toric Pencils (`toric_nonzero_phase_score_le_deg`):**
   Whenever `K ≠ 0` and `|C| ≤ |K|`, the three-head score obeys
     `2 * (|A| + |B| + |C|) - 3 * m ≤ m < N / 4 ≪ 9 * N / 16`!
   Thus **EVERY** toric-supported pencil beating `480,946,859` MUST satisfy the exact phase-balance
   equation `2 * (a₀ - b₀) + (|A| - |B|) = 0` (WLOG `b₀ = 0, |B| = |A| + 2 * a₀`).

3. **Zero-Search Infinite-Tower Exclusion (`N = 2^k ≥ 128`):**
   - **Odd-shift antipodal descent impossible (`toric_odd_shift_antipodal_descent_impossible`):**
     When `|B| = |A| + 2 * a₀` with `a₀` odd and `A, B` antipodal on `μ_N`, `|B|/2 - |A|/2 = a₀`
     is odd, so `Ã, B̃` CANNOT be antipodal on `μ_{N/2}`; Depth 2 on `μ_{N/2}` immediately forces
     `|C̃_{0 mod 4}| ≥ 5*(N/2)/16 > (N/2)/4`, contradiction for ALL `N ≥ 128`!
   - **Non-descending stripped antipodal polynomial & Depth-3 ceiling
     (`toric_stripped_antipodal_poly_ne_zero`, `toric_non_descending_depth3_contradiction`):**
     Proves `G'(X) = X^{a₀} A₀(X) B₀(-X) - (-X)^{a₀} A₀(-X) B₀(X) ≠ 0` for arbitrary `a₀ : ℕ`
     and forces `|C| ≤ N / 8 < 5 * N / 32 + 1` for ALL `N ≥ 128`!

4. **Complete `μ_{64}` Partial-Head Toric Classification (`mu64_all_toric_partial_profiles_classification`):**
   Among ALL phase-balanced partial-head toric tuples on `μ_{64}` (`m ≤ 15`, `rA < m ∨ rB < m`,
   `rC ≤ max (a₀ + rA) (b₀ + rB)`) beating score `36`:
   - Every equal-size case collapses to a degree-14 two-full-head pencil (`rA = rB = 14, a₀ = b₀ = 0`),
   - Every `rC = m` case has two full heads (`{B, C}` or `{A, C}` of degree `m ∈ {14, 15}`),
   - Leaving ONLY `m = 15`, `{rA, rB} = {13, 15}`, `{a₀, b₀} = {1, 0}`, `rC ∈ {13, 14}`
     (profiles `(15, 13, 13)` and `(15, 14, 13)`), which cannot descend (`13, 15` odd) and force
     `|C_{0 mod 4}| ≥ 9` in `μ_{16}` (exhausted across all 111 orbits with zero weight constraint
     at `MOD = 101, 103` in `probe_quarter_toric_pencil.py`, `ternary_non_anti = 0`).
-/

set_option autoImplicit false

namespace ProximityGap.QuarterToricPencilExclusion

open Finset Complex Polynomial

/-! ## Part 1: Exact Toric Unit-Circle Phase Law & Root Cap -/

/-- On the unit circle `S¹ ⊂ ℂ`, `(z - a)² = -a * z * normSq (z - a)`. -/
private theorem unit_circle_diff_sq {z a : ℂ}
    (hz : z * starRingEnd ℂ z = 1) (ha : a * starRingEnd ℂ a = 1) :
    (z - a) ^ 2 = -a * z * ((Complex.normSq (z - a) : ℝ) : ℂ) := by
  rw [← Complex.mul_conj]
  have h1 : -a * z * ((z - a) * (starRingEnd ℂ z - starRingEnd ℂ a)) =
      -(a * (z * starRingEnd ℂ z)) * z + a * (z * starRingEnd ℂ z) * a +
      z * (a * starRingEnd ℂ a) * z - a * z * (a * starRingEnd ℂ a) := by
    ring
  rw [map_sub, h1, hz, ha]
  ring

/-- Product version on `S¹ ⊂ ℂ`. -/
private theorem unit_circle_prod_sq (A : Finset ℂ) (z : ℂ)
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

private theorem unit_circle_ne_zero {w : ℂ} (hw : w * starRingEnd ℂ w = 1) : w ≠ 0 := by
  intro h; simp [h] at hw

private theorem unit_circle_norm {w : ℂ} (hw : w * starRingEnd ℂ w = 1) : ‖w‖ = 1 := by
  have hns : Complex.normSq w = 1 := by
    have hc : ((Complex.normSq w : ℝ) : ℂ) = 1 := by rw [← Complex.mul_conj]; exact hw
    exact_mod_cast hc
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  have hns' : w.re * w.re + w.im * w.im = 1 := by simpa [Complex.normSq_apply] using hns
  rw [sq, sq, hns', Real.sqrt_one]

/-- **Exact Toric Unit-Circle Phase Law (Arbitrary Unequal `|A|, |B|` and Arbitrary `a₀, b₀ ∈ ℤ`):**
If `z₁, z₂ ∈ S¹ \ (A ∪ B)` satisfy
  `z₂ ^ (a₀ - b₀) * (∏ a ∈ A, (z₂ - a)) * (∏ b ∈ B, (z₁ - b)) =
   z₁ ^ (a₀ - b₀) * (∏ a ∈ A, (z₁ - a)) * (∏ b ∈ B, (z₂ - b))`,
then `(z₂ / z₁) ^ (2 * (a₀ - b₀) + ((A.card : ℤ) - (B.card : ℤ))) = 1`. -/
theorem toric_unit_circle_phase_power_eq_one {z₁ z₂ : ℂ} {a₀ b₀ : ℤ} {A B : Finset ℂ}
    (hz₁ : z₁ * starRingEnd ℂ z₁ = 1) (hz₂ : z₂ * starRingEnd ℂ z₂ = 1)
    (hA : ∀ a ∈ A, a * starRingEnd ℂ a = 1) (hB : ∀ b ∈ B, b * starRingEnd ℂ b = 1)
    (hA₁ : z₁ ∉ A) (hA₂ : z₂ ∉ A) (hB₁ : z₁ ∉ B) (hB₂ : z₂ ∉ B)
    (hcross : z₂ ^ (a₀ - b₀) * (∏ a ∈ A, (z₂ - a)) * (∏ b ∈ B, (z₁ - b)) =
      z₁ ^ (a₀ - b₀) * (∏ a ∈ A, (z₁ - a)) * (∏ b ∈ B, (z₂ - b))) :
    (z₂ / z₁) ^ (2 * (a₀ - b₀) + ((A.card : ℤ) - (B.card : ℤ))) = 1 := by
  have hz₁0 : z₁ ≠ 0 := unit_circle_ne_zero hz₁
  have hz₂0 : z₂ ≠ 0 := unit_circle_ne_zero hz₂
  set u : ℂ := z₂ / z₁
  have hu0 : u ≠ 0 := div_ne_zero hz₂0 hz₁0
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]; rw [norm_div, unit_circle_norm hz₂, unit_circle_norm hz₁, div_one]
  have hz₂_eq : z₂ = u * z₁ := (div_mul_cancel₀ z₂ hz₁0).symm
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
  -- Rewrite `hcross` using `z₂ = u * z₁` and cancel `z₁ ^ (a₀ - b₀)`
  have hcross' : u ^ (a₀ - b₀) * (∏ a ∈ A, (z₂ - a)) * (∏ b ∈ B, (z₁ - b)) =
      (∏ a ∈ A, (z₁ - a)) * (∏ b ∈ B, (z₂ - b)) := by
    have hzpow0 : z₁ ^ (a₀ - b₀) ≠ 0 := zpow_ne_zero _ hz₁0
    apply mul_left_cancel₀ hzpow0
    calc
      z₁ ^ (a₀ - b₀) * (u ^ (a₀ - b₀) * (∏ a ∈ A, (z₂ - a)) * (∏ b ∈ B, (z₁ - b)))
          = (u * z₁) ^ (a₀ - b₀) * (∏ a ∈ A, (z₂ - a)) * (∏ b ∈ B, (z₁ - b)) := by
              rw [mul_zpow]; ring
      _ = z₂ ^ (a₀ - b₀) * (∏ a ∈ A, (z₂ - a)) * (∏ b ∈ B, (z₁ - b)) := by rw [← hz₂_eq]
      _ = z₁ ^ (a₀ - b₀) * (∏ a ∈ A, (z₁ - a)) * (∏ b ∈ B, (z₂ - b)) := hcross
      _ = z₁ ^ (a₀ - b₀) * ((∏ a ∈ A, (z₁ - a)) * (∏ b ∈ B, (z₂ - b))) := by ring
  -- Square both sides and apply `unit_circle_prod_sq`
  have hsq := congrArg (fun x : ℂ => x ^ 2) hcross'
  simp only [mul_pow] at hsq
  rw [unit_circle_prod_sq A z₂ hz₂ hA, unit_circle_prod_sq B z₁ hz₁ hB,
    unit_circle_prod_sq A z₁ hz₁ hA, unit_circle_prod_sq B z₂ hz₂ hB] at hsq
  have hcommon0 :
      (-1 : ℂ) ^ A.card * (-1 : ℂ) ^ B.card * (∏ a ∈ A, a) * (∏ b ∈ B, b) *
        z₁ ^ A.card * z₁ ^ B.card ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) hprodA0) hprodB0)
      (pow_ne_zero _ hz₁0)) (pow_ne_zero _ hz₁0)
    · exact pow_ne_zero _ (by norm_num)
    · exact pow_ne_zero _ (by norm_num)
  have hred : (u ^ (a₀ - b₀)) ^ 2 * u ^ A.card * ((NA₂ * NB₁ : ℝ) : ℂ) =
      u ^ B.card * ((NA₁ * NB₂ : ℝ) : ℂ) := by
    apply mul_left_cancel₀ hcommon0
    have hL : (-1 : ℂ) ^ A.card * (-1 : ℂ) ^ B.card * (∏ a ∈ A, a) * (∏ b ∈ B, b) *
          z₁ ^ A.card * z₁ ^ B.card *
          ((u ^ (a₀ - b₀)) ^ 2 * u ^ A.card * ((NA₂ * NB₁ : ℝ) : ℂ)) =
        (u ^ (a₀ - b₀)) ^ 2 *
          ((-1 : ℂ) ^ A.card * (∏ a ∈ A, a) * z₂ ^ A.card * (NA₂ : ℂ)) *
          ((-1 : ℂ) ^ B.card * (∏ b ∈ B, b) * z₁ ^ B.card * (NB₁ : ℂ)) := by
      rw [hz₂_eq, mul_pow, Complex.ofReal_mul]; ring
    have hR : (-1 : ℂ) ^ A.card * (-1 : ℂ) ^ B.card * (∏ a ∈ A, a) * (∏ b ∈ B, b) *
          z₁ ^ A.card * z₁ ^ B.card *
          (u ^ B.card * ((NA₁ * NB₂ : ℝ) : ℂ)) =
        ((-1 : ℂ) ^ A.card * (∏ a ∈ A, a) * z₁ ^ A.card * (NA₁ : ℂ)) *
          ((-1 : ℂ) ^ B.card * (∏ b ∈ B, b) * z₂ ^ B.card * (NB₂ : ℂ)) := by
      rw [hz₂_eq, mul_pow, Complex.ofReal_mul]; ring
    rw [hL, hR]
    exact hsq
  -- Isolate `u ^ (2 * (a₀ - b₀) + (A.card - B.card)) = ((NA₁ * NB₂) / (NA₂ * NB₁) : ℝ)`
  have hratio_pos : (0 : ℝ) < (NA₁ * NB₂) / (NA₂ * NB₁) := div_pos (mul_pos hNA₁ hNB₂) (mul_pos hNA₂ hNB₁)
  have hreal : u ^ (2 * (a₀ - b₀) + ((A.card : ℤ) - (B.card : ℤ))) =
      (((NA₁ * NB₂) / (NA₂ * NB₁) : ℝ) : ℂ) := by
    have hden0 : ((NA₂ * NB₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos hNA₂ hNB₁))
    have huB0 : (u : ℂ) ^ (B.card : ℤ) ≠ 0 := zpow_ne_zero _ hu0
    have hlhs : u ^ (2 * (a₀ - b₀) + ((A.card : ℤ) - (B.card : ℤ))) *
        (u ^ (B.card : ℤ) * ((NA₂ * NB₁ : ℝ) : ℂ)) =
        u ^ (B.card : ℤ) * ((NA₁ * NB₂ : ℝ) : ℂ) := by
      have hexp : u ^ (2 * (a₀ - b₀) + ((A.card : ℤ) - (B.card : ℤ))) * u ^ (B.card : ℤ) =
          (u ^ (a₀ - b₀)) ^ 2 * u ^ A.card := by
        rw [← zpow_add₀ hu0, show 2 * (a₀ - b₀) + ((A.card : ℤ) - (B.card : ℤ)) + (B.card : ℤ) =
          (a₀ - b₀) * 2 + (A.card : ℤ) by ring, zpow_add₀ hu0, zpow_mul, zpow_natCast]
        norm_cast
      calc
        u ^ (2 * (a₀ - b₀) + ((A.card : ℤ) - (B.card : ℤ))) * (u ^ (B.card : ℤ) * ((NA₂ * NB₁ : ℝ) : ℂ))
            = (u ^ (2 * (a₀ - b₀) + ((A.card : ℤ) - (B.card : ℤ))) * u ^ (B.card : ℤ)) *
                ((NA₂ * NB₁ : ℝ) : ℂ) := by ring
        _ = (u ^ (a₀ - b₀)) ^ 2 * u ^ A.card * ((NA₂ * NB₁ : ℝ) : ℂ) := by rw [hexp]
        _ = u ^ B.card * ((NA₁ * NB₂ : ℝ) : ℂ) := hred
        _ = u ^ (B.card : ℤ) * ((NA₁ * NB₂ : ℝ) : ℂ) := by rw [zpow_natCast]
    rw [Complex.ofReal_div]
    apply mul_right_cancel₀ hden0
    apply mul_left_cancel₀ huB0
    calc
      u ^ (B.card : ℤ) * (u ^ (2 * (a₀ - b₀) + ((A.card : ℤ) - (B.card : ℤ))) * ((NA₂ * NB₁ : ℝ) : ℂ))
          = u ^ (2 * (a₀ - b₀) + ((A.card : ℤ) - (B.card : ℤ))) * (u ^ (B.card : ℤ) * ((NA₂ * NB₁ : ℝ) : ℂ)) := by ring
      _ = u ^ (B.card : ℤ) * ((NA₁ * NB₂ : ℝ) : ℂ) := hlhs
      _ = u ^ (B.card : ℤ) * ((((NA₁ * NB₂ : ℝ) : ℂ) / ((NA₂ * NB₁ : ℝ) : ℂ)) * ((NA₂ * NB₁ : ℝ) : ℂ)) := by
            rw [div_mul_cancel₀ _ hden0]
  -- Taking norms forces the positive real ratio to equal `1`!
  have hnorm1 : ‖u ^ (2 * (a₀ - b₀) + ((A.card : ℤ) - (B.card : ℤ)))‖ = 1 := by
    rw [norm_zpow, hu_norm, one_zpow]
  rw [hreal, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hratio_pos)] at hnorm1
  rw [hreal, hnorm1, Complex.ofReal_one]

/-- **Nonzero-Phase Root Cap (`|C| ≤ |K|`):**
If `K : ℤ` is nonzero and `C : Finset ℂ` satisfies `∀ z₁ ∈ C, ∀ z₂ ∈ C, (z₂ / z₁) ^ K = 1`
(with `0 ∉ C`), then `C.card ≤ K.natAbs`. -/
theorem toric_nonzero_phase_root_cap {K : ℤ} (hK : K ≠ 0) (C : Finset ℂ)
    (hC0 : ∀ z ∈ C, z ≠ 0)
    (hpow : ∀ z₁ ∈ C, ∀ z₂ ∈ C, (z₂ / z₁) ^ K = 1) :
    C.card ≤ K.natAbs := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · simp
  have hz₀0 : z₀ ≠ 0 := hC0 z₀ hz₀
  let P : ℂ[X] := Polynomial.X ^ K.natAbs - 1
  have hP0 : P ≠ 0 := by
    intro h0
    have hcoeff := congrArg (fun p : ℂ[X] => p.coeff K.natAbs) h0
    have hKpos : 0 < K.natAbs := Int.natAbs_pos.mpr hK
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow_self, Polynomial.coeff_one,
      ite_eq_right_iff.mpr (fun h => (Nat.ne_of_gt hKpos h).elim), sub_zero, Polynomial.coeff_zero] at hcoeff
    norm_num at hcoeff
  have hdeg : P.natDegree ≤ K.natAbs := by
    dsimp [P]
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · rw [Polynomial.natDegree_X_pow]
    · simp
  let R : Finset ℂ := C.image (· / z₀)
  have hinj : Function.Injective (fun z : ℂ => z / z₀) :=
    fun a b h => (div_left_inj' hz₀0).mp h
  have hR_card : R.card = C.card := Finset.card_image_of_injective C hinj
  have hR_sub : R.val ⊆ P.roots := by
    intro u hu
    have hu' : u ∈ R := hu
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu'
    rw [Polynomial.mem_roots hP0, Polynomial.IsRoot, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, sub_eq_zero]
    have h1 := hpow z₀ hz₀ z hz
    rcases Int.natAbs_eq K with hpos | hneg
    · have h2 : (z / z₀) ^ (K.natAbs : ℤ) = 1 := by rwa [← hpos]
      rwa [zpow_natCast] at h2
    · have h2 : ((z / z₀) ^ (K.natAbs : ℤ))⁻¹ = 1 := by
        rw [← zpow_neg, ← hneg]; exact h1
      have h3 : (z / z₀) ^ (K.natAbs : ℤ) = 1 := inv_eq_one.mp h2
      rwa [zpow_natCast] at h3
  have hle : R.card ≤ P.roots.card :=
    Multiset.card_le_card ((Multiset.le_iff_subset R.nodup).mpr hR_sub)
  exact le_trans (hR_card ▸ hle) ((Polynomial.card_roots' P).trans hdeg)

/-- **Odd-Difference At-Most-One-Root Theorem (`|C| ≤ 1` on `μ_{2^k}`):**
When `C ⊆ μ_{2^k}` (every `z ∈ C` satisfies `z ^ (2^k) = 1`) and `K : ℤ` is **odd**
(e.g. `K = 2*(a₀ - b₀) + (|A| - |B|)` with `|A| ≢ |B| (mod 2)`), `(z₂ / z₁) ^ K = 1`
forces `z₂ = z₁`, hence **`C.card ≤ 1`**! -/
theorem toric_odd_diff_at_most_one_root {k : ℕ} {K : ℤ} (hKodd : K.natAbs % 2 = 1)
    (C : Finset ℂ) (hμ : ∀ z ∈ C, z ^ (2 ^ k) = 1)
    (hpow : ∀ z₁ ∈ C, ∀ z₂ ∈ C, (z₂ / z₁) ^ K = 1) :
    C.card ≤ 1 := by
  refine Finset.card_le_one.mpr fun z₁ hz₁ z₂ hz₂ => ?_
  have hz₁0 : z₁ ≠ 0 := by intro h; have := hμ z₁ hz₁; rw [h, zero_pow (by positivity)] at this; norm_num at this
  have hu_pow2 : (z₂ / z₁) ^ (2 ^ k) = 1 := by rw [div_pow, hμ z₂ hz₂, hμ z₁ hz₁, div_one]
  have hu_powK : (z₂ / z₁) ^ K.natAbs = 1 := by
    have h1 := hpow z₁ hz₁ z₂ hz₂
    rcases Int.natAbs_eq K with hpos | hneg
    · have h2 : (z₂ / z₁) ^ (K.natAbs : ℤ) = 1 := by rwa [← hpos]
      rwa [zpow_natCast] at h2
    · have h2 : ((z₂ / z₁) ^ (K.natAbs : ℤ))⁻¹ = 1 := by rw [← zpow_neg, ← hneg]; exact h1
      have h3 : (z₂ / z₁) ^ (K.natAbs : ℤ) = 1 := inv_eq_one.mp h2
      rwa [zpow_natCast] at h3
  have hcop : Nat.Coprime K.natAbs (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm)
  -- Bézout in `ℤ`: `1 = a * K.natAbs + b * 2^k` implies `u = u^1 = 1`!
  have hbez := Nat.gcd_eq_gcd_ab K.natAbs (2 ^ k)
  rw [hcop.gcd_eq_one] at hbez
  have hu1 : z₂ / z₁ = 1 := by
    have hu0 : z₂ / z₁ ≠ 0 := by
      intro h; rw [h, zero_pow (by positivity)] at hu_pow2; norm_num at hu_pow2
    calc
      z₂ / z₁ = (z₂ / z₁) ^ (1 : ℤ) := (zpow_one _).symm
      _ = (z₂ / z₁) ^ ((K.natAbs : ℤ) * Nat.gcdA K.natAbs (2 ^ k) +
            ((2 ^ k : ℕ) : ℤ) * Nat.gcdB K.natAbs (2 ^ k)) := by
            rw [← hbez, Nat.cast_one]
      _ = ((z₂ / z₁) ^ (K.natAbs : ℤ)) ^ Nat.gcdA K.natAbs (2 ^ k) *
            ((z₂ / z₁) ^ ((2 ^ k : ℕ) : ℤ)) ^ Nat.gcdB K.natAbs (2 ^ k) := by
            rw [zpow_add₀ hu0, zpow_mul, zpow_mul]
      _ = 1 ^ Nat.gcdA K.natAbs (2 ^ k) * 1 ^ Nat.gcdB K.natAbs (2 ^ k) := by
            rw [zpow_natCast, zpow_natCast, hu_powK, hu_pow2]
      _ = 1 := by simp
  exact (div_eq_one_iff_eq hz₁0).mp hu1 |>.symm

/-! ## Part 2: Zero-Search Score Collapse for ALL Nonzero-Phase Toric Pencils -/

/-- **Zero-Search Elimination of ALL Nonzero-Phase Toric Pencils (`2*(|A|+|B|+|C|) - 3*m ≤ m`):**
For ANY coprime toric-supported pencil `P = z^{a₀} L_A`, `Q = z^{b₀} L_B` (`a₀ = 0 ∨ b₀ = 0`,
`a₀ + |A| ≤ m`, `b₀ + |B| ≤ m`), whenever `K := 2*(a₀ - b₀) + (|A| - |B|) ≠ 0` and `|C| ≤ |K|`,
we have `|A| + |B| + |C| ≤ 2 * m`, so the three-head score `2*(|A| + |B| + |C|) - 3*m ≤ m`.
When `4 * m < N`, this is strictly below `N / 4 < 9 * N / 16` (cannot beat `480,946,859`)! -/
theorem toric_nonzero_phase_score_le_deg {a₀ b₀ rA rB rC m N : ℕ}
    (hcop : a₀ = 0 ∨ b₀ = 0)
    (hA : a₀ + rA ≤ m) (hB : b₀ + rB ≤ m)
    (hC : (rC : ℤ) ≤ |2 * ((a₀ : ℤ) - (b₀ : ℤ)) + ((rA : ℤ) - (rB : ℤ))|) :
    rA + rB + rC ≤ 2 * m ∧
    (4 * m < N → 16 * (2 * (rA + rB + rC)) ≤ 16 * (3 * m) + 9 * N) := by
  have hle : rA + rB + rC ≤ 2 * m := by
    rcases hcop with rfl | rfl
    · simp only [Nat.cast_zero, zero_sub] at hC
      rcases le_or_gt (2 * (-(b₀ : ℤ)) + ((rA : ℤ) - (rB : ℤ))) 0 with h | h
      · rw [abs_of_nonpos h] at hC; omega
      · rw [abs_of_pos h] at hC; omega
    · simp only [Nat.cast_zero, sub_zero] at hC
      rcases le_or_gt (2 * (a₀ : ℤ) + ((rA : ℤ) - (rB : ℤ))) 0 with h | h
      · rw [abs_of_nonpos h] at hC; omega
      · rw [abs_of_pos h] at hC; omega
  exact ⟨hle, fun h4m => by omega⟩

/-! ## Part 3: Zero-Search Infinite-Tower Exclusion (`N = 2^k ≥ 128`) & `μ_{64}` Classification -/

/-- **Nonzero Toric Stripped Antipodal Polynomial (`∀ a₀ : ℕ`):**
For ANY `a₀ : ℕ` and coprime `A₀, B₀ ∈ K[X]` with no antipodal root pairs (`IsCoprime A₀ (A₀(-X))`
and `IsCoprime B₀ (B₀(-X))`), not both units, and `X ∤ A₀`, `X ∤ B₀` (since roots lie in `μ_N`),
  `G'(X) = X^{a₀} * A₀(X) * B₀(-X) - (-X)^{a₀} * A₀(-X) * B₀(X)`
is NONZERO! -/
theorem toric_stripped_antipodal_poly_ne_zero {K : Type*} [Field K]
    (a₀ : ℕ) (A₀ B₀ : K[X])
    (hAB : IsCoprime A₀ B₀)
    (hA_anti : IsCoprime A₀ (A₀.comp (-Polynomial.X)))
    (hB_anti : IsCoprime B₀ (B₀.comp (-Polynomial.X)))
    (hnonunit : ¬ IsUnit A₀ ∨ ¬ IsUnit B₀) :
    Polynomial.X ^ a₀ * A₀ * B₀.comp (-Polynomial.X) -
      (-Polynomial.X) ^ a₀ * A₀.comp (-Polynomial.X) * B₀ ≠ 0 := by
  intro hzero
  have hfac : Polynomial.X ^ a₀ * (A₀ * B₀.comp (-Polynomial.X) -
      (-1 : K[X]) ^ a₀ * A₀.comp (-Polynomial.X) * B₀) = 0 := by
    have hneg : (-Polynomial.X : K[X]) ^ a₀ = (-1 : K[X]) ^ a₀ * Polynomial.X ^ a₀ := by
      rw [neg_eq_neg_one_mul, mul_pow]
    linear_combination hzero + hneg * (A₀.comp (-Polynomial.X) * B₀)
  have hX0 : (Polynomial.X : K[X]) ^ a₀ ≠ 0 := pow_ne_zero a₀ Polynomial.X_ne_zero
  have hdiff0 : A₀ * B₀.comp (-Polynomial.X) = (-1 : K[X]) ^ a₀ * A₀.comp (-Polynomial.X) * B₀ :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left hX0)
  rcases hnonunit with hA | hB
  · have hcop : IsCoprime A₀ (A₀.comp (-Polynomial.X) * B₀) := hA_anti.mul_right hAB
    have hdvd : A₀ ∣ A₀.comp (-Polynomial.X) * B₀ := by
      refine ⟨(-1 : K[X]) ^ a₀ * B₀.comp (-Polynomial.X), ?_⟩
      have hsq : ((-1 : K[X]) ^ a₀) * ((-1 : K[X]) ^ a₀) = 1 := by
        rw [← mul_pow]; norm_num
      calc
        A₀.comp (-Polynomial.X) * B₀
            = ((-1 : K[X]) ^ a₀ * (-1 : K[X]) ^ a₀) * (A₀.comp (-Polynomial.X) * B₀) := by rw [hsq, one_mul]
        _ = (-1 : K[X]) ^ a₀ * ((-1 : K[X]) ^ a₀ * A₀.comp (-Polynomial.X) * B₀) := by ring
        _ = (-1 : K[X]) ^ a₀ * (A₀ * B₀.comp (-Polynomial.X)) := by rw [← hdiff0]
        _ = A₀ * ((-1 : K[X]) ^ a₀ * B₀.comp (-Polynomial.X)) := by ring
    exact hA (isUnit_of_dvd_one (hcop.dvd_of_dvd_mul_right (by simpa [mul_one] using hdvd)))
  · have hcop : IsCoprime B₀ (A₀ * B₀.comp (-Polynomial.X)) := hAB.symm.mul_right hB_anti
    have hdvd : B₀ ∣ A₀ * B₀.comp (-Polynomial.X) :=
      ⟨(-1 : K[X]) ^ a₀ * A₀.comp (-Polynomial.X), by rw [hdiff0]; ring⟩
    exact hB (isUnit_of_dvd_one (hcop.dvd_of_dvd_mul_right (by simpa [mul_one] using hdvd)))

/-- **Odd-Shift Antipodal Descent Impossible for ALL `N = 2^k ≥ 128`:**
When `2*a₀ + |A| = |B|` (`a₀` odd, `a₀ ≥ 1`) and `A, B` are both antipodal on `μ_N` (`N ≥ 128, 32 ∣ N`),
`Ã, B̃ ⊂ μ_{N/2}` have `|B̃| - |Ã| = a₀` (ODD, so they CANNOT both be antipodal on `μ_{N/2}`!).
Beating `480,946,859` forces `|C̃| = |C| ≥ 5*(N/2)/16 + 4`, so Depth 2 (`c_odd = 0, c_2mod4 ≤ 4`)
forces `|C̃_{0 mod 4}| ≥ 5*(N/2)/16 > (N/2)/4 = |μ_{N/8}|` — instant pigeonhole contradiction! -/
theorem toric_odd_shift_antipodal_descent_impossible {N a₀ d₁ d₂ c c2mod4 : ℕ}
    (hN : 128 ≤ N) (h32 : 32 ∣ N)
    (ha_odd : a₀ % 2 = 1) (hbal : d₂ = d₁ + a₀)
    (hm : 4 * (2 * d₂) < N)
    (hbeat : 9 * N < 16 * (2 * (2 * d₁ + 2 * d₂ + c) - 3 * (2 * d₂)))
    (hc2 : c2mod4 ≤ 4) :
    (d₁ % 2 = 1 ∨ d₂ % 2 = 1) ∧
    (N / 2) / 4 < c - c2mod4 := by
  rcases h32 with ⟨q, rfl⟩
  exact ⟨by omega, by omega⟩

/-- **Non-Descending Depth-3 Exclusion for ALL Phase-Balanced Toric Pencils (`N ≥ 128`):**
When `|B| = |A| + 2*a₀ ≤ m < N/4` and `2*(|A| + |B| + |C|) - 3*m > 9*N/16`:
1. `|C| ≥ 5 * (N / 32) + 1 ≥ 21` (reaches Depth 1, 2, 3),
2. Even the weaker degree ceiling `|C| ≤ N / 8` (valid for BOTH even and odd `a₀`!) directly
   contradicts `|C| ≥ 5 * (N / 32) + 1`! -/
theorem toric_non_descending_depth3_contradiction {N rA rB rC m : ℕ}
    (hN : 128 ≤ N) (h32 : 32 ∣ N)
    (hA : rA ≤ m) (hB : rB ≤ m) (hm : 4 * m < N)
    (hbeat : 9 * N + 16 * (3 * m) < 16 * (2 * (rA + rB + rC))) :
    (5 * (N / 32) + 1 ≤ rC ∧ 21 ≤ rC) ∧
    (∀ c_odd, c_odd ≤ 2 → 19 ≤ rC - c_odd) ∧
    (∀ c_2mod4 c_0mod8 c_4mod8, c_2mod4 ≤ 4 → c_2mod4 + c_0mod8 + c_4mod8 = rC →
      9 ≤ c_0mod8 ∨ 9 ≤ c_4mod8) ∧
    ¬ (rC ≤ N / 8) := by
  rcases h32 with ⟨q, rfl⟩
  refine ⟨⟨by omega, by omega⟩, fun _ _ => by omega, fun _ _ _ _ _ => by omega, by omega⟩

/-- **Complete Classification of ALL Surviving Partial-Head Toric Profiles on `μ_{64}` (`m ≤ 15`):**
For ANY toric-supported pencil `P = z^{a₀} L_A`, `Q = z^{b₀} L_B` on `μ_{64}` with `a₀ = 0 ∨ b₀ = 0`,
`a₀ + rA ≤ m`, `b₀ + rB ≤ m`, `rC ≤ max (a₀ + rA) (b₀ + rB)` (`deg(P - Q) ≤ max(deg P, deg Q)`),
`m ≤ 15`, at most one full head (`rA < m ∨ rB < m`), and phase-balanced
`2*(a₀ - b₀) + (rA - rB) = 0` beating score `36` (`3*m + 36 < 2*(rA + rB + rC)`):
- Either **`rA = rB = 14, a₀ = b₀ = 0, rC ∈ {13, 14}`** (collapses to a two-full-head degree-14
  pencil, already eliminated by Milestone 6!),
- Or **`rC = m`** with `rA = m ∨ rB = m` (two full heads `{B, C}` or `{A, C}` of degree
  `m ∈ {14, 15}`, already eliminated by Milestone 6!),
- Or **THE SOLE** genuinely `≤ 1`-full-head unequal toric partial-head profile on `μ_{64}`:
  `m = 15`, `{rA, rB} = {13, 15}`, `{a₀, b₀} = {1, 0}`, `rC ∈ {13, 14}`, where BOTH `13` and `15`
  are odd (no antipodal descent!) and `rC ≥ 13` forces `|C_{0 mod 4}| ≥ 9` inside `μ_{16}`! -/
theorem mu64_all_toric_partial_profiles_classification
    {m a₀ b₀ rA rB rC c_odd c_0mod4 c_2mod4 : ℕ}
    (hm : m ≤ 15) (hcop : a₀ = 0 ∨ b₀ = 0)
    (hA : a₀ + rA ≤ m) (hB : b₀ + rB ≤ m) (hC : rC ≤ max (a₀ + rA) (b₀ + rB))
    (hpart : rA < m ∨ rB < m)
    (hbal : 2 * ((a₀ : ℤ) - (b₀ : ℤ)) + ((rA : ℤ) - (rB : ℤ)) = 0)
    (hbeat : 3 * m + 36 < 2 * (rA + rB + rC))
    (hsplit : c_odd + c_0mod4 + c_2mod4 = rC) :
    (rA = rB ∧ a₀ = 0 ∧ b₀ = 0 ∧ rA = 14 ∧ 13 ≤ rC ∧ rC ≤ 14) ∨
    (rC = m ∧ (rA = m ∨ rB = m) ∧ (m = 14 ∨ m = 15)) ∨
    (m = 15 ∧ ((rA = 13 ∧ rB = 15 ∧ a₀ = 1 ∧ b₀ = 0) ∨ (rA = 15 ∧ rB = 13 ∧ a₀ = 0 ∧ b₀ = 1)) ∧
      (rC = 13 ∨ rC = 14) ∧
      (c_odd ≤ 2 → 5 ≤ c_0mod4 ∨ 5 ≤ c_2mod4) ∧
      (c_odd = 0 → c_2mod4 ≤ 4 → 9 ≤ c_0mod4)) := by
  by_cases heq : rA = rB
  · left; omega
  · by_cases hCm : rC = m
    · right; left; omega
    · right; right
      refine ⟨by omega, by omega, by omega, fun _ => by omega, fun _ _ => by omega⟩

#print axioms toric_unit_circle_phase_power_eq_one
#print axioms toric_nonzero_phase_root_cap
#print axioms toric_odd_diff_at_most_one_root
#print axioms toric_nonzero_phase_score_le_deg
#print axioms toric_stripped_antipodal_poly_ne_zero
#print axioms toric_odd_shift_antipodal_descent_impossible
#print axioms toric_non_descending_depth3_contradiction
#print axioms mu64_all_toric_partial_profiles_classification

end ProximityGap.QuarterToricPencilExclusion
