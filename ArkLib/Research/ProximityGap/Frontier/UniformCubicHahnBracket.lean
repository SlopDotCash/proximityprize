/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CubicHahnJohnson
import ArkLib.Research.ProximityGap.SmoothListRankBracket

/-!
# Central-Moment Cubic Hahn Strip, Uniform Four-Rate Bounds, and Smooth Bracket Upgrades

We derive three exact central-moment sum-of-squares identities for the degree-3 Hahn
coefficients (`cubicC2_central`, `cubicC1_central`, `cubicC0_central`) around the
hypergeometric mean `μ = t² / n` and variance `V = t² (n - t)² / (n² (n - 1))`.

These three identities yield **simultaneously**:
1. **Universal `Θ(√n)` Super-Johnson Strip (`cubic_hahn_exact_sqrt_barrier`,
   `cubic_hahn_sqrt_strip`)**: for ANY field `F`, ANY injective domain `D : I ↪ F`
   of length `n ≥ 5`, ANY dimension `k`, ANY interleaving width, and ANY agreement
   level `t` inside the super-Johnson strip `(k - 1) - t²/n ≤ t(n - t) / (2 n ⌈√(n-1)⌉)`,
   `Lambda ≤ ⌊n * (⌈√(n - 1)⌉ + 1)³ / (n - t)⌋ = O(n^(3/2) / (1 - t/n))`.
2. **Uniform-in-`n` (`n ≥ 256`) `Johnson + 1` (`four_rate_safe_plus_one`)**:
   Slashes `MultipleOmissionJohnson`'s universal multipliers `![40, 32, 14, 14]` down to
   **`![11, 7, 6, 5]`** (`2.3×–4.6×` tighter across all four challenge rates).
3. **Uniform-in-`n` (`n ≥ 256`) `Johnson + 2` (`four_rate_safe_plus_two`)**:
   Certifies the **second full integer step** strictly beyond Johnson for all `n ≥ 256` with
   universal multipliers **`![61, 14, 10, 9]`** (`2.1×–36.6×` tighter than `![1584, 512, 58, 19]`).
4. **Official `SmoothListRankBracket` (`RankReview.listAnswer`) Lower-Endpoint Upgrades**:
   - `first_failure_plus_one_tight`: preserves `n - agreements n k + 1 ≤ e.val` under
     `2.3×–4.6×` smaller smooth fields (`![11, 7, 6, 5] * n ≤ |F| / 2¹²⁸`).
   - `first_failure_plus_two` and `first_failure_plus_two_reserved`: **strictly advance**
     the universal lower endpoint of `RankReview.listAnswer` from `n - agreements n k + 1`
     to **`n - agreements n k + 2`** for all four rates and all `n ≥ failureLength j`.
   - `production_super_johnson_listAnswer`: on any length-`2³⁰` smooth domain over a field
     with `|F| < 2²⁵⁶` and `superJohnsonBudget j ≤ |F| / 2¹²⁸` (including 255-bit smooth
     fields such as BLS12-381), pushes `RankReview.listAnswer` **`+4,799` (1/2), `+8,192`
     (1/4), `+10,592` (1/8), and `+12,288` (1/16)** full integer errors strictly beyond Johnson.
-/

set_option autoImplicit false

namespace ProximityGap.UniformCubicHahnBracket

open Finset Code InterleavedListJohnsonRank CubicHahnJohnson MultipleOmissionJohnson
open ProximityPrize SmoothPrizeCapacityTable SmoothListRankBracket
open scoped NNReal ENNReal

section CentralMomentIdentities

/-- Exact hypergeometric variance `V(n, t) = t² (n - t)² / (n² (n - 1))`. -/
def hypVar (n t : ℚ) : ℚ :=
  t ^ 2 * (n - t) ^ 2 / (n ^ 2 * (n - 1))

/-- Exact central-moment identity for `cubicC2`: manifestly nonnegative whenever `δ ≤ 2σ`. -/
theorem cubicC2_central (n t δ σ : ℚ) (hn0 : n ≠ 0) (hn4 : n - 4 ≠ 0) :
    cubicC2 n t (t ^ 2 / n + δ) (t ^ 2 / n - σ) =
      6 * (n - 2 * t) ^ 2 / (n * (n - 4)) + 2 * (2 * σ - δ) := by
  unfold cubicC2
  field_simp [hn0, hn4]
  ring

/-- Exact central-moment sum-of-squares identity for `cubicC1`: separates out the strictly
positive sum-of-squares surplus `A₀(n, t) - V(n, t) > 0` for all `n ≥ 5`. -/
theorem cubicC1_central (n t δ σ : ℚ) (hn0 : n ≠ 0) (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0)
    (hn3 : n - 3 ≠ 0) (hn4 : n - 4 ≠ 0) (hq : n ^ 2 + 10 * n - 12 ≠ 0) :
    cubicC1 n t (t ^ 2 / n + δ) (t ^ 2 / n - σ) =
      ((2 * (n ^ 2 + 10 * n - 12) * (t * (n - t)) - 6 * n ^ 2 * (n - 1)) ^ 2 +
        2 * n ^ 3 * (n - 1) * (n - 2) ^ 2 * (n - 3)) /
          (2 * n ^ 2 * (n - 1) * (n - 2) * (n - 3) * (n ^ 2 + 10 * n - 12)) +
      hypVar n t +
      (2 * σ - δ) * (n - 2 * t) ^ 2 / (n * (n - 2)) +
      σ * (σ - 2 * δ) := by
  set q : ℚ := n ^ 2 + 10 * n - 12
  unfold cubicC1 cubicC2 hypVar
  field_simp [hn0, hn1, hn2, hn3, hn4, hq]
  dsimp [q]
  ring

/-- Exact central-moment identity for `cubicC0`: `μ₃(n, t) + (2σ - δ) V - δ σ²`, where
the third central moment `μ₃ ≥ 0` is always a square! -/
theorem cubicC0_central (n t δ σ : ℚ) (hn0 : n ≠ 0) (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0)
    (hn3 : n - 3 ≠ 0) (hn4 : n - 4 ≠ 0) :
    cubicC0 n t (t ^ 2 / n + δ) (t ^ 2 / n - σ) =
      t ^ 2 * (n - t) ^ 2 * (n - 2 * t) ^ 2 / (n ^ 3 * (n - 1) * (n - 2)) +
      (2 * σ - δ) * hypVar n t - δ * σ ^ 2 := by
  unfold cubicC0 cubicC1 cubicC2 hypVar
  field_simp [hn0, hn1, hn2, hn3, hn4]
  ring

/-- Universal `Θ(√n)` super-Johnson barrier theorem: for ANY field `F`, ANY injective domain
`D : I ↪ F` (`n ≥ 5`), ANY dimension `k`, ANY interleaving width, ANY agreement `t ≥ k - 1`,
and ANY rational scale `σ > 0` with `σ² ≤ V(n, t)` and `(k - 1) - t²/n < σ`, setting
`r₀ = t²/n - σ` gives a certified finite list bound all the way to the exact Cubic Hahn
`√V` barrier. -/
theorem cubic_hahn_exact_sqrt_barrier {I F : Type} [Fintype I] [Nonempty I] [Field F]
    (D : I ↪ F) (k t width B : ℕ) (σ : ℚ)
    (hn : 5 ≤ Fintype.card I) (hdt : k - 1 ≤ t) (htn : t ≤ Fintype.card I) (hσpos : 0 < σ)
    (hσV : σ ^ 2 ≤ hypVar (Fintype.card I) t)
    (hδ : ((k - 1 : ℕ) : ℚ) - (t : ℚ) ^ 2 / (Fintype.card I : ℚ) < σ)
    (hB : ((t : ℚ) - ((k - 1 : ℕ) : ℚ)) * ((t : ℚ) - ((t : ℚ) ^ 2 / (Fintype.card I : ℚ) - σ)) ^ 2 <
      ((B : ℚ) + 1) * (2 * (σ - (((k - 1 : ℕ) : ℚ) - (t : ℚ) ^ 2 / (Fintype.card I : ℚ))) * σ ^ 2)) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code D k : Set (I → F)))
      (((Fintype.card I - t : ℕ) : ℝ) / Fintype.card I) ≤ (B : ℕ∞) := by
  set n : ℚ := (Fintype.card I : ℚ)
  set d : ℚ := ((k - 1 : ℕ) : ℚ)
  set δ : ℚ := d - (t : ℚ) ^ 2 / n
  have hn5 : (5 : ℚ) ≤ n := by dsimp [n]; exact_mod_cast hn
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hn2 : 0 < n - 2 := by linarith
  have hn3 : 0 < n - 3 := by linarith
  have hn4 : 0 < n - 4 := by linarith
  have hq : 0 < n ^ 2 + 10 * n - 12 := by nlinarith
  have hd_eq : d = (t : ℚ) ^ 2 / n + δ := by dsimp [δ]; ring
  have h2σδ : 0 ≤ 2 * σ - δ := by linarith
  have hc2 : 0 ≤ cubicC2 n t d ((t : ℚ) ^ 2 / n - σ) := by
    rw [hd_eq, cubicC2_central n t δ σ hn0.ne' hn4.ne']
    positivity
  have hc1 : 0 ≤ cubicC1 n t d ((t : ℚ) ^ 2 / n - σ) := by
    rw [hd_eq, cubicC1_central n t δ σ hn0.ne' hn1.ne' hn2.ne' hn3.ne' hn4.ne' hq.ne']
    have hsurp : 0 ≤ ((2 * (n ^ 2 + 10 * n - 12) * ((t : ℚ) * (n - t)) - 6 * n ^ 2 * (n - 1)) ^ 2 +
        2 * n ^ 3 * (n - 1) * (n - 2) ^ 2 * (n - 3)) /
          (2 * n ^ 2 * (n - 1) * (n - 2) * (n - 3) * (n ^ 2 + 10 * n - 12)) := by positivity
    have hmid : 0 ≤ (2 * σ - δ) * (n - 2 * (t : ℚ)) ^ 2 / (n * (n - 2)) := by positivity
    have htail : 0 ≤ hypVar n t + σ * (σ - 2 * δ) := by
      have : hypVar n t + σ * (σ - 2 * δ) = (hypVar n t - σ ^ 2) + 2 * σ * (σ - δ) := by ring
      rw [this]
      have h1 : 0 ≤ hypVar n t - σ ^ 2 := by linarith
      have h2 : 0 ≤ 2 * σ * (σ - δ) := mul_nonneg (by linarith) (by linarith)
      linarith
    linarith
  have hc0_ge : 2 * (σ - δ) * σ ^ 2 ≤ cubicC0 n t d ((t : ℚ) ^ 2 / n - σ) := by
    rw [hd_eq, cubicC0_central n t δ σ hn0.ne' hn1.ne' hn2.ne' hn3.ne' hn4.ne']
    have hmu3 : 0 ≤ (t : ℚ) ^ 2 * (n - t) ^ 2 * (n - 2 * t) ^ 2 /
        (n ^ 3 * (n - 1) * (n - 2)) := by positivity
    have hmulV : (2 * σ - δ) * σ ^ 2 ≤ (2 * σ - δ) * hypVar n t :=
      mul_le_mul_of_nonneg_left hσV h2σδ
    linarith
  have hsd : 0 < σ - δ := by linarith
  have hc0 : 0 < cubicC0 n t d ((t : ℚ) ^ 2 / n - σ) :=
    lt_of_lt_of_le (by positivity) hc0_ge
  have hδ_real : (((Fintype.card I - t : ℕ) : ℝ) / Fintype.card I) * (Fintype.card I : ℝ) <
      (Fintype.card I : ℝ) - t + 1 := by
    have hnR : (0 : ℝ) < Fintype.card I := by exact_mod_cast (show 0 < Fintype.card I by omega)
    rw [div_mul_cancel₀ _ hnR.ne', Nat.cast_sub htn]
    linarith
  have hgap : ((t : ℚ) - d) * ((t : ℚ) - ((t : ℚ) ^ 2 / n - σ)) ^ 2 <
      ((B + 1 : ℕ) : ℚ) * cubicC0 n t d ((t : ℚ) ^ 2 / n - σ) := by
    have hB1 : 0 ≤ (B : ℚ) + 1 := by positivity
    push_cast
    exact lt_of_lt_of_le hB (mul_le_mul_of_nonneg_left hc0_ge hB1)
  exact list_le_of_cubic_hahn D k t width B _ ((t : ℚ) ^ 2 / n - σ) hn hdt hδ_real hc0 hc1 hc2 hgap

/-- Parameter-free general `O(n^(3/2) / (1 - t/n))` super-Johnson list-decoding theorem!
Over ANY field `F`, ANY injective domain `D : I ↪ F` (`n ≥ 5`), ANY dimension `k`,
ANY interleaving width, and ANY agreement `0 < t < n` (`k - 1 ≤ t`) inside half the
exact Cubic Hahn `Θ(√n)` strip (`(k - 1) - t²/n ≤ t(n - t) / (2 n m)`, `m = ⌈√(n - 1)⌉`),
the list size is unconditionally at most `⌊n * (m + 1)³ / (n - t)⌋`. -/
theorem cubic_hahn_sqrt_strip {I F : Type} [Fintype I] [Nonempty I] [Field F]
    (D : I ↪ F) (k t width : ℕ)
    (hn : 5 ≤ Fintype.card I) (hdt : k - 1 ≤ t) (htpos : 0 < t) (htlt : t < Fintype.card I)
    (hstrip : ((k - 1 : ℕ) : ℚ) - (t : ℚ) ^ 2 / (Fintype.card I : ℚ) ≤
      (t : ℚ) * ((Fintype.card I : ℚ) - t) /
        (2 * (Fintype.card I : ℚ) * ((Nat.sqrt (Fintype.card I - 2) + 1 : ℕ) : ℚ))) :
    let n := Fintype.card I
    let m := Nat.sqrt (n - 2) + 1
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code D k : Set (I → F)))
      (((n - t : ℕ) : ℝ) / n) ≤ ((n * (m + 1) ^ 3 / (n - t) : ℕ) : ℕ∞) := by
  dsimp only
  set nNat := Fintype.card I
  set mNat := Nat.sqrt (nNat - 2) + 1
  set n : ℚ := (nNat : ℚ)
  set m : ℚ := (mNat : ℚ)
  set d : ℚ := ((k - 1 : ℕ) : ℚ)
  set δ : ℚ := d - (t : ℚ) ^ 2 / n
  set T : ℚ := (t : ℚ) * (n - t) / n
  set σ : ℚ := T / m
  have hn5 : (5 : ℚ) ≤ n := by dsimp [n]; exact_mod_cast hn
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hn2 : 0 < n - 2 := by linarith
  have hn3 : 0 < n - 3 := by linarith
  have hn4 : 0 < n - 4 := by linarith
  have hq : 0 < n ^ 2 + 10 * n - 12 := by nlinarith
  have htposQ : (0 : ℚ) < t := by exact_mod_cast htpos
  have htltQ : (t : ℚ) < n := by dsimp [n]; exact_mod_cast htlt
  have hntpos : (0 : ℚ) < n - t := by linarith
  have hmpos : (0 : ℚ) < m := by dsimp [m, mNat]; positivity
  have hm_sq : n - 1 ≤ m ^ 2 := by
    have hnat : nNat - 1 ≤ mNat ^ 2 := by
      have hsq := Nat.lt_succ_sqrt (nNat - 2)
      rw [Nat.succ_eq_add_one] at hsq
      dsimp [mNat]
      rw [sq]
      omega
    have hq' : ((nNat - 1 : ℕ) : ℚ) ≤ (mNat : ℚ) ^ 2 := by exact_mod_cast hnat
    rwa [Nat.cast_sub (by omega)] at hq'
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hσpos : 0 < σ := div_pos hTpos hmpos
  have hσV : σ ^ 2 ≤ hypVar n t := by
    dsimp [σ, T, hypVar]
    have hden1 : 0 < n ^ 2 * (n - 1) := by positivity
    have hden2 : 0 < n ^ 2 * m ^ 2 := by positivity
    rw [div_pow, div_pow, div_div, div_le_div_iff₀ hden2 hden1]
    have hsq_eq : ((t : ℚ) * (n - t)) ^ 2 = (t : ℚ) ^ 2 * (n - t) ^ 2 := by ring
    rw [hsq_eq]
    have hle : n ^ 2 * (n - 1) ≤ n ^ 2 * m ^ 2 :=
      mul_le_mul_of_nonneg_left hm_sq (sq_nonneg n)
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  have hδ_half : δ ≤ σ / 2 := by
    have hσ_eq : σ / 2 = (t : ℚ) * (n - t) / (2 * n * m) := by dsimp [σ, T]; ring
    rw [hσ_eq]; exact hstrip
  have hδ_lt : δ < σ := by linarith
  have hσ_sub : σ / 2 ≤ σ - δ := by linarith
  have h2σ3 : σ ^ 3 ≤ 2 * (σ - δ) * σ ^ 2 := by nlinarith [sq_nonneg σ]
  have hnum_le : ((t : ℚ) - d) * ((t : ℚ) - ((t : ℚ) ^ 2 / n - σ)) ^ 2 ≤
      (n * (m + 1) ^ 3 / (n - t)) * σ ^ 3 := by
    have ht_r0 : (t : ℚ) - ((t : ℚ) ^ 2 / n - σ) = (m + 1) * σ := by
      dsimp [σ, T]; field_simp [hmpos.ne', hn0.ne']; ring
    have hd_nn : (0 : ℚ) ≤ d := by dsimp [d]; positivity
    have htd : (t : ℚ) - d ≤ t := by linarith
    have hm_le : m ≤ m + 1 := by linarith
    have htm : (t : ℚ) * ((m + 1) * σ) ^ 2 = (n * m * (m + 1) ^ 2 / (n - t)) * σ ^ 3 := by
      dsimp [σ, T]; field_simp [hmpos.ne', hntpos.ne', hn0.ne']
    calc
      ((t : ℚ) - d) * ((t : ℚ) - ((t : ℚ) ^ 2 / n - σ)) ^ 2
        = ((t : ℚ) - d) * ((m + 1) * σ) ^ 2 := by rw [ht_r0]
      _ ≤ (t : ℚ) * ((m + 1) * σ) ^ 2 := mul_le_mul_of_nonneg_right htd (sq_nonneg _)
      _ = (n * m * (m + 1) ^ 2 / (n - t)) * σ ^ 3 := htm
      _ ≤ (n * (m + 1) ^ 3 / (n - t)) * σ ^ 3 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply div_le_div_of_nonneg_right _ hntpos.le
          have : n * m * (m + 1) ^ 2 ≤ n * (m + 1) * (m + 1) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_le (by linarith)) (sq_nonneg _)
          linarith
  have hfloor : n * (m + 1) ^ 3 / (n - t) < ((nNat * (mNat + 1) ^ 3 / (nNat - t) : ℕ) : ℚ) + 1 := by
    have hpos_sub : 0 < nNat - t := by omega
    have hdiv_lt : nNat * (mNat + 1) ^ 3 < (nNat * (mNat + 1) ^ 3 / (nNat - t) + 1) * (nNat - t) := by
      have hmod := Nat.div_add_mod (nNat * (mNat + 1) ^ 3) (nNat - t)
      have hmlt := Nat.mod_lt (nNat * (mNat + 1) ^ 3) hpos_sub
      nlinarith
    have hq'' : ((nNat * (mNat + 1) ^ 3 : ℕ) : ℚ) <
        (((nNat * (mNat + 1) ^ 3 / (nNat - t) : ℕ) : ℚ) + 1) * ((nNat - t : ℕ) : ℚ) := by
      exact_mod_cast hdiv_lt
    rw [Nat.cast_sub htlt.le] at hq''
    rw [div_lt_iff₀ hntpos]
    push_cast at hq''
    simpa [n, m] using hq''
  have hd_eq : d = (t : ℚ) ^ 2 / n + δ := by dsimp [δ]; ring
  have h2σδ : 0 ≤ 2 * σ - δ := by linarith
  have hc2 : 0 ≤ cubicC2 n t d ((t : ℚ) ^ 2 / n - σ) := by
    rw [hd_eq, cubicC2_central n t δ σ hn0.ne' hn4.ne']; positivity
  have hc1 : 0 ≤ cubicC1 n t d ((t : ℚ) ^ 2 / n - σ) := by
    rw [hd_eq, cubicC1_central n t δ σ hn0.ne' hn1.ne' hn2.ne' hn3.ne' hn4.ne' hq.ne']
    have hsurp : 0 ≤ ((2 * (n ^ 2 + 10 * n - 12) * ((t : ℚ) * (n - t)) - 6 * n ^ 2 * (n - 1)) ^ 2 +
        2 * n ^ 3 * (n - 1) * (n - 2) ^ 2 * (n - 3)) /
          (2 * n ^ 2 * (n - 1) * (n - 2) * (n - 3) * (n ^ 2 + 10 * n - 12)) := by positivity
    have hmid : 0 ≤ (2 * σ - δ) * (n - 2 * (t : ℚ)) ^ 2 / (n * (n - 2)) := by positivity
    have htail : 0 ≤ hypVar n t + σ * (σ - 2 * δ) := by
      have : hypVar n t + σ * (σ - 2 * δ) = (hypVar n t - σ ^ 2) + 2 * σ * (σ - δ) := by ring
      rw [this]
      have h1 : 0 ≤ hypVar n t - σ ^ 2 := by linarith
      have h2 : 0 ≤ 2 * σ * (σ - δ) := mul_nonneg (by linarith) (by linarith)
      linarith
    linarith
  have hc0_ge : σ ^ 3 ≤ cubicC0 n t d ((t : ℚ) ^ 2 / n - σ) := by
    rw [hd_eq, cubicC0_central n t δ σ hn0.ne' hn1.ne' hn2.ne' hn3.ne' hn4.ne']
    have hmu3 : 0 ≤ (t : ℚ) ^ 2 * (n - t) ^ 2 * (n - 2 * t) ^ 2 /
        (n ^ 3 * (n - 1) * (n - 2)) := by positivity
    have hmulV : (2 * σ - δ) * σ ^ 2 ≤ (2 * σ - δ) * hypVar n t :=
      mul_le_mul_of_nonneg_left hσV h2σδ
    linarith
  have hc0 : 0 < cubicC0 n t d ((t : ℚ) ^ 2 / n - σ) := lt_of_lt_of_le (by positivity) hc0_ge
  have hδ_real : (((nNat - t : ℕ) : ℝ) / nNat) * (nNat : ℝ) < (nNat : ℝ) - t + 1 := by
    have hnR : (0 : ℝ) < nNat := by exact_mod_cast (show 0 < nNat by omega)
    rw [div_mul_cancel₀ _ hnR.ne', Nat.cast_sub htlt.le]
    linarith
  have hgap : ((t : ℚ) - d) * ((t : ℚ) - ((t : ℚ) ^ 2 / n - σ)) ^ 2 <
      ((nNat * (mNat + 1) ^ 3 / (nNat - t) + 1 : ℕ) : ℚ) *
        cubicC0 n t d ((t : ℚ) ^ 2 / n - σ) := by
    push_cast
    calc
      ((t : ℚ) - d) * ((t : ℚ) - ((t : ℚ) ^ 2 / n - σ)) ^ 2
        ≤ (n * (m + 1) ^ 3 / (n - t)) * σ ^ 3 := hnum_le
      _ < (((nNat * (mNat + 1) ^ 3 / (nNat - t) : ℕ) : ℚ) + 1) * σ ^ 3 :=
          mul_lt_mul_of_pos_right hfloor (by positivity)
      _ ≤ (((nNat * (mNat + 1) ^ 3 / (nNat - t) : ℕ) : ℚ) + 1) *
            cubicC0 n t d ((t : ℚ) ^ 2 / n - σ) :=
          mul_le_mul_of_nonneg_left hc0_ge (by positivity)
  exact list_le_of_cubic_hahn D k t width (nNat * (mNat + 1) ^ 3 / (nNat - t)) _
    ((t : ℚ) ^ 2 / n - σ) hn hdt hδ_real hc0 hc1 hc2 hgap

/-- Central-moment ratio-cap wrapper: proves `cubicC2 ≥ 0`, `cubicC1 ≥ 0`, `cubicC0 > 0`,
and `(t - d) * (t - r₀)² < (M * n + 1) * cubicC0` in 20 lines of linear algebra whenever
`n * (d - t²/n) ≤ u * T` (`T = t (n - t) / n`) and `n ≥ n0`. -/
private theorem cubic_hahn_of_ratio_cap {n t d n0 u c M : ℚ}
    (hn0 : 5 ≤ n0) (hn : n0 ≤ n) (htpos : 0 < t) (htlt : t < n)
    (hδ_nn : 0 ≤ d - t ^ 2 / n)
    (hu : n * (d - t ^ 2 / n) ≤ u * (t * (n - t) / n))
    (hu_nn : 0 ≤ u) (hc : 0 < c)
    (hc2_cond : u / n0 ≤ 2 * c)
    (hc1_cond : 2 * c * u / n0 ≤ 1 / n0 + c ^ 2)
    (hc0_cond : 0 < 2 * c - u * (c ^ 2 + 1 / n0))
    (hM : (1 + c) ^ 2 / (2 * c - u * (c ^ 2 + 1 / n0)) ≤ M) :
    let r0 := t ^ 2 / n - c * (t * (n - t) / n)
    0 ≤ cubicC2 n t d r0 ∧ 0 ≤ cubicC1 n t d r0 ∧ 0 < cubicC0 n t d r0 ∧
      (t - d) * (t - r0) ^ 2 < (M * n + 1) * cubicC0 n t d r0 := by
  dsimp only
  set T : ℚ := t * (n - t) / n
  set δ : ℚ := d - t ^ 2 / n
  set σ : ℚ := c * T
  have hn5 : 5 ≤ n := le_trans hn0 hn
  have hnpos : 0 < n := by linarith
  have hn0pos : 0 < n0 := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hn2 : 0 < n - 2 := by linarith
  have hn3 : 0 < n - 3 := by linarith
  have hn4 : 0 < n - 4 := by linarith
  have hq : 0 < n ^ 2 + 10 * n - 12 := by nlinarith
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hd_eq : d = t ^ 2 / n + δ := by dsimp [δ]; ring
  have hinv_le : 1 / n ≤ 1 / n0 := one_div_le_one_div_of_le hn0pos hn
  have hδ_le_n : δ ≤ u * T / n := by
    rw [le_div_iff₀ hnpos]; linarith
  have hδ_le_n0 : δ ≤ u * T / n0 := by
    have : u * T / n ≤ u * T / n0 := div_le_div_of_nonneg_left (by positivity) hn0pos hn
    exact hδ_le_n.trans this
  have h2σδ : 0 ≤ 2 * σ - δ := by
    have : u * T / n0 ≤ 2 * c * T := by
      calc u * T / n0 = (u / n0) * T := by ring
        _ ≤ (2 * c) * T := mul_le_mul_of_nonneg_right hc2_cond hTpos.le
        _ = 2 * c * T := by ring
    dsimp [σ]; linarith
  have hV_ge : T ^ 2 / n ≤ hypVar n t := by
    dsimp [T, hypVar]
    have hsq : (t * (n - t) / n) ^ 2 / n = t ^ 2 * (n - t) ^ 2 / (n ^ 2 * n) := by
      field_simp [hnpos.ne']
    rw [hsq]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have hc2 : 0 ≤ cubicC2 n t d (t ^ 2 / n - σ) := by
    rw [hd_eq, cubicC2_central n t δ σ hnpos.ne' hn4.ne']
    positivity
  have hc1 : 0 ≤ cubicC1 n t d (t ^ 2 / n - σ) := by
    rw [hd_eq, cubicC1_central n t δ σ hnpos.ne' hn1.ne' hn2.ne' hn3.ne' hn4.ne' hq.ne']
    have hsurp : 0 ≤ ((2 * (n ^ 2 + 10 * n - 12) * (t * (n - t)) - 6 * n ^ 2 * (n - 1)) ^ 2 +
        2 * n ^ 3 * (n - 1) * (n - 2) ^ 2 * (n - 3)) /
          (2 * n ^ 2 * (n - 1) * (n - 2) * (n - 3) * (n ^ 2 + 10 * n - 12)) := by positivity
    have hmid : 0 ≤ (2 * σ - δ) * (n - 2 * t) ^ 2 / (n * (n - 2)) := by positivity
    have htail : 0 ≤ hypVar n t + σ * (σ - 2 * δ) := by
      have h1 : T ^ 2 * (c ^ 2 + (1 - 2 * c * u) / n) ≤ hypVar n t + σ * (σ - 2 * δ) := by
        have hδ_mul : 2 * c * T * δ ≤ 2 * c * u * T ^ 2 / n := by
          calc 2 * c * T * δ ≤ 2 * c * T * (u * T / n) :=
                mul_le_mul_of_nonneg_left hδ_le_n (by positivity)
            _ = 2 * c * u * T ^ 2 / n := by ring
        dsimp [σ]
        have hrew : T ^ 2 * (c ^ 2 + (1 - 2 * c * u) / n) =
            T ^ 2 / n + c * T * (c * T) - 2 * c * u * T ^ 2 / n := by ring
        linarith
      have h2 : 0 ≤ c ^ 2 + (1 - 2 * c * u) / n := by
        by_cases hcu : 2 * c * u ≤ 1
        · have : 0 ≤ (1 - 2 * c * u) / n := div_nonneg (by linarith) hnpos.le
          positivity
        · push Not at hcu
          have : (2 * c * u - 1) / n ≤ (2 * c * u - 1) / n0 :=
            div_le_div_of_nonneg_left (by linarith) hn0pos hn
          have hrew : 1 / n0 + c ^ 2 - 2 * c * u / n0 = c ^ 2 - (2 * c * u - 1) / n0 := by ring
          have hrew2 : c ^ 2 + (1 - 2 * c * u) / n = c ^ 2 - (2 * c * u - 1) / n := by ring
          linarith
      exact le_trans (mul_nonneg (sq_nonneg T) h2) h1
    linarith
  have hc0_lb : T ^ 3 / n * (2 * c - u * (c ^ 2 + 1 / n0)) ≤ cubicC0 n t d (t ^ 2 / n - σ) := by
    rw [hd_eq, cubicC0_central n t δ σ hnpos.ne' hn1.ne' hn2.ne' hn3.ne' hn4.ne']
    have hmu3 : 0 ≤ t ^ 2 * (n - t) ^ 2 * (n - 2 * t) ^ 2 /
        (n ^ 3 * (n - 1) * (n - 2)) := by positivity
    have h1 : (2 * σ - δ) * (T ^ 2 / n) ≤ (2 * σ - δ) * hypVar n t :=
      mul_le_mul_of_nonneg_left hV_ge h2σδ
    have h2 : δ * (c ^ 2 + 1 / n) ≤ u * T / n * (c ^ 2 + 1 / n0) := by
      have ha : δ * (c ^ 2 + 1 / n) ≤ (u * T / n) * (c ^ 2 + 1 / n) :=
        mul_le_mul_of_nonneg_right hδ_le_n (by positivity)
      have hb : (u * T / n) * (c ^ 2 + 1 / n) ≤ (u * T / n) * (c ^ 2 + 1 / n0) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      exact ha.trans hb
    have h3 : T ^ 2 * (δ * (c ^ 2 + 1 / n)) ≤ T ^ 2 * (u * T / n * (c ^ 2 + 1 / n0)) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg T)
    have hrew1 : (2 * σ - δ) * (T ^ 2 / n) - δ * σ ^ 2 =
        2 * c * T ^ 3 / n - T ^ 2 * (δ * (c ^ 2 + 1 / n)) := by dsimp [σ]; ring
    have hrew2 : T ^ 3 / n * (2 * c - u * (c ^ 2 + 1 / n0)) =
        2 * c * T ^ 3 / n - T ^ 2 * (u * T / n * (c ^ 2 + 1 / n0)) := by ring
    linarith
  have hc0 : 0 < cubicC0 n t d (t ^ 2 / n - σ) :=
    lt_of_lt_of_le (by positivity) hc0_lb
  have hgap : (t - d) * (t - (t ^ 2 / n - σ)) ^ 2 < (M * n + 1) * cubicC0 n t d (t ^ 2 / n - σ) := by
    have htd : t - d ≤ T := by
      have : t - d = T - δ := by dsimp [T, δ]; field_simp [hnpos.ne']; ring
      linarith
    have htr0 : t - (t ^ 2 / n - σ) = (1 + c) * T := by
      dsimp [σ, T]; field_simp [hnpos.ne']; ring
    have hM' : (1 + c) ^ 2 ≤ M * (2 * c - u * (c ^ 2 + 1 / n0)) :=
      (div_le_iff₀ hc0_cond).mp hM
    have hMn : (1 + c) ^ 2 * T ^ 3 ≤ M * n * cubicC0 n t d (t ^ 2 / n - σ) := by
      calc
        (1 + c) ^ 2 * T ^ 3
          ≤ (M * (2 * c - u * (c ^ 2 + 1 / n0))) * T ^ 3 :=
            mul_le_mul_of_nonneg_right hM' (by positivity)
        _ = M * n * (T ^ 3 / n * (2 * c - u * (c ^ 2 + 1 / n0))) := by
            field_simp [hnpos.ne']
        _ ≤ M * n * cubicC0 n t d (t ^ 2 / n - σ) :=
            mul_le_mul_of_nonneg_left hc0_lb (by
              have hMnn : 0 ≤ M := le_trans (by positivity) hM
              positivity)
    calc
      (t - d) * (t - (t ^ 2 / n - σ)) ^ 2
        = (t - d) * ((1 + c) * T) ^ 2 := by rw [htr0]
      _ ≤ T * ((1 + c) * T) ^ 2 := mul_le_mul_of_nonneg_right htd (sq_nonneg _)
      _ = (1 + c) ^ 2 * T ^ 3 := by ring
      _ ≤ M * n * cubicC0 n t d (t ^ 2 / n - σ) := hMn
      _ < (M * n + 1) * cubicC0 n t d (t ^ 2 / n - σ) := by linarith
  exact ⟨hc2, hc1, hc0, hgap⟩

end CentralMomentIdentities

section UniformFourRate

/-- Improved uniform multiples of `n` at `Johnson + 1` (`2.3×–4.6×` tighter than `![40, 32, 14, 14]`). -/
def multiplePlusOne : Fin 4 → ℕ := ![11, 7, 6, 5]

/-- Uniform multiples of `n` at the second full integer step beyond Johnson (`Johnson + 2`),
slashing omissions `![1584, 512, 58, 19]` by `2.1×–36.6×`. -/
def multiplePlusTwo : Fin 4 → ℕ := ![61, 14, 10, 9]

private theorem grid_sq_local {n k : ℕ} (hp : 0 < n * (k - 1)) :
    (agreements n k) ^ 2 < n * (k - 1) ∧ n * (k - 1) ≤ (agreements n k + 1) ^ 2 := by
  have h1 := Nat.sqrt_le' (n * (k - 1) - 1)
  have h2 := Nat.succ_le_succ_sqrt' (n * (k - 1) - 1)
  unfold agreements
  omega

private theorem ratio_cap_from_bracket {n t d K ahi tmin : ℚ}
    (hn : 0 < n) (htmin : tmin ≤ t) (htmin_pos : 0 < tmin)
    (hahi : t ≤ ahi * n) (hahi_lt : ahi < 1)
    (hhi : n * d ≤ (t + K) ^ 2) (hK : 0 ≤ K) :
    n * (d - t ^ 2 / n) ≤ ((2 * K + K ^ 2 / tmin) / (1 - ahi)) * (t * (n - t) / n) := by
  have htpos : 0 < t := lt_of_lt_of_le htmin_pos htmin
  have h1 : n * (d - t ^ 2 / n) ≤ 2 * K * t + K ^ 2 := by
    have : n * (d - t ^ 2 / n) = n * d - t ^ 2 := by field_simp [hn.ne']
    linarith
  have h2 : 2 * K * t + K ^ 2 ≤ (2 * K + K ^ 2 / tmin) * t := by
    have : K ^ 2 ≤ (K ^ 2 / tmin) * t := by
      rw [div_mul_eq_mul_div, le_div_iff₀ htmin_pos]
      exact mul_le_mul_of_nonneg_left htmin (sq_nonneg K)
    linarith
  have h3 : (1 - ahi) * n ≤ n - t := by linarith
  have h4 : t ≤ (t * (n - t) / n) / (1 - ahi) := by
    rw [le_div_iff₀ (by linarith : 0 < 1 - ahi), le_div_iff₀ hn]
    nlinarith
  have h5 : (2 * K + K ^ 2 / tmin) * t ≤
      ((2 * K + K ^ 2 / tmin) / (1 - ahi)) * (t * (n - t) / n) := by
    have hmul := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 2 * K + K ^ 2 / tmin)
    have hrew : (2 * K + K ^ 2 / tmin) * (t * (n - t) / n / (1 - ahi)) =
        ((2 * K + K ^ 2 / tmin) / (1 - ahi)) * (t * (n - t) / n) := by ring
    linarith
  exact h1.trans (h2.trans h5)

/-- Uniform-in-`n` (`n ≥ 256`) `Johnson + 1` bound over arbitrary fields, injective domains,
and interleaving widths, slashing `MultipleOmissionJohnson`'s `![40, 32, 14, 14]` to
`![11, 7, 6, 5]`. -/
theorem four_rate_safe_plus_one {I F : Type} [Fintype I] [Nonempty I] [Field F]
    (D : I ↪ F) (j : Fin 4) (k width : ℕ)
    (hn : Fintype.card I = divisor j * k) (hlarge : 256 ≤ Fintype.card I) :
    let n := Fintype.card I
    let t := agreements n k
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code D k : Set (I → F)))
      (((n - t : ℕ) : ℝ) / n) ≤ ((multiplePlusOne j * n : ℕ) : ℕ∞) := by
  classical
  dsimp only
  set n := Fintype.card I
  set t := agreements n k
  have hk : 16 ≤ k := by fin_cases j <;> norm_num [divisor] at hn <;> omega
  have hp : 0 < n * (k - 1) := Nat.mul_pos (by omega) (by omega)
  obtain ⟨hlo, hhi⟩ := grid_sq_local hp
  change t ^ 2 < n * (k - 1) at hlo
  change n * (k - 1) ≤ (t + 1) ^ 2 at hhi
  have ht_lt_n : t < n := by
    by_contra! h
    have h1 : n * (k - 1) < n * n :=
      Nat.mul_lt_mul_of_pos_left (by fin_cases j <;> norm_num [divisor] at hn <;> omega) (by omega)
    have h2 : n * n ≤ t * t := Nat.mul_le_mul h h
    nlinarith
  have hdt : k - 1 ≤ t := by
    by_contra! h
    have h1 : (t + 1) ^ 2 ≤ (k - 1) ^ 2 := Nat.pow_le_pow_left h 2
    have h2 : (k - 1) ^ 2 < n * (k - 1) := by
      have : k - 1 < n := by fin_cases j <;> norm_num [divisor] at hn <;> omega
      nlinarith
    omega
  have hδ : (((n - t : ℕ) : ℝ) / n) * (n : ℝ) < (n : ℝ) - t + 1 := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [div_mul_cancel₀ _ hnR.ne', Nat.cast_sub ht_lt_n.le]
    linarith
  have hnQ : (256 : ℚ) ≤ n := by exact_mod_cast hlarge
  have hloQ : (t : ℚ) ^ 2 < (n : ℚ) * ((k - 1 : ℕ) : ℚ) := by exact_mod_cast hlo
  have hhiQ : (n : ℚ) * ((k - 1 : ℕ) : ℚ) ≤ ((t : ℚ) + 1) ^ 2 := by exact_mod_cast hhi
  have hδ_nn : 0 ≤ ((k - 1 : ℕ) : ℚ) - (t : ℚ) ^ 2 / n := by
    have : (t : ℚ) ^ 2 / n ≤ ((k - 1 : ℕ) : ℚ) := by
      rw [div_le_iff₀ (by linarith : (0 : ℚ) < n)]; linarith
    linarith
  have htltQ : (t : ℚ) < n := by exact_mod_cast ht_lt_n
  fin_cases j
  · -- Rate 1/2 (`M = 11`, `c = 3/23`, `ahi = 442/625`, `tmin = 180`)
    have hnk : n = 2 * k := by simpa [divisor] using hn
    have ht180 : 180 ≤ t := by
      by_contra! h
      have hsq : (t + 1) ^ 2 ≤ 180 ^ 2 := Nat.pow_le_pow_left h 2
      have hprod : 256 * 127 ≤ n * (k - 1) := Nat.mul_le_mul hlarge (by omega)
      omega
    have hahi : (t : ℚ) ≤ 442 / 625 * n := by
      by_contra! h
      have hsq : (442 / 625 * (n : ℚ)) ^ 2 < (t : ℚ) ^ 2 := by nlinarith
      have hnkQ : (n : ℚ) = 2 * k := by exact_mod_cast hnk
      have hk1 : ((k - 1 : ℕ) : ℚ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      nlinarith
    have hu := ratio_cap_from_bracket (by linarith) (by exact_mod_cast ht180 : (180 : ℚ) ≤ t)
      (by norm_num) hahi (by norm_num) hhiQ (by norm_num)
    obtain ⟨hc2, hc1, hc0, hgap⟩ := cubic_hahn_of_ratio_cap (n0 := 256)
      (u := (2 * 1 + 1 ^ 2 / 180) / (1 - 442 / 625)) (c := 3 / 23) (M := 11)
      (by norm_num) hnQ (by exact_mod_cast (show 0 < t by omega)) htltQ hδ_nn hu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact list_le_of_cubic_hahn D k t width (11 * n) _ _ (by omega) hdt hδ hc0 hc1 hc2
      (by push_cast; exact hgap)
  · -- Rate 1/4 (`M = 7`, `c = 1/5`, `ahi = 1/2`, `tmin = 126`)
    have hnk : n = 4 * k := by simpa [divisor] using hn
    have ht126 : 126 ≤ t := by
      by_contra! h
      have hsq : (t + 1) ^ 2 ≤ 126 ^ 2 := Nat.pow_le_pow_left h 2
      have hprod : 256 * 63 ≤ n * (k - 1) := Nat.mul_le_mul hlarge (by omega)
      omega
    have hahi : (t : ℚ) ≤ 1 / 2 * n := by
      by_contra! h
      have hsq : (1 / 2 * (n : ℚ)) ^ 2 < (t : ℚ) ^ 2 := by nlinarith
      have hnkQ : (n : ℚ) = 4 * k := by exact_mod_cast hnk
      have hk1 : ((k - 1 : ℕ) : ℚ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      nlinarith
    have hu := ratio_cap_from_bracket (by linarith) (by exact_mod_cast ht126 : (126 : ℚ) ≤ t)
      (by norm_num) hahi (by norm_num) hhiQ (by norm_num)
    obtain ⟨hc2, hc1, hc0, hgap⟩ := cubic_hahn_of_ratio_cap (n0 := 256)
      (u := (2 * 1 + 1 ^ 2 / 126) / (1 - 1 / 2)) (c := 1 / 5) (M := 7)
      (by norm_num) hnQ (by exact_mod_cast (show 0 < t by omega)) htltQ hδ_nn hu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact list_le_of_cubic_hahn D k t width (7 * n) _ _ (by omega) hdt hδ hc0 hc1 hc2
      (by push_cast; exact hgap)
  · -- Rate 1/8 (`M = 6`, `c = 1/4`, `ahi = 221/625`, `tmin = 89`)
    have hnk : n = 8 * k := by simpa [divisor] using hn
    have ht89 : 89 ≤ t := by
      by_contra! h
      have hsq : (t + 1) ^ 2 ≤ 89 ^ 2 := Nat.pow_le_pow_left h 2
      have hprod : 256 * 31 ≤ n * (k - 1) := Nat.mul_le_mul hlarge (by omega)
      omega
    have hahi : (t : ℚ) ≤ 221 / 625 * n := by
      by_contra! h
      have hsq : (221 / 625 * (n : ℚ)) ^ 2 < (t : ℚ) ^ 2 := by nlinarith
      have hnkQ : (n : ℚ) = 8 * k := by exact_mod_cast hnk
      have hk1 : ((k - 1 : ℕ) : ℚ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      nlinarith
    have hu := ratio_cap_from_bracket (by linarith) (by exact_mod_cast ht89 : (89 : ℚ) ≤ t)
      (by norm_num) hahi (by norm_num) hhiQ (by norm_num)
    obtain ⟨hc2, hc1, hc0, hgap⟩ := cubic_hahn_of_ratio_cap (n0 := 256)
      (u := (2 * 1 + 1 ^ 2 / 89) / (1 - 221 / 625)) (c := 1 / 4) (M := 6)
      (by norm_num) hnQ (by exact_mod_cast (show 0 < t by omega)) htltQ hδ_nn hu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact list_le_of_cubic_hahn D k t width (6 * n) _ _ (by omega) hdt hδ hc0 hc1 hc2
      (by push_cast; exact hgap)
  · -- Rate 1/16 (`M = 5`, `c = 3/11`, `ahi = 1/4`, `tmin = 61`)
    have hnk : n = 16 * k := by simpa [divisor] using hn
    have ht61 : 61 ≤ t := by
      by_contra! h
      have hsq : (t + 1) ^ 2 ≤ 61 ^ 2 := Nat.pow_le_pow_left h 2
      have hprod : 256 * 15 ≤ n * (k - 1) := Nat.mul_le_mul hlarge (by omega)
      omega
    have hahi : (t : ℚ) ≤ 1 / 4 * n := by
      by_contra! h
      have hsq : (1 / 4 * (n : ℚ)) ^ 2 < (t : ℚ) ^ 2 := by nlinarith
      have hnkQ : (n : ℚ) = 16 * k := by exact_mod_cast hnk
      have hk1 : ((k - 1 : ℕ) : ℚ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      nlinarith
    have hu := ratio_cap_from_bracket (by linarith) (by exact_mod_cast ht61 : (61 : ℚ) ≤ t)
      (by norm_num) hahi (by norm_num) hhiQ (by norm_num)
    obtain ⟨hc2, hc1, hc0, hgap⟩ := cubic_hahn_of_ratio_cap (n0 := 256)
      (u := (2 * 1 + 1 ^ 2 / 61) / (1 - 1 / 4)) (c := 3 / 11) (M := 5)
      (by norm_num) hnQ (by exact_mod_cast (show 0 < t by omega)) htltQ hδ_nn hu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact list_le_of_cubic_hahn D k t width (5 * n) _ _ (by omega) hdt hδ hc0 hc1 hc2
      (by push_cast; exact hgap)

/-- Uniform-in-`n` (`n ≥ 256`) `Johnson + 2` bound over arbitrary fields, injective domains,
and interleaving widths, certifying the second full integer step strictly beyond Johnson
with universal multipliers `![61, 14, 10, 9]`. -/
theorem four_rate_safe_plus_two {I F : Type} [Fintype I] [Nonempty I] [Field F]
    (D : I ↪ F) (j : Fin 4) (k width : ℕ)
    (hn : Fintype.card I = divisor j * k) (hlarge : 256 ≤ Fintype.card I) :
    let n := Fintype.card I
    let t := agreements n k - 1
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code D k : Set (I → F)))
      (((n - t : ℕ) : ℝ) / n) ≤ ((multiplePlusTwo j * n : ℕ) : ℕ∞) := by
  classical
  dsimp only
  set n := Fintype.card I
  set t1 := agreements n k
  set t := t1 - 1
  have hk : 16 ≤ k := by fin_cases j <;> norm_num [divisor] at hn <;> omega
  have hp : 0 < n * (k - 1) := Nat.mul_pos (by omega) (by omega)
  obtain ⟨hlo1, hhi1⟩ := grid_sq_local hp
  change t1 ^ 2 < n * (k - 1) at hlo1
  change n * (k - 1) ≤ (t1 + 1) ^ 2 at hhi1
  have ht1_ge : k ≤ t1 := by
    by_contra! h
    have h1 : (t1 + 1) ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left h 2
    have h2 : k ^ 2 < n * (k - 1) := by
      have h2k : 2 * k ≤ n := by fin_cases j <;> norm_num [divisor] at hn <;> omega
      have hmul : 2 * k * (k - 1) ≤ n * (k - 1) := Nat.mul_le_mul_right (k - 1) h2k
      zify [show 1 ≤ k by omega] at hmul ⊢
      nlinarith
    omega
  have ht_succ : t + 1 = t1 := by dsimp [t]; omega
  have ht_lt_n : t < n := by
    by_contra! h
    have h1 : n * (k - 1) < n * n :=
      Nat.mul_lt_mul_of_pos_left (by fin_cases j <;> norm_num [divisor] at hn <;> omega) (by omega)
    have h2 : n * n ≤ t1 * t1 := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hdt : k - 1 ≤ t := by omega
  have hδ : (((n - t : ℕ) : ℝ) / n) * (n : ℝ) < (n : ℝ) - t + 1 := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [div_mul_cancel₀ _ hnR.ne', Nat.cast_sub ht_lt_n.le]
    linarith
  have hnQ : (256 : ℚ) ≤ n := by exact_mod_cast hlarge
  have hloQ : ((t : ℚ) + 1) ^ 2 < (n : ℚ) * ((k - 1 : ℕ) : ℚ) := by
    exact_mod_cast (show (t + 1) ^ 2 < n * (k - 1) by rw [ht_succ]; exact hlo1)
  have hhiQ : (n : ℚ) * ((k - 1 : ℕ) : ℚ) ≤ ((t : ℚ) + 2) ^ 2 := by
    exact_mod_cast (show n * (k - 1) ≤ (t + 2) ^ 2 by
      rw [show t + 2 = t1 + 1 by omega]; exact hhi1)
  have hδ_nn : 0 ≤ ((k - 1 : ℕ) : ℚ) - (t : ℚ) ^ 2 / n := by
    have : (t : ℚ) ^ 2 / n ≤ ((k - 1 : ℕ) : ℚ) := by
      rw [div_le_iff₀ (by linarith : (0 : ℚ) < n)]
      nlinarith [Nat.cast_nonneg (α := ℚ) t]
    linarith
  have htltQ : (t : ℚ) < n := by exact_mod_cast ht_lt_n
  fin_cases j
  · -- Rate 1/2 (`M = 61`, `c = 1/14`, `ahi = 442/625`, `tmin = 179`)
    have hnk : n = 2 * k := by simpa [divisor] using hn
    have ht179 : 179 ≤ t := by
      by_contra! h
      have hsq : (t1 + 1) ^ 2 ≤ 180 ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hprod : 256 * 127 ≤ n * (k - 1) := Nat.mul_le_mul hlarge (by omega)
      omega
    have hahi : (t : ℚ) ≤ 442 / 625 * n := by
      by_contra! h
      have hsq : (442 / 625 * (n : ℚ)) ^ 2 < ((t : ℚ) + 1) ^ 2 := by nlinarith
      have hnkQ : (n : ℚ) = 2 * k := by exact_mod_cast hnk
      have hk1 : ((k - 1 : ℕ) : ℚ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      nlinarith
    have hu := ratio_cap_from_bracket (by linarith) (by exact_mod_cast ht179 : (179 : ℚ) ≤ t)
      (by norm_num) hahi (by norm_num) hhiQ (by norm_num)
    obtain ⟨hc2, hc1, hc0, hgap⟩ := cubic_hahn_of_ratio_cap (n0 := 256)
      (u := (2 * 2 + 2 ^ 2 / 179) / (1 - 442 / 625)) (c := 1 / 14) (M := 61)
      (by norm_num) hnQ (by exact_mod_cast (show 0 < t by omega)) htltQ hδ_nn hu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact list_le_of_cubic_hahn D k t width (61 * n) _ _ (by omega) hdt hδ hc0 hc1 hc2
      (by push_cast; exact hgap)
  · -- Rate 1/4 (`M = 14`, `c = 3/26`, `ahi = 1/2`, `tmin = 125`)
    have hnk : n = 4 * k := by simpa [divisor] using hn
    have ht125 : 125 ≤ t := by
      by_contra! h
      have hsq : (t1 + 1) ^ 2 ≤ 126 ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hprod : 256 * 63 ≤ n * (k - 1) := Nat.mul_le_mul hlarge (by omega)
      omega
    have hahi : (t : ℚ) ≤ 1 / 2 * n := by
      by_contra! h
      have hsq : (1 / 2 * (n : ℚ)) ^ 2 < ((t : ℚ) + 1) ^ 2 := by nlinarith
      have hnkQ : (n : ℚ) = 4 * k := by exact_mod_cast hnk
      have hk1 : ((k - 1 : ℕ) : ℚ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      nlinarith
    have hu := ratio_cap_from_bracket (by linarith) (by exact_mod_cast ht125 : (125 : ℚ) ≤ t)
      (by norm_num) hahi (by norm_num) hhiQ (by norm_num)
    obtain ⟨hc2, hc1, hc0, hgap⟩ := cubic_hahn_of_ratio_cap (n0 := 256)
      (u := (2 * 2 + 2 ^ 2 / 125) / (1 - 1 / 2)) (c := 3 / 26) (M := 14)
      (by norm_num) hnQ (by exact_mod_cast (show 0 < t by omega)) htltQ hδ_nn hu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact list_le_of_cubic_hahn D k t width (14 * n) _ _ (by omega) hdt hδ hc0 hc1 hc2
      (by push_cast; exact hgap)
  · -- Rate 1/8 (`M = 10`, `c = 1/7`, `ahi = 221/625`, `tmin = 88`)
    have hnk : n = 8 * k := by simpa [divisor] using hn
    have ht88 : 88 ≤ t := by
      by_contra! h
      have hsq : (t1 + 1) ^ 2 ≤ 89 ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hprod : 256 * 31 ≤ n * (k - 1) := Nat.mul_le_mul hlarge (by omega)
      omega
    have hahi : (t : ℚ) ≤ 221 / 625 * n := by
      by_contra! h
      have hsq : (221 / 625 * (n : ℚ)) ^ 2 < ((t : ℚ) + 1) ^ 2 := by nlinarith
      have hnkQ : (n : ℚ) = 8 * k := by exact_mod_cast hnk
      have hk1 : ((k - 1 : ℕ) : ℚ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      nlinarith
    have hu := ratio_cap_from_bracket (by linarith) (by exact_mod_cast ht88 : (88 : ℚ) ≤ t)
      (by norm_num) hahi (by norm_num) hhiQ (by norm_num)
    obtain ⟨hc2, hc1, hc0, hgap⟩ := cubic_hahn_of_ratio_cap (n0 := 256)
      (u := (2 * 2 + 2 ^ 2 / 88) / (1 - 221 / 625)) (c := 1 / 7) (M := 10)
      (by norm_num) hnQ (by exact_mod_cast (show 0 < t by omega)) htltQ hδ_nn hu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact list_le_of_cubic_hahn D k t width (10 * n) _ _ (by omega) hdt hδ hc0 hc1 hc2
      (by push_cast; exact hgap)
  · -- Rate 1/16 (`M = 9`, `c = 4/25`, `ahi = 1/4`, `tmin = 60`)
    have hnk : n = 16 * k := by simpa [divisor] using hn
    have ht60 : 60 ≤ t := by
      by_contra! h
      have hsq : (t1 + 1) ^ 2 ≤ 61 ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hprod : 256 * 15 ≤ n * (k - 1) := Nat.mul_le_mul hlarge (by omega)
      omega
    have hahi : (t : ℚ) ≤ 1 / 4 * n := by
      by_contra! h
      have hsq : (1 / 4 * (n : ℚ)) ^ 2 < ((t : ℚ) + 1) ^ 2 := by nlinarith
      have hnkQ : (n : ℚ) = 16 * k := by exact_mod_cast hnk
      have hk1 : ((k - 1 : ℕ) : ℚ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      nlinarith
    have hu := ratio_cap_from_bracket (by linarith) (by exact_mod_cast ht60 : (60 : ℚ) ≤ t)
      (by norm_num) hahi (by norm_num) hhiQ (by norm_num)
    obtain ⟨hc2, hc1, hc0, hgap⟩ := cubic_hahn_of_ratio_cap (n0 := 256)
      (u := (2 * 2 + 2 ^ 2 / 60) / (1 - 1 / 4)) (c := 4 / 25) (M := 9)
      (by norm_num) hnQ (by exact_mod_cast (show 0 < t by omega)) htltQ hδ_nn hu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact list_le_of_cubic_hahn D k t width (9 * n) _ _ (by omega) hdt hδ hc0 hc1 hc2
      (by push_cast; exact hgap)

end UniformFourRate

section SmoothBracketUpgrades

private theorem smooth_divisor_mul_dim {I F : Type} [Fintype I] [Nonempty I] [Field F] [DecidableEq F]
    (D : I ↪ F) [ReedSolomon.Smooth D] (j : Fin 4) (hlarge : 256 ≤ Fintype.card I) :
    Fintype.card I = divisor j * prizeDimension (ι := I) j := by
  have de : divisor j = prizeDenominator j := by fin_cases j <;> decide
  obtain ⟨s, hs⟩ := ReedSolomon.Smooth.h_card_pow2 (domain := D)
  have hden : 2 ^ (j.val + 1) ≤ 2 ^ s := by
    rw [← hs]
    have : prizeDenominator j ≤ 256 := by fin_cases j <;> decide
    exact this.trans hlarge
  have dvd : prizeDenominator j ∣ Fintype.card I := by
    change 2 ^ (j.val + 1) ∣ Fintype.card I
    rw [hs]
    exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hden)
  rw [de]
  exact (Nat.mul_div_cancel' dvd).symm

/-- Tighter field-size hypothesis for the `Johnson + 1` smooth list rank bracket:
requires only `![11, 7, 6, 5] * n ≤ |F| / 2¹²⁸` instead of `![40, 32, 14, 14] * n`. -/
theorem first_failure_plus_one_tight {I F : Type} [Fintype I] [Nonempty I] [Field F]
    [Fintype F] [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D] (j : Fin 4) (width : ℕ)
    [NeZero width] (hn : failureLength j ≤ Fintype.card I) (hq : Fintype.card F < 2 ^ 256)
    (hbudget : multiplePlusOne j * Fintype.card I ≤ Fintype.card F / 2 ^ 128) :
    let n := Fintype.card I
    let k := prizeDimension (ι := I) j
    ∃ e : Fin (n + 1), RankReview.listAnswer D (prizeThreshold : ℝ≥0) k width = some e ∧
      n - agreements n k + 1 ≤ e.val ∧ e.val ≤ ⌊(n : ℝ≥0) * failureRadius j⌋₊ := by
  classical
  let n := Fintype.card I
  let k := prizeDimension (ι := I) j
  let a := n - agreements n k
  let z := (a : ℝ≥0) / (n : ℝ≥0)
  have hlarge : 256 ≤ n := le_trans (by fin_cases j <;> decide) hn
  have hd : n = divisor j * k := smooth_divisor_mul_dim D j hlarge
  have hnr : 0 < (n : ℝ≥0) := by exact_mod_cast Fintype.card_pos (α := I)
  have hz : z ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast Nat.sub_le n _) hnr.le
  have hu : failureRadius j ≤ 1 := by
    fin_cases j <;> norm_num [failureRadius] <;> apply div_le_one_of_le₀ <;> norm_num
  have hc := RankReview.listAnswer_correct D (prizeThreshold : ℝ≥0) k width
    (Nat.div_le_self n (prizeDenominator j))
  have lower := (hc z hz).mp (by
    apply (FourRateList128.budget_cast (Fintype.card F) _).mpr
    exact (four_rate_safe_plus_one D j k width hd hlarge).trans (by exact_mod_cast hbudget))
  have upper := mt (hc (failureRadius j) hu).mpr
    (failures D j width hn hq (δ := failureRadius j) le_rfl).2.not_ge
  cases he : RankReview.listAnswer D (prizeThreshold : ℝ≥0) k width with
  | none => rw [he] at upper; exact False.elim (upper trivial)
  | some e =>
    rw [he] at lower upper
    have low : (a : ℝ≥0) < (e.val : ℝ≥0) := (div_lt_div_iff_of_pos_right hnr).mp lower
    have high : (e.val : ℝ≥0) ≤ failureRadius j * n := (div_le_iff₀ hnr).mp (not_lt.mp upper)
    refine ⟨e, he, ?_, Nat.le_floor ?_⟩
    · exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast low : a < e.val)
    · rwa [mul_comm]

/-- Strictly advances the universal lower endpoint of `RankReview.listAnswer` from
`n - agreements n k + 1` to **`n - agreements n k + 2`** across all four challenge rates,
for all smooth lengths `n ≥ failureLength j` and all positive widths. -/
theorem first_failure_plus_two {I F : Type} [Fintype I] [Nonempty I] [Field F]
    [Fintype F] [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D] (j : Fin 4) (width : ℕ)
    [NeZero width] (hn : failureLength j ≤ Fintype.card I) (hq : Fintype.card F < 2 ^ 256)
    (hbudget : multiplePlusTwo j * Fintype.card I ≤ Fintype.card F / 2 ^ 128) :
    let n := Fintype.card I
    let k := prizeDimension (ι := I) j
    ∃ e : Fin (n + 1), RankReview.listAnswer D (prizeThreshold : ℝ≥0) k width = some e ∧
      n - agreements n k + 2 ≤ e.val ∧ e.val ≤ ⌊(n : ℝ≥0) * failureRadius j⌋₊ := by
  classical
  dsimp only
  set n := Fintype.card I
  set k := prizeDimension (ι := I) j
  set a := n - (agreements n k - 1)
  let z := (a : ℝ≥0) / (n : ℝ≥0)
  have hlarge : 256 ≤ n := le_trans (by fin_cases j <;> decide) hn
  have hd : n = divisor j * k := smooth_divisor_mul_dim D j hlarge
  have hnr : 0 < (n : ℝ≥0) := by exact_mod_cast Fintype.card_pos (α := I)
  have hz : z ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast Nat.sub_le n _) hnr.le
  have hu : failureRadius j ≤ 1 := by
    fin_cases j <;> norm_num [failureRadius] <;> apply div_le_one_of_le₀ <;> norm_num
  have hc := RankReview.listAnswer_correct D (prizeThreshold : ℝ≥0) k width
    (Nat.div_le_self n (prizeDenominator j))
  have lower := (hc z hz).mp (by
    apply (FourRateList128.budget_cast (Fintype.card F) _).mpr
    exact (four_rate_safe_plus_two D j k width hd hlarge).trans (by exact_mod_cast hbudget))
  have upper := mt (hc (failureRadius j) hu).mpr
    (failures D j width hn hq (δ := failureRadius j) le_rfl).2.not_ge
  have hk : 16 ≤ k := by fin_cases j <;> norm_num [divisor] at hd <;> omega
  have hpos_ag : 1 ≤ agreements n k := by
    have hp : 0 < n * (k - 1) := Nat.mul_pos (by omega) (by omega)
    obtain ⟨_, hhi⟩ := grid_sq_local hp
    have hprod : 256 * 15 ≤ n * (k - 1) := Nat.mul_le_mul hlarge (by omega)
    by_contra! h
    have h0 : agreements n k = 0 := by omega
    rw [h0] at hhi
    omega
  have hag_le : agreements n k ≤ n := by
    have hp : 0 < n * (k - 1) := Nat.mul_pos (by omega) (by omega)
    obtain ⟨hlo, _⟩ := grid_sq_local hp
    by_contra! h
    have h1 : n * (k - 1) < n * n :=
      Nat.mul_lt_mul_of_pos_left (by fin_cases j <;> norm_num [divisor] at hd <;> omega) (by omega)
    have h2 : n * n ≤ agreements n k * agreements n k := Nat.mul_le_mul h.le h.le
    nlinarith
  have ha_eq : a = n - agreements n k + 1 := by dsimp [a]; omega
  cases he : RankReview.listAnswer D (prizeThreshold : ℝ≥0) k width with
  | none => rw [he] at upper; exact False.elim (upper trivial)
  | some e =>
    rw [he] at lower upper
    have low : (a : ℝ≥0) < (e.val : ℝ≥0) := (div_lt_div_iff_of_pos_right hnr).mp lower
    have high : (e.val : ℝ≥0) ≤ failureRadius j * n := (div_le_iff₀ hnr).mp (not_lt.mp upper)
    refine ⟨e, rfl, ?_, Nat.le_floor ?_⟩
    · have hlt : a < e.val := by exact_mod_cast low
      rw [ha_eq] at hlt
      exact Nat.succ_le_of_lt hlt
    · rwa [mul_comm]

/-- Combined `Johnson + 2` lower endpoint and reserved-fiber upper endpoint for `RankReview.listAnswer`. -/
theorem first_failure_plus_two_reserved {I F : Type} [Fintype I] [Nonempty I] [Field F]
    [Fintype F] [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D] (j : Fin 4) (width : ℕ)
    [NeZero width] (hn : failureLength j ≤ Fintype.card I) (hq : Fintype.card F < 2 ^ 256)
    (hbudget : multiplePlusTwo j * Fintype.card I ≤ Fintype.card F / 2 ^ 128) :
    let n := Fintype.card I
    let k := prizeDimension (ι := I) j
    let h := failureLength j
    let c := SmoothReservedListBoundary.errorCoefficient j
    ∃ e : Fin (n + 1), RankReview.listAnswer D (prizeThreshold : ℝ≥0) k width = some e ∧
      n - agreements n k + 2 ≤ e.val ∧ e.val ≤ c * (n / h) + 1 := by
  obtain ⟨e, he, hlo, -⟩ := first_failure_plus_two D j width hn hq hbudget
  obtain ⟨m, f, _, len, hf, hhi⟩ := SmoothReservedListBoundary.first_failure_le D j width hn hq
  have hfe : f = e := Option.some.inj (hf.symm.trans he)
  subst f
  have hp : 0 < failureLength j := by fin_cases j <;> decide
  have hdiv : Fintype.card I / failureLength j = m := by rw [len, Nat.mul_div_cancel _ hp]
  dsimp only
  rw [hdiv]
  exact ⟨e, he, hlo, hhi⟩

/-- Production-length (`n = 2³⁰`) super-Johnson certified budgets (`< 2⁶² ≪ 2¹²⁷`). -/
def superJohnsonBudget : Fin 4 → ℕ :=
  ![142046270429484896, 2305271392757763350, 499537678460700742, 1383257789440870609]

/-- Production-length (`n = 2³⁰`) super-Johnson first-failure lower bounds
(`+4,799`, `+8,192`, `+10,592`, and `+12,288` full errors strictly past Johnson). -/
def superJohnsonMinFailure : Fin 4 → ℕ :=
  ![314496499, 536879106, 694127355, 805318659]

/-- On ANY length-`2³⁰` smooth domain (`Fintype.card I = 2³⁰`) over a `< 2²⁵⁶` field with
`superJohnsonBudget j ≤ |F| / 2¹²⁸` (satisfied by every 190-to-255-bit smooth field such as
BLS12-381), `RankReview.listAnswer` lies strictly past Johnson by `+4,799` (1/2), `+8,192`
(1/4), `+10,592` (1/8), and `+12,288` (1/16) full integer errors! -/
theorem production_super_johnson_listAnswer {I F : Type} [Fintype I] [Nonempty I]
    [Field F] [Fintype F] [DecidableEq F]
    (D : I ↪ F) [ReedSolomon.Smooth D] (hcard : Fintype.card I = 1073741824)
    (j : Fin 4) (width : ℕ) [NeZero width]
    (hq : Fintype.card F < 2 ^ 256)
    (hbudget : superJohnsonBudget j ≤ Fintype.card F / 2 ^ 128) :
    let k := prizeDimension (ι := I) j
    ∃ e : Fin (Fintype.card I + 1),
      RankReview.listAnswer D (prizeThreshold : ℝ≥0) k width = some e ∧
      superJohnsonMinFailure j ≤ e.val ∧
      e.val ≤ SmoothReservedListBoundary.errorCoefficient j * (1073741824 / failureLength j) + 1 := by
  classical
  have hn : failureLength j ≤ Fintype.card I := by
    rw [hcard]; fin_cases j <;> norm_num [failureLength]
  obtain ⟨m, e, _, len, he, hhi⟩ := SmoothReservedListBoundary.first_failure_le D j width hn hq
  have hp : 0 < failureLength j := by fin_cases j <;> norm_num [failureLength]
  have hdiv : 1073741824 / failureLength j = m := by
    rw [← hcard, len, Nat.mul_div_cancel _ hp]
  have hc := RankReview.listAnswer_correct D (prizeThreshold : ℝ≥0)
    (prizeDimension (ι := I) j) width
    (Nat.div_le_self _ (prizeDenominator j))
  have hnr : (0 : ℝ≥0) < (Fintype.card I : ℝ≥0) := by
    rw [hcard]; norm_num
  have hlow (k0 e0 t B : ℕ) (r0 : ℚ) (hk : prizeDimension (ι := I) j = k0)
      (he0 : e0 + t = 1073741824) (hdt : k0 - 1 ≤ t) (hB : B = superJohnsonBudget j)
      (hc0 : 0 < cubicC0 1073741824 t ((k0 - 1 : ℕ) : ℚ) r0)
      (hc1 : 0 ≤ cubicC1 1073741824 t ((k0 - 1 : ℕ) : ℚ) r0)
      (hc2 : 0 ≤ cubicC2 1073741824 t ((k0 - 1 : ℕ) : ℚ) r0)
      (hgap : ((t : ℚ) - ((k0 - 1 : ℕ) : ℚ)) * ((t : ℚ) - r0) ^ 2 <
        ((B + 1 : ℕ) : ℚ) * cubicC0 1073741824 t ((k0 - 1 : ℕ) : ℚ) r0) :
      e0 + 1 ≤ e.val := by
    let z : ℝ≥0 := (e0 : ℝ≥0) / (Fintype.card I : ℝ≥0)
    have hz : z ≤ 1 := div_le_one_of_le₀ (by rw [hcard]; exact_mod_cast (show e0 ≤ 1073741824 by omega)) hnr.le
    have hδ : (z : ℝ) * (Fintype.card I : ℝ) < (Fintype.card I : ℝ) - t + 1 := by
      have hnR : (0 : ℝ) < Fintype.card I := by rw [hcard]; norm_num
      have hzR : (z : ℝ) = (e0 : ℝ) / Fintype.card I := by dsimp [z]; push_cast; rfl
      rw [hzR, div_mul_cancel₀ _ hnR.ne', hcard]
      have hsumR : (e0 : ℝ) + t = (1073741824 : ℕ) := by exact_mod_cast he0
      linarith
    have hsafe : Lambda (interleavedCodeSet (κ := Fin width)
        (ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → F))) (z : ℝ) ≤ (B : ℕ∞) := by
      rw [hk]
      apply list_le_of_cubic_hahn D k0 t width B (z : ℝ) r0 (by omega) hdt hδ
      · rwa [hcard]
      · rwa [hcard]
      · rwa [hcard]
      · rwa [hcard]
    have hsafe' := (hc z hz).mp (by
      apply (FourRateList128.budget_cast (Fintype.card F) _).mpr
      exact hsafe.trans (by rw [hB]; exact_mod_cast hbudget))
    rw [he] at hsafe'
    have hlt : (e0 : ℝ≥0) < (e.val : ℝ≥0) := (div_lt_div_iff_of_pos_right hnr).mp hsafe'
    exact Nat.succ_le_of_lt (by exact_mod_cast hlt)
  refine ⟨e, he, ?_, hdiv.symm ▸ hhi⟩
  fin_cases j
  · exact hlow 536870912 314496498 759245326 142046270429484896 536857338
      (by simp [prizeDimension, prizeDenominator, hcard]) (by norm_num) (by norm_num)
      (by simp [superJohnsonBudget])
      (by norm_num [cubicC0, cubicC1, cubicC2])
      (by norm_num [cubicC1, cubicC2])
      (by norm_num [cubicC2])
      (by norm_num [cubicC0, cubicC1, cubicC2])
  · exact hlow 268435456 536879105 536862719 2305271392757763350 268419071
      (by simp [prizeDimension, prizeDenominator, hcard]) (by norm_num) (by norm_num)
      (by simp [superJohnsonBudget])
      (by norm_num [cubicC0, cubicC1, cubicC2])
      (by norm_num [cubicC1, cubicC2])
      (by norm_num [cubicC2])
      (by norm_num [cubicC0, cubicC1, cubicC2])
  · exact hlow 134217728 694127354 379614470 499537678460700742 134202749
      (by simp [prizeDimension, prizeDenominator, hcard]) (by norm_num) (by norm_num)
      (by simp [superJohnsonBudget])
      (by norm_num [cubicC0, cubicC1, cubicC2])
      (by norm_num [cubicC1, cubicC2])
      (by norm_num [cubicC2])
      (by norm_num [cubicC0, cubicC1, cubicC2])
  · exact hlow 67108864 805318658 268423166 1383257789440870609 67096575
      (by simp [prizeDimension, prizeDenominator, hcard]) (by norm_num) (by norm_num)
      (by simp [superJohnsonBudget])
      (by norm_num [cubicC0, cubicC1, cubicC2])
      (by norm_num [cubicC1, cubicC2])
      (by norm_num [cubicC2])
      (by norm_num [cubicC0, cubicC1, cubicC2])

end SmoothBracketUpgrades

end ProximityGap.UniformCubicHahnBracket

#print axioms ProximityGap.UniformCubicHahnBracket.cubicC2_central
#print axioms ProximityGap.UniformCubicHahnBracket.cubicC1_central
#print axioms ProximityGap.UniformCubicHahnBracket.cubicC0_central
#print axioms ProximityGap.UniformCubicHahnBracket.cubic_hahn_exact_sqrt_barrier
#print axioms ProximityGap.UniformCubicHahnBracket.cubic_hahn_sqrt_strip
#print axioms ProximityGap.UniformCubicHahnBracket.four_rate_safe_plus_one
#print axioms ProximityGap.UniformCubicHahnBracket.four_rate_safe_plus_two
#print axioms ProximityGap.UniformCubicHahnBracket.first_failure_plus_one_tight
#print axioms ProximityGap.UniformCubicHahnBracket.first_failure_plus_two
#print axioms ProximityGap.UniformCubicHahnBracket.first_failure_plus_two_reserved
#print axioms ProximityGap.UniformCubicHahnBracket.production_super_johnson_listAnswer
