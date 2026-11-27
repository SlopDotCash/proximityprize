/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation
import ArkLib.Research.ProximityGap.Frontier.DoubleInterpolationCommonFactor

/-! # Blown-up Gauss-graph excess intersection and half-rate safety through 313,215,000 errors

This module proves the algebraic core of the nef-safe blown-up Gauss-graph height bound,
constructs the two mixed Hasse interpolation surfaces at `e = 313,215,000` half-rate errors
on any injective domain of length `2^30`, and certifies the dual-constraint `(α, β)` Veronese
and transverse allocation below the second designated prime's 128-bit budget `2^31`.

The surface intersection argument on `Bl_{∪ C_x} Bl_Σ P(O ⊕ O ⊕ O(d))` and projective
plane-curve duality are written in `docs/research/proximity-gap/half-blowup-gauss-window.md`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.HalfBlowupGaussWindow

open Finset Polynomial HalfSuccessorJetInterpolation SecondPrimeQuarticInterpolation

abbrev n : ℕ := 1073741824
abbrev d : ℕ := 536870911
abbrev e : ℕ := 313215000
abbrev t : ℕ := n - e
abbrev miss : ℕ := 4096
abbrev core : ℕ := t - miss
abbrev bound : ℕ := 2145744452

/-! ## Algebraic core of the nef-safe blown-up Gauss-graph bound -/

/-- If a primary interpolant of order `r` on `T` (`|T| = t`) and strict weight `< r * t`
factors as `F^k * G` with `k * W + Wg < r * t` and `G` nonzero on a section agreeing on `T`,
then the site vanishing orders `i` of `F` on `T` satisfy `W + 1 ≤ ∑ x ∈ T, i x`. -/
theorem factor_order_sum_ge {α : Type*} (T : Finset α) (i j : α → ℕ)
    {k W Wg r t₀ : ℕ} (hT : T.card = t₀)
    (hwt : k * W + Wg < r * t₀)
    (hord : ∀ x ∈ T, r ≤ k * i x + j x)
    (hgj : ∑ x ∈ T, j x ≤ Wg) :
    W + 1 ≤ ∑ x ∈ T, i x := by
  have hsum : r * t₀ ≤ k * (∑ x ∈ T, i x) + ∑ x ∈ T, j x := by
    calc r * t₀ = ∑ _x ∈ T, r := by rw [Finset.sum_const, hT, smul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ T, (k * i x + j x) := Finset.sum_le_sum hord
      _ = k * (∑ x ∈ T, i x) + ∑ x ∈ T, j x := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hlt : k * W < k * ∑ x ∈ T, i x := by omega
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- Algebraic cancellation of the excess intersection correction against the discarded
volume term `-3 b^2 W + 2 d b^3` under the nef condition `∑ λ_x ≤ W`. -/
theorem volume_excess_cancel {α : Type*} (T : Finset α) (i lam : α → ℚ)
    {b W d₀ m : ℚ} (hb : 0 ≤ b) (hm : 0 ≤ m) (hbd : b * d₀ ≤ W)
    (hi : ∀ x ∈ T, i x ≤ b) (hlam0 : ∀ x ∈ T, 0 ≤ lam x)
    (hlam1 : ∀ x ∈ T, 0 < lam x → lam x + 1 ≤ i x)
    (hsum : ∑ x ∈ T, lam x ≤ W) :
    (6 * b * W * m - 3 * b ^ 2 * (d₀ * m + W) + 2 * d₀ * b ^ 3) -
      ∑ x ∈ T, ((2 * i x * lam x + lam x ^ 2) * m - i x * lam x ^ 2) ≤
    m * (6 * b * W - 3 * b ^ 2 * d₀ - 3 * ∑ x ∈ T, lam x ^ 2 - 2 * ∑ x ∈ T, lam x) := by
  have h1 : ∀ x ∈ T, 3 * lam x ^ 2 + 2 * lam x ≤ 2 * i x * lam x + lam x ^ 2 := by
    intro x hx
    rcases eq_or_lt_of_le (hlam0 x hx) with h0 | hpos
    · rw [← h0]; norm_num
    · have := hlam1 x hx hpos
      nlinarith
  have h2 : ∀ x ∈ T, i x * lam x ^ 2 ≤ b ^ 2 * lam x := by
    intro x hx
    rcases eq_or_lt_of_le (hlam0 x hx) with h0 | hpos
    · rw [← h0]; norm_num
    · have hli := hlam1 x hx hpos
      have hib := hi x hx
      have hil : i x * lam x ≤ b * b :=
        mul_le_mul hib (by linarith) hpos.le hb
      calc i x * lam x ^ 2 = (i x * lam x) * lam x := by ring
        _ ≤ (b * b) * lam x := mul_le_mul_of_nonneg_right hil hpos.le
        _ = b ^ 2 * lam x := by ring
  have hs1 : 3 * ∑ x ∈ T, lam x ^ 2 + 2 * ∑ x ∈ T, lam x ≤
      ∑ x ∈ T, (2 * i x * lam x + lam x ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum h1
  have hs2 : ∑ x ∈ T, i x * lam x ^ 2 ≤ b ^ 2 * ∑ x ∈ T, lam x := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum h2
  have hsplit : ∑ x ∈ T, ((2 * i x * lam x + lam x ^ 2) * m - i x * lam x ^ 2) =
      (∑ x ∈ T, (2 * i x * lam x + lam x ^ 2)) * m - ∑ x ∈ T, i x * lam x ^ 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hbw : b ^ 2 * ∑ x ∈ T, lam x ≤ b ^ 2 * W :=
    mul_le_mul_of_nonneg_left hsum (sq_nonneg b)
  have hvol : 0 ≤ 2 * b ^ 2 * (W - b * d₀) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg b)) (sub_nonneg.mpr hbd)
  have hms : (3 * ∑ x ∈ T, lam x ^ 2 + 2 * ∑ x ∈ T, lam x) * m ≤
      (∑ x ∈ T, (2 * i x * lam x + lam x ^ 2)) * m :=
    mul_le_mul_of_nonneg_right hs1 hm
  rw [hsplit]
  nlinarith

/-- Explicit nef-admissible rational blow-up weights on a `t₀`-site agreement set `T`,
proving both the weight cap `W + 1 ≤ b * t₀` and the Cauchy–Schwarz lower bound
`(W - t₀)^2 ≤ t₀ * ∑ λ_x^2` when `t₀ ≤ W`. -/
theorem nef_weight_cauchy_schwarz {α : Type*} (T : Finset α) (i : α → ℕ)
    {b W t₀ : ℕ} (hT : T.card = t₀) (ht : 0 < t₀)
    (hi : ∀ x ∈ T, i x ≤ b) (hord : W + 1 ≤ ∑ x ∈ T, i x) :
    W + 1 ≤ b * t₀ ∧
    (t₀ ≤ W → ∃ lam : α → ℚ,
      (∀ x ∈ T, 0 ≤ lam x) ∧
      (∀ x ∈ T, 0 < lam x → lam x + 1 ≤ (i x : ℚ)) ∧
      ∑ x ∈ T, lam x ≤ (W : ℚ) ∧
      (W : ℚ) - (t₀ : ℚ) ≤ ∑ x ∈ T, lam x ∧
      ((W : ℚ) - (t₀ : ℚ)) ^ 2 ≤ (t₀ : ℚ) * ∑ x ∈ T, lam x ^ 2) := by
  have hWbt : W + 1 ≤ b * t₀ := by
    calc W + 1 ≤ ∑ x ∈ T, i x := hord
      _ ≤ ∑ _x ∈ T, b := Finset.sum_le_sum hi
      _ = b * t₀ := by rw [Finset.sum_const, hT, smul_eq_mul, mul_comm]
  refine ⟨hWbt, fun htW => ?_⟩
  let u : α → ℚ := fun x => ((i x - 1 : ℕ) : ℚ)
  let U : ℚ := ∑ x ∈ T, u x
  have hu_ge : ∀ x ∈ T, (i x : ℚ) - 1 ≤ u x := by
    intro x _
    dsimp only [u]
    cases hx : i x with
    | zero => norm_num
    | succ k => push_cast; linarith
  have hU_ge : (W : ℚ) - (t₀ : ℚ) + 1 ≤ U := by
    have hs : ∑ x ∈ T, ((i x : ℚ) - 1) ≤ U := Finset.sum_le_sum hu_ge
    rw [Finset.sum_sub_distrib, Finset.sum_const, hT, nsmul_eq_mul, mul_one] at hs
    have hordQ : (W : ℚ) + 1 ≤ ∑ x ∈ T, (i x : ℚ) := by exact_mod_cast hord
    linarith
  have hWt_nn : (0 : ℚ) ≤ (W : ℚ) - (t₀ : ℚ) := sub_nonneg.mpr (by exact_mod_cast htW)
  have hU_pos : 0 < U := by linarith
  let lam : α → ℚ := fun x => if U ≤ (W : ℚ) then u x else ((W : ℚ) / U) * u x
  have hlam0 : ∀ x ∈ T, 0 ≤ lam x := by
    intro x _
    dsimp only [lam, u]
    split_ifs
    · positivity
    · exact mul_nonneg (div_nonneg (Nat.cast_nonneg W) hU_pos.le) (Nat.cast_nonneg _)
  have hlam1 : ∀ x ∈ T, 0 < lam x → lam x + 1 ≤ (i x : ℚ) := by
    intro x _ hpos
    have hu_pos : 0 < u x := by
      dsimp only [lam] at hpos
      split_ifs at hpos with hle
      · exact hpos
      · by_contra hle'
        push Not at hle'
        have : ((W : ℚ) / U) * u x ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (div_nonneg (Nat.cast_nonneg W) hU_pos.le) hle'
        linarith
    have hi_pos : 1 ≤ i x := by
      dsimp only [u] at hu_pos
      by_contra h0
      have : i x = 0 := by omega
      simp [this] at hu_pos
    have hu_eq : u x = (i x : ℚ) - 1 := by
      dsimp only [u]
      rw [Nat.cast_sub hi_pos, Nat.cast_one]
    have hlam_le_u : lam x ≤ u x := by
      dsimp only [lam]
      split_ifs with hle
      · exact le_rfl
      · push Not at hle
        have hdiv : (W : ℚ) / U ≤ 1 := (div_le_one hU_pos).mpr hle.le
        nlinarith
    linarith
  have hsum_le : ∑ x ∈ T, lam x ≤ (W : ℚ) := by
    dsimp only [lam]
    split_ifs with hle
    · exact hle
    · rw [← Finset.mul_sum]
      change ((W : ℚ) / U) * U ≤ (W : ℚ)
      rw [div_mul_cancel₀ _ hU_pos.ne']
  have hsum_ge : (W : ℚ) - (t₀ : ℚ) ≤ ∑ x ∈ T, lam x := by
    dsimp only [lam]
    split_ifs with hle
    · change (W : ℚ) - (t₀ : ℚ) ≤ U; linarith
    · rw [← Finset.mul_sum]
      change (W : ℚ) - (t₀ : ℚ) ≤ ((W : ℚ) / U) * U
      rw [div_mul_cancel₀ _ hU_pos.ne']
      linarith [show (0 : ℚ) ≤ (t₀ : ℚ) from Nat.cast_nonneg t₀]
  have hcs : (∑ x ∈ T, lam x) ^ 2 ≤ (t₀ : ℚ) * ∑ x ∈ T, lam x ^ 2 := by
    have hnn : 0 ≤ ∑ x ∈ T, ∑ y ∈ T, (lam x - lam y) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h1 : ∑ x ∈ T, ∑ _y ∈ T, lam x ^ 2 = (t₀ : ℚ) * ∑ x ∈ T, lam x ^ 2 := by
      simp [Finset.sum_const, hT, nsmul_eq_mul, Finset.mul_sum]
    have h2 : ∑ _x ∈ T, ∑ y ∈ T, lam y ^ 2 = (t₀ : ℚ) * ∑ y ∈ T, lam y ^ 2 := by
      simp [Finset.sum_const, hT, nsmul_eq_mul]
    have h3 : ∑ x ∈ T, ∑ y ∈ T, 2 * (lam x * lam y) = 2 * (∑ x ∈ T, lam x) ^ 2 := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    have hexp : ∑ x ∈ T, ∑ y ∈ T, (lam x - lam y) ^ 2 =
        (∑ x ∈ T, ∑ _y ∈ T, lam x ^ 2) - (∑ x ∈ T, ∑ y ∈ T, 2 * (lam x * lam y)) +
        (∑ _x ∈ T, ∑ y ∈ T, lam y ^ 2) := by
      have hterm : ∀ x y, (lam x - lam y) ^ 2 = lam x ^ 2 - 2 * (lam x * lam y) + lam y ^ 2 :=
        fun x y => by ring
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    linarith
  have hsq_ge : ((W : ℚ) - (t₀ : ℚ)) ^ 2 ≤ (∑ x ∈ T, lam x) ^ 2 := by nlinarith
  exact ⟨lam, hlam0, hlam1, hsum_le, hsum_ge, hsq_ge.trans hcs⟩

/-- Integer pole-degree budget per unit of actual companion degree after subtracting the
nef-safe blown-up excess intersection along a `t₀`-site agreement set. -/
def blowupH (b W t₀ d₀ : ℕ) : ℕ :=
  (6 * b + 2) * W - 3 * b ^ 2 * d₀ - 3 * (W - t₀) ^ 2 / t₀ - 2 * (W - t₀)

/-- The rational blown-up height bound is bounded above by the integer formula `blowupH`. -/
theorem blowupH_ge_rat {b W t₀ d₀ : ℕ} (ht : 0 < t₀) (hbd : b * d₀ ≤ W) (hW : W ≤ b * t₀) :
    ((6 * b + 2 : ℚ) * W - 3 * (b : ℚ) ^ 2 * d₀ -
      3 * ((W - t₀ : ℕ) : ℚ) ^ 2 / (t₀ : ℚ) - 2 * ((W - t₀ : ℕ) : ℚ)) ≤
    (blowupH b W t₀ d₀ : ℚ) := by
  have hdiv : ((3 * (W - t₀) ^ 2 / t₀ : ℕ) : ℚ) ≤ 3 * ((W - t₀ : ℕ) : ℚ) ^ 2 / (t₀ : ℚ) := by
    have htQ : (0 : ℚ) < (t₀ : ℚ) := by exact_mod_cast ht
    rw [le_div_iff₀ htQ]
    exact_mod_cast Nat.div_mul_le_self (3 * (W - t₀) ^ 2) t₀
  have hsub_le : 3 * b ^ 2 * d₀ + 3 * (W - t₀) ^ 2 / t₀ + 2 * (W - t₀) ≤ (6 * b + 2) * W := by
    have h1 : 3 * b ^ 2 * d₀ ≤ 3 * b * W := by nlinarith
    have h2 : 3 * (W - t₀) ^ 2 / t₀ ≤ 3 * b * W := by
      have : 3 * (W - t₀) ^ 2 ≤ 3 * b * W * t₀ := by
        have hwt : W - t₀ ≤ W := Nat.sub_le W t₀
        nlinarith
      exact Nat.div_le_of_le_mul (by linarith)
    have h3 : 2 * (W - t₀) ≤ 2 * W := by omega
    have hlin : (6 * b + 2) * W = 3 * b * W + 3 * b * W + 2 * W := by ring
    omega
  unfold blowupH
  have hcast : ((6 * b + 2) * W - 3 * b ^ 2 * d₀ - 3 * (W - t₀) ^ 2 / t₀ - 2 * (W - t₀) : ℕ) =
      ((6 * b + 2) * W - (3 * b ^ 2 * d₀ + 3 * (W - t₀) ^ 2 / t₀ + 2 * (W - t₀)) : ℕ) := by omega
  rw [hcast, Nat.cast_sub hsub_le]
  push_cast
  linarith

/-- `blowupH b W t₀ d₀` is monotone nondecreasing in `W` throughout `[b * d₀, b * t₀ - 1]`,
so its maximum over all admissible weights is attained at `min wMax (b * t₀ - 1)`. -/
theorem blowupH_mono {b W wMax t₀ d₀ : ℕ} (ht : 0 < t₀) (hbd : b * d₀ ≤ W)
    (hhi : W ≤ min wMax (b * t₀ - 1)) :
    blowupH b W t₀ d₀ ≤ blowupH b (min wMax (b * t₀ - 1)) t₀ d₀ := by
  have step : ∀ w, b * d₀ ≤ w → w + 1 ≤ b * t₀ - 1 →
      blowupH b w t₀ d₀ ≤ blowupH b (w + 1) t₀ d₀ := by
    intro w hwd hw1
    unfold blowupH
    have h1 : 3 * b ^ 2 * d₀ ≤ 3 * b * w := by nlinarith
    by_cases hwt : w < t₀
    · have hs0 : w - t₀ = 0 := by omega
      have hs1 : w + 1 - t₀ = 0 := by omega
      rw [hs0, hs1]
      simp only [Nat.zero_pow (by decide : 0 < 2), mul_zero, Nat.zero_div, Nat.sub_zero]
      exact Nat.sub_le_sub_right (Nat.mul_le_mul_left _ (Nat.le_succ w)) _
    · push Not at hwt
      have hs1 : w + 1 - t₀ = (w - t₀) + 1 := by omega
      have hdiff : 3 * ((w - t₀) + 1) ^ 2 ≤ 3 * (w - t₀) ^ 2 + (6 * b - 1) * t₀ := by
        have hbt : 1 ≤ b := by
          rcases Nat.eq_zero_or_pos b with rfl | hbpos
          · omega
          · exact hbpos
        have hle : w - t₀ + 1 ≤ b * t₀ - t₀ := by omega
        have h6 : 6 * (w - t₀) + 3 ≤ (6 * b - 1) * t₀ := by
          have hmul : 6 * (w - t₀ + 1) ≤ 6 * (b * t₀ - t₀) := Nat.mul_le_mul_left 6 hle
          have : (6 * b - 1) * t₀ = 6 * (b * t₀) - t₀ := by
            rw [Nat.sub_mul, one_mul, Nat.mul_assoc]
          omega
        nlinarith
      have hdiv_step : 3 * ((w - t₀) + 1) ^ 2 / t₀ ≤ 3 * (w - t₀) ^ 2 / t₀ + 6 * b := by
        have hA : 3 * (w - t₀) ^ 2 < (3 * (w - t₀) ^ 2 / t₀ + 1) * t₀ := by
          have := Nat.div_add_mod (3 * (w - t₀) ^ 2) t₀
          have := Nat.mod_lt (3 * (w - t₀) ^ 2) ht
          nlinarith
        have hB : 3 * ((w - t₀) + 1) ^ 2 < (3 * (w - t₀) ^ 2 / t₀ + 6 * b + 1) * t₀ := by
          have : (6 * b - 1) * t₀ ≤ 6 * b * t₀ := Nat.mul_le_mul_right t₀ (Nat.sub_le _ _)
          nlinarith
        exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul ht).mpr hB)
      have hsub_w : 3 * b ^ 2 * d₀ + 3 * (w - t₀) ^ 2 / t₀ + 2 * (w - t₀) ≤ (6 * b + 2) * w := by
        have h2 : 3 * (w - t₀) ^ 2 / t₀ ≤ 3 * b * w := by
          have : 3 * (w - t₀) ^ 2 ≤ 3 * b * w * t₀ := by
            have : w - t₀ ≤ w := Nat.sub_le w t₀
            have : w ≤ b * t₀ := by omega
            nlinarith
          exact Nat.div_le_of_le_mul (by linarith)
        have hlin : (6 * b + 2) * w = 3 * b * w + 3 * b * w + 2 * w := by ring
        omega
      have hmul_step : (6 * b + 2) * (w + 1) = (6 * b + 2) * w + 6 * b + 2 := by ring
      rw [hs1]
      omega
  have go : ∀ m, W ≤ m → m ≤ b * t₀ - 1 → blowupH b W t₀ d₀ ≤ blowupH b m t₀ d₀ := by
    intro m hWm
    refine Nat.le_induction (fun _ => le_rfl) (fun k hk ih hk1 => ?_) m hWm
    exact (ih (by omega)).trans (step k (hbd.trans hk) hk1)
  exact go (min wMax (b * t₀ - 1)) hhi (Nat.min_le_right _ _)

/-- Case-1 fallback bound: if every section assigned to a common factor `F` of degree `(b, m)`
with `b ≤ m` also lies on a coprime companion cofactor `Q'` of degree `(v₂ - j - b, s₂ - j - m)`,
then `F` carries at most `(s₂ - j + v₂ - j) * m` assigned sections. -/
theorem coprime_companion_fallback {F : Type} [Field F] (P Q' : F[X][X][X]) (prim : P.IsPrimitive)
    (G : Finset F) (w : F → F[X]) {b m v' s' : ℕ}
    (hb : P.natDegree = b) (hbm : b ≤ m) (hv' : Q'.natDegree ≤ v')
    (hp : WeightedSylvesterDegree.TotalDegreeLe P m)
    (hq : WeightedSylvesterDegree.TotalDegreeLe Q' s')
    (roots : ∀ z ∈ G, P.eval₂ (evalRingHom (C z)) (w z) = 0 ∧
      Q'.eval₂ (evalRingHom (C z)) (w z) = 0)
    (coprime : ∀ f : F[X][X][X], Irreducible f → 0 < f.natDegree → f ∣ P → ¬ f ∣ Q') :
    G.card ≤ (s' + v') * m := by
  have hres : G.card ≤ P.natDegree * s' + Q'.natDegree * m := by
    by_contra! tooMany
    obtain ⟨f, hirr, hpos, hdvd, hq'⟩ :=
      DoubleInterpolationCommonFactor.exists_common prim G w roots hp hq tooMany
    exact coprime f hirr hpos hdvd hq'
  rw [hb] at hres
  have h1 : b * s' ≤ m * s' := Nat.mul_le_mul_right s' hbm
  have h2 : Q'.natDegree * m ≤ v' * m := Nat.mul_le_mul_right m hv'
  nlinarith

/-! ## Mixed Hasse interpolants at 313,215,000 half-rate errors -/

/-- Exact scalar-coefficient constraint count at a site of order `r`. -/
def rowCount (s r : ℕ) : ℕ := ∑ j ∈ range r, (r - j) * (s + 1 - j)

theorem card_rows (s r : ℕ) : Fintype.card (JetRows s r) = rowCount s r := by
  simp only [JetRows, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, rowCount]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (r - j) * (s + 1 - j)) r

/-- Exact monomial count below the strict weighted-degree cap `W`. -/
def columnCount (s b D W : ℕ) : ℕ := ∑ j ∈ range (b + 1), (s + 1 - j) * (W - j * D)

theorem card_columns (s b D W : ℕ) : Fintype.card (Monomials s b D W) = columnCount s b D W := by
  simp only [Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, columnCount]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (s + 1 - j) * (W - j * D)) (b + 1)

/-- Exact mixed-Hasse rank surpluses for the primary `(88, 124, 188604)` and
companion `(174, 246, 14431)` surfaces at `e = 313,215,000`. -/
theorem ranks :
    columnCount 188604 124 d (88 * t) = n * rowCount 188604 88 + 152825916 ∧
    columnCount 14431 246 d (174 * t) = n * rowCount 14431 174 + 13495881357 := by
  decide +kernel

/-- The support and specialization guarantees for a nonzero received-row interpolant. -/
def SectionSurface {I F : Type} [Field F] (dom : I ↪ F) (u v : I → F)
    (s b D W : ℕ) (T : ℕ) : Prop :=
  ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
    (∀ j h x, ((Q.coeff j).coeff h).coeff x ≠ 0 → j ≤ b ∧ h + j ≤ s ∧ x + j * D < W) ∧
    (∀ x, Q.eval₂ (mapRingHom (evalRingHom (dom x)))
      (Polynomial.C (u x) + X * Polynomial.C (v x)) = 0) ∧
    ∀ g : F, ∀ q : F[X], q.natDegree ≤ D → ∀ S : Finset I, T ≤ S.card →
      (∀ x ∈ S, q.eval (dom x) = u x + g * v x) → Q.eval₂ (evalRingHom (Polynomial.C g)) q = 0

private theorem received_line_of_jet {F : Type} [Field F] {s b D W : ℕ}
    (a : Monomials s b D W → F) (x u v : F)
    (h : ∑ m, Polynomial.C (a m) * jetTerm m 0 0 x u v = 0) :
    (surface a).eval₂ (mapRingHom (evalRingHom x)) (Polynomial.C u + X * Polynomial.C v) = 0 := by
  rw [surface_received_line]
  convert h using 1
  unfold receivedLine
  apply sum_congr rfl
  intro m _
  simp only [jetTerm, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  rfl

set_option maxRecDepth 8192 in
/-- Both production surfaces exist on every length-`2^30` injective domain over any field
and vanish on every witnessing section with at least `t = 760,526,824` agreements. -/
theorem surfaces {I F : Type} [Fintype I] [Field F] (dom : I ↪ F) (u v : I → F)
    (hn : Fintype.card I = n) (companion : Bool) :
    let r := if companion then 174 else 88
    let b := if companion then 246 else 124
    let s := if companion then 14431 else 188604
    SectionSurface dom u v s b d (r * t) t := by
  cases companion
  · obtain ⟨a, ha, jets, hf⟩ := exists_surface dom u v (by decide : 0 < 88) (by decide : 0 < t)
      (by decide : 88 ≤ 188604 + 1) (by
        rw [hn, card_rows, card_columns]
        exact ranks.1 ▸ Nat.lt_add_of_pos_right (by decide))
    exact ⟨surface a, surface_ne_zero ha, fun _ _ _ h => surface_support a h,
      fun x => received_line_of_jet a _ _ _ (jets x 0 0 (by decide)),
      fun g q hq S hS hag => by rw [surface_eval]; exact hf g q hq S hS hag⟩
  · obtain ⟨a, ha, jets, hf⟩ := exists_surface dom u v (by decide : 0 < 174) (by decide : 0 < t)
      (by decide : 174 ≤ 14431 + 1) (by
        rw [hn, card_rows, card_columns]
        exact ranks.2 ▸ Nat.lt_add_of_pos_right (by decide))
    exact ⟨surface a, surface_ne_zero ha, fun _ _ _ h => surface_support a h,
      fun x => received_line_of_jet a _ _ _ (jets x 0 0 (by decide)),
      fun g q hq S hS hag => by rw [surface_eval]; exact hf g q hq S hS hag⟩

/-! ## Dual-constraint `(α, β)` Veronese and transverse allocation -/

private def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

private def unionAt (j a : ℕ) : ℕ :=
  ceilDiv (2 * a * j * core - j * (j - 1) * d) (a * (a + 1))

private def discreteUnion (j : ℕ) : ℕ :=
  let a₁ := 7 * j / 10
  let a₂ := (7 * j + 9) / 10
  let u₁ := if 1 ≤ a₁ ∧ a₁ < j then unionAt j a₁ else 0
  let u₂ := if 1 ≤ a₂ ∧ a₂ < j then unionAt j a₂ else 0
  max u₁ u₂

/-- Upper bound on the scalar population assigned to `j` rich polynomial affine heads. -/
def headMass (j : ℕ) : ℕ :=
  if j < 3 then j * (e + 1) else
    let cover := max (discreteUnion j) (ceilDiv (j * core ^ 2) (core + (j - 1) * d))
    min (j * (e + 1)) (j * n - (j - 1) * cover)

/-- Blown-up height bound maximized over `W ∈ [b * d, min (88 * t - 1 - j * d) (b * t - 1)]`. -/
def maxBlowupH (j b : ℕ) : ℕ :=
  blowupH b (min (88 * t - 1 - j * d) (b * t - 1)) t d

/-- Base price per unit of actual companion degree (triangle determinant, plus transverse
tangent bound when `j ≥ 3`), valid for every actual plane degree `m ≥ b`. -/
def basePrice (j b : ℕ) : ℕ :=
  let H := maxBlowupH j b
  let R := (2 * b - 1) * n
  let p := min j 2
  let tri := 2 * b + ceilDiv ((3 - p) * (R + H)) (3 * t - (n + 2 * d + p * miss))
  let trv := if 3 ≤ j then 2 * b + ceilDiv (H + R) (t + discreteUnion j - (n + d)) else tri
  4 * b - 2 + min tri trv

/-- Veronese price per unit of actual companion degree at `j = 0` for `(s, a)`
valid whenever `m > s * (s - 1)`. -/
def veronesePrice (b s a h C_a E_s : ℕ) : ℕ :=
  let H := maxBlowupH 0 b
  let R := (2 * b - 1) * n
  let gap := a * h * t - (C_a * n + E_s * d)
  4 * b - 2 + 2 * s * b + ceilDiv (h * (a * R + s * H)) gap

/-- Price per unit of actual companion degree at `j = 0` valid for `m > 6 * 5 = 30`. -/
def price6 (b : ℕ) : ℕ := min (basePrice 0 b) (veronesePrice b 6 5 28 35 112)

/-- Price per unit of actual companion degree at `j = 0` valid for `m > 12 * 11 = 132`. -/
def price12 (b : ℕ) : ℕ := min (price6 b) (veronesePrice b 12 10 91 220 728)

/-- Price per unit of actual companion degree at `j = 0` valid for `m > 24 * 23 = 552`. -/
def price24 (b : ℕ) : ℕ := min (price12 b) (veronesePrice b 24 20 325 1540 5200)

/-- The five non-nonlinear label classes: rich heads, scalar-only primary factors,
single noncommon resultant, small polynomial heads, and nonaffine common linear factors. -/
def otherLabels (j : ℕ) : ℕ :=
  headMass j + 188604 + (188604 * 246 + 124 * 14431) + (124 - j) * 188604 + (14431 - j) * 21

/-- Linear-duality slope per unit of actual companion degree `m`. -/
def alpha (j : ℕ) : ℕ :=
  if j = 0 then 131427 else (bound - otherLabels j) / (14431 - j)

/-- Linear-duality surcharge per unit of actual ordinate degree `b` (nonzero only at `j = 0`). -/
def beta (j : ℕ) : ℕ :=
  if j = 0 then 27182 else 0

/-- All denominator positivity, core-collinearity, identity-site, Veronese-gap, tame
characteristic, and global budget requirements hold strictly. -/
theorem parameters :
    n + 2 * d < 3 * core ∧ e < miss * 188604 ∧ 14431 < 188604 ∧
    4 * n ≤ 20 * (t - d) ∧
    n + 2 * d + 2 * miss < 3 * t ∧
    35 * n + 112 * d < 5 * 28 * t ∧
    220 * n + 728 * d < 10 * 91 * t ∧
    1540 * n + 5200 * d < 20 * 325 * t ∧
    2 * (88 * t) * 124 < 2 ^ 100 ∧ 14431 * 14430 < 2 ^ 100 ∧
    bound < 2 * n ∧
    otherLabels 0 + 14431 * alpha 0 + 124 * beta 0 ≤ bound ∧
    (∀ j : Fin 125, 3 ≤ j.val →
      ((1 ≤ 7 * j.val / 10 ∧ 7 * j.val / 10 < j.val) ∨
       (1 ≤ (7 * j.val + 9) / 10 ∧ (7 * j.val + 9) / 10 < j.val)) ∧
      n + d < t + discreteUnion j.val) := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Every `(j, b)` pair satisfies the weight admissibility, Case-1 companion fallback,
and dual-constraint `(α, β)` pricing across all Veronese degree regimes. -/
theorem dual_prices :
    ∀ j : Fin 125,
      otherLabels j.val + (14431 - j.val) * alpha j.val + (124 - j.val) * beta j.val ≤ bound ∧
      (2 ≤ 124 - j.val → (14431 - j.val) + (246 - j.val) ≤ alpha j.val) ∧
      ∀ b : Fin (124 - j.val + 1), 2 ≤ b.val →
        b.val * d ≤ 88 * t - 1 - j.val * d ∧
        if j.val = 0 then
          price24 b.val ≤ alpha 0 ∧
          (b.val ≤ 30 → (basePrice 0 b.val - alpha 0) * 30 ≤ beta 0 * b.val) ∧
          (b.val ≤ 132 → (price6 b.val - alpha 0) * 132 ≤ beta 0 * b.val) ∧
          (b.val ≤ 552 → (price12 b.val - alpha 0) * 552 ≤ beta 0 * b.val)
        else
          basePrice j.val b.val ≤ alpha j.val := by
  decide +kernel

/-- Applicable per-unit-`m` nonlinear price for an actual factor of degrees `(b, m)`. -/
def factorUnitPrice (j b m : ℕ) : ℕ :=
  if j = 0 then
    if 552 < m then price24 b
    else if 132 < m then price12 b
    else if 30 < m then price6 b
    else basePrice 0 b
  else basePrice j b

private theorem factor_dual_bound (j : Fin 125) {b m : ℕ}
    (hb : 2 ≤ b) (hbhi : b ≤ 124 - j.val) (hbm : b ≤ m) :
    m * factorUnitPrice j.val b m ≤ m * alpha j.val + b * beta j.val := by
  have h := ((dual_prices j).2.2 ⟨b, by omega⟩ hb).2
  by_cases hj : j.val = 0
  · simp only [hj, ↓reduceIte] at h
    unfold factorUnitPrice
    simp only [hj, ↓reduceIte]
    split_ifs with h552 h132 h30
    · exact (Nat.mul_le_mul_left m h.1).trans (Nat.le_add_right _ _)
    · have hle : b ≤ 552 := by omega
      have h5 := h.2.2.2 hle
      by_cases hu : price12 b ≤ alpha 0
      · exact (Nat.mul_le_mul_left m hu).trans (Nat.le_add_right _ _)
      · have hdiff : m * (price12 b - alpha 0) ≤ (price12 b - alpha 0) * 552 := by
          rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
        have hstep : m * price12 b = m * alpha 0 + m * (price12 b - alpha 0) := by
          rw [← Nat.mul_add, Nat.add_sub_of_le (by omega)]
        rw [hstep]
        have hbb : beta 0 * b = b * beta 0 := mul_comm _ _
        omega
    · have hle : b ≤ 132 := by omega
      have h4 := h.2.2.1 hle
      by_cases hu : price6 b ≤ alpha 0
      · exact (Nat.mul_le_mul_left m hu).trans (Nat.le_add_right _ _)
      · have hdiff : m * (price6 b - alpha 0) ≤ (price6 b - alpha 0) * 132 := by
          rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
        have hstep : m * price6 b = m * alpha 0 + m * (price6 b - alpha 0) := by
          rw [← Nat.mul_add, Nat.add_sub_of_le (by omega)]
        rw [hstep]
        have hbb : beta 0 * b = b * beta 0 := mul_comm _ _
        omega
    · have hle : b ≤ 30 := by omega
      have h3 := h.2.1 hle
      by_cases hu : basePrice 0 b ≤ alpha 0
      · exact (Nat.mul_le_mul_left m hu).trans (Nat.le_add_right _ _)
      · have hdiff : m * (basePrice 0 b - alpha 0) ≤ (basePrice 0 b - alpha 0) * 30 := by
          rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
        have hstep : m * basePrice 0 b = m * alpha 0 + m * (basePrice 0 b - alpha 0) := by
          rw [← Nat.mul_add, Nat.add_sub_of_le (by omega)]
        rw [hstep]
        have hbb : beta 0 * b = b * beta 0 := mul_comm _ _
        omega
  · simp only [hj, ↓reduceIte] at h
    unfold factorUnitPrice
    simp only [hj, ↓reduceIte]
    exact (Nat.mul_le_mul_left m h).trans (Nat.le_add_right _ _)

/-- Total bad-scalar allocation across all six label classes at `313,215,000` half-rate errors.
Accepts both blown-up Gauss-graph factors (`pop ≤ deg * factorUnitPrice`) and Case-1
companion-cofactor fallback factors (`pop ≤ deg * ((14431 - j) + (246 - j))`). -/
theorem allocation {J : Type*} (S : Finset J) (degree value pop : J → ℕ) (j : Fin 125)
    (heads scalar outside small linear : ℕ)
    (hheads : heads ≤ headMass j.val)
    (hscalar : scalar ≤ 188604)
    (houtside : outside ≤ 188604 * 246 + 124 * 14431)
    (hsmall : small ≤ (124 - j.val) * 188604)
    (hlinear : linear ≤ (14431 - j.val) * 21)
    (htotalDeg : ∑ i ∈ S, degree i ≤ 14431 - j.val)
    (htotalVal : ∑ i ∈ S, value i ≤ 124 - j.val)
    (hvalue : ∀ i ∈ S, 2 ≤ value i ∧ value i ≤ degree i)
    (hpop : ∀ i ∈ S,
      pop i ≤ degree i * factorUnitPrice j.val (value i) (degree i) ∨
      pop i ≤ degree i * ((14431 - j.val) + (246 - j.val))) :
    heads + scalar + outside + small + linear + ∑ i ∈ S, pop i ≤ bound := by
  have each (i : J) (hi : i ∈ S) : pop i ≤ degree i * alpha j.val + value i * beta j.val := by
    obtain ⟨hlo, hvm⟩ := hvalue i hi
    have hhi : value i ≤ 124 - j.val :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi).trans htotalVal
    rcases hpop i hi with hgeom | hcase1
    · exact hgeom.trans (factor_dual_bound j hlo hhi hvm)
    · have h2 : 2 ≤ 124 - j.val := hlo.trans hhi
      exact (hcase1.trans (Nat.mul_le_mul_left _ ((dual_prices j).2.1 h2))).trans
        (Nat.le_add_right _ _)
  have hsum : ∑ i ∈ S, pop i ≤
      (∑ i ∈ S, degree i) * alpha j.val + (∑ i ∈ S, value i) * beta j.val := by
    calc ∑ i ∈ S, pop i ≤ ∑ i ∈ S, (degree i * alpha j.val + value i * beta j.val) :=
          Finset.sum_le_sum each
      _ = (∑ i ∈ S, degree i) * alpha j.val + (∑ i ∈ S, value i) * beta j.val := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have h1 := Nat.mul_le_mul_right (alpha j.val) htotalDeg
  have h2 := Nat.mul_le_mul_right (beta j.val) htotalVal
  have htot := (dual_prices j).1
  unfold otherLabels at htot
  omega

#print axioms factor_order_sum_ge
#print axioms volume_excess_cancel
#print axioms nef_weight_cauchy_schwarz
#print axioms blowupH_ge_rat
#print axioms blowupH_mono
#print axioms coprime_companion_fallback
#print axioms ranks
#print axioms surfaces
#print axioms parameters
#print axioms dual_prices
#print axioms allocation

end ArkLib.ProximityGap.Frontier.HalfBlowupGaussWindow
