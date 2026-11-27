/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude

Ported from mitschabaude-bot/ArkLib:reduced-rate (commit 93fd4833b88fb0b964a29d9ca8cbbcd7ca781ba4)
to keep canonical ArkLib/Data/CodingTheory/HiddenDerivative/ untouched on the 31ff7ddf pin.
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.InterpolationBounds
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.JohnsonCertificate

/-!
# Curve-height slot surplus and degree bounds for Johnson power curves

Companion extension module collecting the curve-height interpolation slot counts
(`johnsonCurveSourceSlotCount`, `johnsonCurveRowSlotCount`,
`johnson_curve_interpolation_slot_surplus`) and degree-`ℓ` Johnson matrix bounds
(`sum_johnsonColumns_curveSlots`, `sum_johnsonFinRowWeight_curveSlots`,
`johnsonFinMatrix_curve_degree_le`) used by `Johnson/Curve.lean`.
-/

namespace ReedSolomon.HiddenDerivative

noncomputable section

private theorem sum_linear_product_succ (X D Z : ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), (X - D * i) * (Z - i)) =
      X * (m + 1) * Z - X * ((m : ℝ) * (m + 1) / 2) -
      D * ((m : ℝ) * (m + 1) / 2) * Z +
      D * ((m : ℝ) * (m + 1) * (2 * m + 1) / 6) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem staircase_closed_form_lower {d X dy y z : ℝ}
    (hd : 0 ≤ d) (hdy_y : dy ≤ y) (hy : 0 ≤ y)
    (hy_lt : y < dy + 1) (hyz : y ≤ z) (hdX : d * dy ≤ X) :
    d * (dy * (dy + 1) / 2 * z - (dy ^ 3 - dy) / 6) ≤
      X * y * z - X * (y * (y - 1) / 2) -
      d * (y * (y - 1) / 2) * z + d * (y * (y - 1) * (2 * y - 1) / 6) := by
  let r := y - dy
  have hr0 : 0 ≤ r := sub_nonneg.mpr hdy_y
  have hr1 : r ≤ 1 := sub_le_iff_le_add'.2 hy_lt.le
  have hbracket : 0 ≤ 3 * z + 1 - 3 * dy - 2 * r := by
    dsimp only [r]
    linarith only [hyz, hdy_y]
  have hround : 0 ≤ d * r * (1 - r) * (3 * z + 1 - 3 * dy - 2 * r) / 6 := by
    positivity
  have hcoeff : 0 ≤ y * z - y * (y - 1) / 2 := by
    have hb : 0 ≤ z - (y - 1) / 2 := by linarith only [hyz, hy]
    exact (mul_nonneg hy hb).trans_eq (by ring)
  have hxgain : 0 ≤ (X - d * dy) * (y * z - y * (y - 1) / 2) :=
    mul_nonneg (sub_nonneg.mpr hdX) hcoeff
  have hroundId :
      (d * dy * y * z - d * dy * (y * (y - 1) / 2) -
          d * (y * (y - 1) / 2) * z +
          d * (y * (y - 1) * (2 * y - 1) / 6)) -
        d * (dy * (dy + 1) / 2 * z - (dy ^ 3 - dy) / 6) =
          d * r * (1 - r) * (3 * z + 1 - 3 * dy - 2 * r) / 6 := by
    dsimp only [r]
    ring
  have hxgainId :
      (X * y * z - X * (y * (y - 1) / 2)) -
        (d * dy * y * z - d * dy * (y * (y - 1) / 2)) =
          (X - d * dy) * (y * z - y * (y - 1) / 2) := by ring
  linarith only [hroundId, hxgainId, hround, hxgain]

/-! ### Curve interpolation counts

A received curve `∑ t, z ^ t w_t` has challenge degree `ℓ`. The curve interpolant takes challenge
height `ℓ h`, and its column of `y`-degree `j` has challenge degree below `ℓ h + 1 - ℓ j`, so the
scalar counts are those of the line at the real height `h + 1 / ℓ`, scaled by `ℓ`. -/

/-- The number of source coefficients `∑_{j ≤ μ} (X - D j)(H + 1 - ℓ j)` of the curve
interpolant of challenge height `H` for a received curve of challenge degree `ℓ`. -/
def johnsonCurveSourceSlotCount (X D μ ℓ H : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (μ + 1), (X - D * j) * (H + 1 - ℓ * j)

/-- The number of scalar multiplicity constraints `n ∑_{b < m} (m - b)(H + 1 - ℓ b)` of the curve
interpolant of challenge height `H` for a received curve of challenge degree `ℓ`. -/
def johnsonCurveRowSlotCount (n m ℓ H : ℕ) : ℕ :=
  n * ∑ b ∈ Finset.range m, (m - b) * (H + 1 - ℓ * b)

private theorem curveSourceSlotCount_cast {X D μ ℓ h : ℕ} (hℓ : 0 < ℓ)
    (hDX : D * μ < X) (hμh : μ ≤ h) :
    (johnsonCurveSourceSlotCount X D μ ℓ (ℓ * h) : ℝ) =
      ℓ * ((X : ℝ) * (μ + 1) * (h + 1 / ℓ) -
        (X : ℝ) * ((μ : ℝ) * (μ + 1) / 2) -
        (D : ℝ) * ((μ : ℝ) * (μ + 1) / 2) * (h + 1 / ℓ) +
        (D : ℝ) * ((μ : ℝ) * (μ + 1) * (2 * μ + 1) / 6)) := by
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne'
  rw [johnsonCurveSourceSlotCount, ← sum_linear_product_succ, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  have hjμ : j ≤ μ := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [Nat.cast_sub ((Nat.mul_le_mul_left D hjμ).trans (Nat.le_of_lt hDX))]
  rw [Nat.cast_sub ((Nat.mul_le_mul_left ℓ (hjμ.trans hμh)).trans (Nat.le_succ _))]
  push_cast
  field_simp

private theorem curveRowSlotCount_cast {n m ℓ h : ℕ} (hℓ : 0 < ℓ) (hmh : m ≤ h + 1) :
    (johnsonCurveRowSlotCount n m ℓ (ℓ * h) : ℝ) =
      ℓ * ((n : ℝ) * ((m : ℝ) * (m + 1) / 2 * (h + 1 / ℓ) -
        ((m : ℝ) ^ 3 - m) / 6)) := by
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne'
  rw [johnsonCurveRowSlotCount]
  push_cast
  cases m with
  | zero => simp
  | succ q =>
      have hs := sum_linear_product_succ ((q + 1 : ℕ) : ℝ) 1 (h + 1 / ℓ) q
      simp only [one_mul] at hs
      have hsum : (∑ b ∈ Finset.range (q + 1),
          (((q + 1 - b : ℕ) : ℝ) * ((ℓ * h + 1 - ℓ * b : ℕ) : ℝ))) =
          ℓ * ∑ b ∈ Finset.range (q + 1),
            (((q + 1 : ℕ) : ℝ) - b) * ((h + 1 / ℓ : ℝ) - b) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        have hbm : b ≤ q + 1 := Nat.le_of_lt (Finset.mem_range.mp hb)
        have hbh : b ≤ h := by have := Finset.mem_range.mp hb; omega
        rw [Nat.cast_sub hbm,
          Nat.cast_sub ((Nat.mul_le_mul_left ℓ hbh).trans (Nat.le_succ _))]
        push_cast
        field_simp
      rw [hsum, hs]
      push_cast
      ring

/-- The candidate cutoff stays strictly below the challenge cutoff, `μ + 1 ≤ h`, when the
agreement fraction `√ρ₋ + η` is at most `1`. In real terms `t / √ρ₋ + 1 ≤ t² / (3ρ₋)`, i.e.
`t² ≥ 3 t √ρ₋ + 3 ρ₋`: for `√ρ₋ ≤ 23/25` this follows from `t ≥ 7/2`, and otherwise
`η ≤ 1 - √ρ₋ < 2/25` forces `t ≥ √ρ₋ / (2η) + 1/2 > 6`. -/
theorem johnsonMu_add_one_le_H {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) (heta : 0 < eta) (ha : johnsonAgreement n D eta ≤ 1) :
    johnsonMu n D eta + 1 ≤ johnsonH n D eta := by
  let x := √(johnsonRhoMinus n D)
  let t := johnsonT n D eta
  have hx := johnsonSqrt_mem_Ioo hD hDn
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have hx2 : x ^ 2 = johnsonRhoMinus n D :=
    Real.sq_sqrt (johnsonRhoMinus_pos hD hDn).le
  have ht : 7 / 2 ≤ t := johnsonT_ge_seven_halves n D eta
  have hgap : x / 2 ≤ (johnsonM n D eta : ℝ) * eta := johnson_half_gap n D heta
  have hmt : (johnsonM n D eta : ℝ) = t - 1 / 2 := by
    simp only [t, johnsonT]
    ring
  have hetax : eta ≤ 1 - x := by
    unfold johnsonAgreement at ha
    linarith only [ha]
  have hquad : 3 * t * x + 3 * x ^ 2 ≤ t ^ 2 := by
    rcases le_or_gt x (23 / 25) with hxs | hxl
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hxs),
        mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ht)]
    · have hprod : x / 2 ≤ (t - 1 / 2) * (1 - x) := by
        rw [hmt] at hgap
        exact hgap.trans (mul_le_mul_of_nonneg_left hetax (by linarith only [ht]))
      have ht6 : 6 ≤ t := by nlinarith
      nlinarith
  have hreal : t / x + 1 ≤ t ^ 2 / (3 * johnsonRhoMinus n D) := by
    rw [← hx2, div_add_one hx0.ne', div_le_div_iff₀ hx0 (by positivity)]
    nlinarith
  have hceil := Nat.ceil_mono hreal
  rw [Nat.ceil_add_one (div_pos (by linarith only [ht]) hx0).le] at hceil
  rw [← johnsonMu_add_one hD hDn, ← johnsonH_add_one hD hDn] at hceil
  omega

/-- At the rounded Johnson cutoffs and challenge height `ℓ h`, the curve source-slot count
strictly exceeds the curve row-slot count, for every challenge degree `ℓ ≥ 1`. Both counts are
`ℓ` times the line counts at the real height `z = h + 1 / ℓ`. The line comparison holds at `z`
because `z > h ≥ t² / (3ρ₋) - 1` and the slack of the line comparison at `t² / (3ρ₋)` exceeds
one unit of height; the staircase lower bound needs `μ + 1 ≤ z`, which is
`johnsonMu_add_one_le_H`. -/
theorem johnson_curve_interpolation_slot_surplus {n D ℓ : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) (heta : 0 < eta) (ha : johnsonAgreement n D eta ≤ 1)
    (hℓ : 0 < ℓ) :
    johnsonCurveRowSlotCount n (johnsonM n D eta) ℓ (ℓ * johnsonH n D eta) <
      johnsonCurveSourceSlotCount (johnsonXCutoff n D eta) D
        (johnsonMu n D eta) ℓ (ℓ * johnsonH n D eta) := by
  let x := √(johnsonRhoMinus n D)
  let t := johnsonT n D eta
  let m := johnsonM n D eta
  let μ := johnsonMu n D eta
  let h := johnsonH n D eta
  let Xc := johnsonXCutoff n D eta
  let dy := t / x
  let z : ℝ := h + 1 / ℓ
  change johnsonCurveRowSlotCount n m ℓ (ℓ * h) <
    johnsonCurveSourceSlotCount Xc D μ ℓ (ℓ * h)
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx := johnsonSqrt_mem_Ioo hD hDn
  have hx0 : 0 < x := by exact hx.1
  have hx2 : x ^ 2 = johnsonRhoMinus n D :=
    Real.sq_sqrt (johnsonRhoMinus_pos hD hDn).le
  have ht : 7 / 2 ≤ t := johnsonT_ge_seven_halves n D eta
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hm3 : 3 ≤ m := johnsonM_ge_three n D eta
  have ht_def : t = (m : ℝ) + 1 / 2 := by rfl
  have hDreal : (D : ℝ) = n * x ^ 2 := by
    rw [hx2]
    unfold johnsonRhoMinus
    field_simp
  have hμh : μ ≤ h := johnsonMu_le_H hDn
  have hμh1 : μ + 1 ≤ h := johnsonMu_add_one_le_H hD hDn heta ha
  have hmz : m ≤ h + 1 := johnsonM_le_H_add_one hD hDn
  have hDX : D * μ < Xc := johnson_D_mul_mu_lt_XCutoff hD hDn
  have hsource := curveSourceSlotCount_cast hℓ hDX hμh
  have hrow := curveRowSlotCount_cast (n := n) hℓ hmz
  have hdy0 : 0 ≤ dy := (div_pos ht0 hx0).le
  have hdy_y : dy ≤ (μ + 1 : ℕ) := by
    rw [johnsonMu_add_one hD hDn]
    exact Nat.le_ceil _
  have hy_lt : ((μ + 1 : ℕ) : ℝ) < dy + 1 := by
    rw [johnsonMu_add_one hD hDn]
    exact Nat.ceil_lt_add_one hdy0
  have hhz : (h : ℝ) < z := by
    dsimp only [z]
    linarith only [one_div_pos.mpr hℓR]
  have hyz : ((μ + 1 : ℕ) : ℝ) ≤ z :=
    (show ((μ + 1 : ℕ) : ℝ) ≤ h by exact_mod_cast hμh1).trans hhz.le
  have hX : (D : ℝ) * dy ≤ Xc := by
    have heq : (D : ℝ) * dy = t * n * x := by
      dsimp only [dy]
      rw [hDreal]
      field_simp [hx0.ne']
    rw [heq]
    unfold Xc johnsonXCutoff
    exact Nat.le_ceil _
  have hsourceLower := staircase_closed_form_lower
    (d := (D : ℝ)) (X := (Xc : ℝ)) (dy := dy)
    (y := ((μ + 1 : ℕ) : ℝ)) (z := z)
    (by positivity) hdy_y (by positivity) hy_lt hyz hX
  have hz0 : t ^ 2 / (3 * x ^ 2) - 1 < z := by
    have hceil : t ^ 2 / (3 * x ^ 2) ≤ (h : ℝ) + 1 := by
      have := Nat.le_ceil (t ^ 2 / (3 * x ^ 2))
      rw [hx2, ← johnsonH_add_one hD hDn] at this
      rw [hx2]
      exact_mod_cast this
    linarith only [hceil, hhz]
  have hcoef : 0 < t * x + 1 / 4 :=
    add_pos_of_nonneg_of_pos (mul_nonneg ht0.le hx0.le) (by norm_num)
  have hmreal : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hmain :
      (n : ℝ) * ((m : ℝ) * (m + 1) / 2 * z - ((m : ℝ) ^ 3 - m) / 6) <
        (D : ℝ) * (dy * (dy + 1) / 2 * z - (dy ^ 3 - dy) / 6) := by
    have hcoefId :
        (D : ℝ) * (dy * (dy + 1)) - n * ((m : ℝ) * (m + 1)) =
          n * (t * x + 1 / 4) := by
      dsimp only [dy]
      rw [hDreal, ht_def]
      field_simp [hx0.ne']
      ring
    have hcubicId :
        (D : ℝ) * (dy ^ 3 - dy) - n * ((m : ℝ) ^ 3 - m) =
          n * (t ^ 3 / x - t * x - ((m : ℝ) ^ 3 - m)) := by
      dsimp only [dy]
      rw [hDreal]
      field_simp [hx0.ne']
    have hpositiveBelowCutoff :
        0 ≤ 3 * (t * x + 1 / 4) * (t ^ 2 / (3 * x ^ 2) - 1) -
          (t ^ 3 / x - t * x - ((m : ℝ) ^ 3 - m)) := by
      have hid : 3 * (t * x + 1 / 4) * (t ^ 2 / (3 * x ^ 2) - 1) -
          (t ^ 3 / x - t * x - ((m : ℝ) ^ 3 - m)) =
          t ^ 2 / (4 * x ^ 2) + ((m : ℝ) ^ 3 - m - 2 * t * x - 3 / 4) := by
        field_simp
        ring
      have htx : t * x ≤ t := mul_le_of_le_one_right ht0.le hx.2.le
      have hcubic : 0 ≤ (m : ℝ) ^ 3 - m - 2 * t * x - 3 / 4 := by
        rw [ht_def] at htx
        nlinarith [mul_nonneg (sub_nonneg.mpr hmreal) (sub_nonneg.mpr hmreal)]
      rw [hid]
      positivity
    have hscaled :
        3 * (t * x + 1 / 4) * (t ^ 2 / (3 * x ^ 2) - 1) <
          3 * (t * x + 1 / 4) * z :=
      mul_lt_mul_of_pos_left hz0 (mul_pos three_pos hcoef)
    have hbracket :
        0 < 3 * (t * x + 1 / 4) * z -
          (t ^ 3 / x - t * x - ((m : ℝ) ^ 3 - m)) := by
      linarith only [hpositiveBelowCutoff, hscaled]
    have hdiff :
        (D : ℝ) * (dy * (dy + 1) / 2 * z - (dy ^ 3 - dy) / 6) -
          (n : ℝ) * ((m : ℝ) * (m + 1) / 2 * z - ((m : ℝ) ^ 3 - m) / 6) =
          (n : ℝ) / 6 * (3 * (t * x + 1 / 4) * z -
            (t ^ 3 / x - t * x - ((m : ℝ) ^ 3 - m))) := by
      calc
        _ = 1 / 6 *
            (3 * ((D : ℝ) * (dy * (dy + 1)) - n * ((m : ℝ) * (m + 1))) * z -
              ((D : ℝ) * (dy ^ 3 - dy) - n * ((m : ℝ) ^ 3 - m))) := by ring
        _ = _ := by rw [hcoefId, hcubicId]; ring
    rw [← sub_pos, hdiff]
    exact mul_pos (div_pos hn (by norm_num)) hbracket
  have hsourceLower' :
      (D : ℝ) * (dy * (dy + 1) / 2 * z - (dy ^ 3 - dy) / 6) ≤
        (Xc : ℝ) * (μ + 1) * z - (Xc : ℝ) * ((μ : ℝ) * (μ + 1) / 2) -
          (D : ℝ) * ((μ : ℝ) * (μ + 1) / 2) * z +
          (D : ℝ) * ((μ : ℝ) * (μ + 1) * (2 * μ + 1) / 6) := by
    convert hsourceLower using 1
    push_cast
    ring
  have hcast : (johnsonCurveRowSlotCount n m ℓ (ℓ * h) : ℝ) <
      (johnsonCurveSourceSlotCount Xc D μ ℓ (ℓ * h) : ℝ) := by
    rw [hrow, hsource]
    exact mul_lt_mul_of_pos_left (hmain.trans_le hsourceLower') hℓR
  exact_mod_cast hcast


end

namespace SymbolicReceivedInterpolation

open Polynomial

/-- Enumerating the columns preserves the curve source-slot count at challenge degree `ℓ` and
height `H`. -/
theorem sum_johnsonColumns_curveSlots (X D μ ℓ H : ℕ) :
    Finset.univ.sum (fun j : Fin (Fintype.card (JohnsonColumnIndex X D μ)) ↦
      H + 1 - ℓ * (johnsonColumns X D μ j).y₀) = johnsonCurveSourceSlotCount X D μ ℓ H := by
  let e := Fintype.equivFin (JohnsonColumnIndex X D μ)
  calc
    _ = Finset.univ.sum (fun q : JohnsonColumnIndex X D μ ↦ H + 1 - ℓ * q.1.val) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro q _
      simp [e, johnsonColumns]
    _ = Finset.univ.sum (fun j : Fin (μ + 1) ↦
        (X - D * j.val) * (H + 1 - ℓ * j.val)) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro j _
      simp
    _ = johnsonCurveSourceSlotCount X D μ ℓ H := by
      rw [johnsonCurveSourceSlotCount, ← Fin.sum_univ_eq_sum_range]

/-- Enumerating the triangular rows preserves the curve row-slot count at challenge degree `ℓ`
and height `H`. -/
theorem sum_johnsonFinRowWeight_curveSlots {n : ℕ} (m ℓ H : ℕ) :
    Finset.univ.sum (fun i : Fin (Fintype.card (JohnsonRowIndex n m)) ↦
      H + 1 - ℓ * johnsonFinRowWeight m i) = johnsonCurveRowSlotCount n m ℓ H := by
  let e := Fintype.equivFin (JohnsonRowIndex n m)
  calc
    _ = Finset.univ.sum (fun row : JohnsonRowIndex n m ↦ H + 1 - ℓ * row.2.1.val) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro row _
      simp [e, johnsonFinRowWeight]
    _ = n * Finset.univ.sum (fun q : JohnsonLocalRowIndex m ↦ H + 1 - ℓ * q.1.val) := by
      rw [Fintype.sum_prod_type]
      simp
    _ = n * Finset.univ.sum (fun q : Fin m ↦
        (m - q.val) * (H + 1 - ℓ * q.val)) := by
      congr 1
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro q _
      simp
    _ = johnsonCurveRowSlotCount n m ℓ H := by
      rw [johnsonCurveRowSlotCount, ← Fin.sum_univ_eq_sum_range]

/-- For received values of challenge degree at most `ℓ`, the Johnson constraint matrix satisfies
the shifted degree premise `ℓ (j - e)`. -/
theorem johnsonConstraintMatrix_curve_degree_le {F : Type*} [Field F] {n : ℕ}
    (X D μ m ℓ : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ) (row : JohnsonRowIndex n m)
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ))) :
    (johnsonConstraintMatrix X D μ m centers w row j).natDegree ≤
      ℓ * ((johnsonColumns X D μ j).y₀ - row.2.1.val) := by
  have h := natDegree_localConstraintMatrix_le_sub m ℓ
    centers w hw (johnsonColumns X D μ)
    (row.1, johnsonLocalRow m row.2) j
  simpa [johnsonConstraintMatrix, johnsonLocalRow_localJetDegree] using h

/-- For received values of challenge degree at most `ℓ`, flattened entries satisfy the shifted
degree premise `ℓ (j - e)`. -/
theorem johnsonFinMatrix_curve_degree_le {F : Type*} [Field F] {n : ℕ}
    (X D μ m ℓ : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (i : Fin (Fintype.card (JohnsonRowIndex n m)))
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ))) :
    (johnsonFinMatrix X D μ m centers w i j).natDegree ≤
      ℓ * ((johnsonColumns X D μ j).y₀ - johnsonFinRowWeight m i) := by
  simpa [johnsonFinMatrix, johnsonFinRowWeight] using
    johnsonConstraintMatrix_curve_degree_le X D μ m ℓ centers w hw
      ((Fintype.equivFin (JohnsonRowIndex n m)).symm i) j

end SymbolicReceivedInterpolation

end ReedSolomon.HiddenDerivative

#print axioms ReedSolomon.HiddenDerivative.johnsonMu_add_one_le_H
#print axioms ReedSolomon.HiddenDerivative.johnson_curve_interpolation_slot_surplus
#print axioms ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation.sum_johnsonColumns_curveSlots
#print axioms ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation.sum_johnsonFinRowWeight_curveSlots
#print axioms ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation.johnsonFinMatrix_curve_degree_le
