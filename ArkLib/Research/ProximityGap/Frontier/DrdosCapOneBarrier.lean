/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FirstOrderZeroCapJohnson

/-! # Exact Johnson boundary for linear-in-derivative (`M = 1`) first-order interpolation

For a first-order hidden-derivative interpolant with first-derivative cap `M = 1`
(linear in `Y₁`, including all linear and Riccati ODEs), the graded rank profile has
total row count `n (m² + 1)`, while the source columns split into `b = 0` (weight `D`)
and `b = 1` (weight `D - 1`).

The linear-in-`m` deficit of the `b = 0` layer and linear-in-`m` surplus of the `b = 1`
layer cancel identically. Consequently:

* Strictly beyond Johnson (`A² < n D`), every prefix of the column profile is bounded
  by the corresponding prefix of the row profile, so by Abel's inequality NO shifted
  first-order certificate with `M = 1` can achieve a slot surplus for any multiplicity
  `m`, total jet degree `μ`, challenge weight `ℓ`, or height `h`.
* At exact Johnson equality (`A² = n D`), the `+1` slack from `wt(Y₁) = D - 1 < D`
  yields a strict surplus at multiplicity `m = D (A + 1)`.

Together with `FirstOrderZeroCapJohnson` (`M = 0 ↔ n D < A²`), this proves the exact
sharp hierarchy:
- `M = 0` achieves surplus iff `n D < A²` (strictly below Johnson),
- `M = 1` achieves surplus iff `n D ≤ A²` (at or below Johnson),
- Every strictly beyond-Johnson (`A² < n D`) shifted first-order certificate requires
  `2 ≤ M` (nonlinear in `Y₁`) and `2 ≤ μ`.
-/
set_option autoImplicit false
namespace ProximityGap.DrdosCapOneBarrier
open Finset ReedSolomon.HiddenDerivative

/-- Closed-form graded rank profile at first-derivative cap `M = 1`. -/
def rowLayerOne (m t : ℕ) : ℕ :=
  if t = 0 then m else if t + 1 ≤ m then 2 * (m - t) else if t = m then 1 else 0

/-- At `M = 1` and `0 < D ≤ A`, the numerical graded rank bound equals `rowLayerOne m t`. -/
theorem rank_one_cap {D A m : ℕ} (hD : 0 < D) (hDA : D ≤ A) (t : ℕ) :
    firstOrderGradedRankBound D A m 1 t = rowLayerOne m t := by
  unfold firstOrderGradedRankBound rowLayerOne
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  by_cases ht0 : t = 0
  · subst ht0
    simp only [ite_true]
    calc
      _ = ∑ _s ∈ range m, 1 := by
            apply sum_congr rfl
            intro s hs
            have hsm := mem_range.mp hs
            have ha : s < m * A := lt_of_lt_of_le hsm (Nat.le_mul_of_pos_right m (by omega))
            simp [firstOrderGradedSourceCount, ha, show 1 ≤ m - s by omega]
      _ = m := by simp
  · simp only [ht0, ite_false]
    have hactive : ∀ s < m, t ≤ m → s + (D - 1) * t < m * A := by
      intro s hsm htm
      have h1 : (D - 1) * t ≤ (D - 1) * m := Nat.mul_le_mul_left _ htm
      have h2 : D * m ≤ A * m := Nat.mul_le_mul_right m hDA
      have h3 : (D - 1) * m + m = D * m := by
        have := congrArg (fun z : ℕ => z * m) (Nat.sub_add_cancel hD)
        nlinarith
      nlinarith
    by_cases htm : t + 1 ≤ m
    · simp only [htm, ite_true]
      have hsplit : ∑ s ∈ range m, min (m - s) (firstOrderGradedSourceCount D A m 1 s t) =
          ∑ s ∈ range m, if s + 1 < t then 0
            else if s + 1 = t then 1
            else if s + 1 = m then 1
            else 2 := by
        apply sum_congr rfl
        intro s hs
        have hsm := mem_range.mp hs
        have ha := hactive s hsm (by omega)
        simp only [firstOrderGradedSourceCount, ha, ite_true]
        split_ifs <;> omega
      rw [hsplit]
      have hzero : ∑ s ∈ range (t - 1),
          (if s + 1 < t then 0 else if s + 1 = t then 1 else if s + 1 = m then 1 else 2) = 0 := by
        apply sum_eq_zero
        intro s hs
        have := mem_range.mp hs
        simp [show s + 1 < t by omega]
      have hrange : range m = range (t - 1) ∪ Ico (t - 1) m := by
        ext s; simp only [mem_range, mem_union, mem_Ico]; omega
      rw [hrange, sum_union (by rw [disjoint_left]; intro s h1 h2; simp only [mem_range, mem_Ico] at h1 h2; omega),
        hzero, zero_add]
      have hfirst : t - 1 ∈ Ico (t - 1) m := mem_Ico.mpr ⟨le_rfl, by omega⟩
      have hlast : m - 1 ∈ (Ico (t - 1) m).erase (t - 1) :=
        mem_erase.mpr ⟨by omega, mem_Ico.mpr ⟨by omega, by omega⟩⟩
      rw [← add_sum_erase _ _ hfirst, ← add_sum_erase _ _ hlast]
      have hfval : (if (t - 1) + 1 < t then 0 else if (t - 1) + 1 = t then 1 else if (t - 1) + 1 = m then 1 else 2) = 1 := by
        split_ifs <;> omega
      have hlval : (if (m - 1) + 1 < t then 0 else if (m - 1) + 1 = t then 1 else if (m - 1) + 1 = m then 1 else 2) = 1 := by
        split_ifs <;> omega
      rw [hfval, hlval]
      have hmid : ∑ s ∈ ((Ico (t - 1) m).erase (t - 1)).erase (m - 1),
          (if s + 1 < t then 0 else if s + 1 = t then 1 else if s + 1 = m then 1 else 2) =
          ∑ _s ∈ ((Ico (t - 1) m).erase (t - 1)).erase (m - 1), 2 := by
        apply sum_congr rfl
        intro s hs
        simp only [mem_erase, mem_Ico] at hs
        split_ifs <;> omega
      rw [hmid, sum_const, smul_eq_mul, card_erase_of_mem hlast, card_erase_of_mem hfirst, Nat.card_Ico]
      omega
    · simp only [htm, ite_false]
      by_cases hteq : t = m
      · rcases hteq with rfl
        simp only [ite_true]
        have hlast : t - 1 ∈ range t := mem_range.mpr (by omega)
        rw [← add_sum_erase _ _ hlast]
        have hl : min (t - (t - 1)) (firstOrderGradedSourceCount D A t 1 (t - 1) t) = 1 := by
          have ha := hactive (t - 1) (by omega) le_rfl
          simp only [firstOrderGradedSourceCount, ha, ite_true]
          omega
        have hrest : ∑ s ∈ (range t).erase (t - 1),
            min (t - s) (firstOrderGradedSourceCount D A t 1 s t) = 0 := by
          apply sum_eq_zero
          intro s hs
          simp only [mem_erase, mem_range] at hs
          simp only [firstOrderGradedSourceCount]
          split_ifs <;> omega
        rw [hl, hrest, add_zero]
      · simp only [hteq, ite_false]
        apply sum_eq_zero
        intro s hs
        have hsm := mem_range.mp hs
        simp only [firstOrderGradedSourceCount]
        split_ifs <;> omega

private theorem rowLayerOne_sum_le {m T : ℕ} (hT : 1 ≤ T) (hTm : T ≤ m) :
    ∑ t ∈ range T, rowLayerOne m t + T * (T - 1) = (2 * T - 1) * m := by
  induction T with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simp [rowLayerOne]
    | succ j =>
      have hj := ih (by omega) (by omega)
      rw [sum_range_succ]
      have hlayer : rowLayerOne m (j + 1) = 2 * (m - (j + 1)) := by
        unfold rowLayerOne
        simp [show j + 1 < m by omega]
      rw [hlayer]
      have hsub : j + 1 ≤ m := by omega
      zify [hsub, show 1 ≤ 2 * (j + 1) by omega, show 1 ≤ 2 * (j + 1 + 1) by omega,
        show 1 ≤ j + 1 by omega, show 1 ≤ j + 1 + 1 by omega] at hj ⊢
      nlinarith

private theorem rowLayerOne_sum_full {m T : ℕ} (hm : 0 < m) (hT : m + 1 ≤ T) :
    ∑ t ∈ range T, rowLayerOne m t = m ^ 2 + 1 := by
  have hcut : ∑ t ∈ range T, rowLayerOne m t = ∑ t ∈ range (m + 1), rowLayerOne m t := by
    symm
    apply sum_subset (range_mono hT)
    intro t ht hnot
    simp only [mem_range] at ht hnot
    unfold rowLayerOne
    simp [show t ≠ 0 by omega, show ¬ t < m by omega, show t ≠ m by omega]
  rw [hcut, sum_range_succ]
  have hm_sum := rowLayerOne_sum_le (m := m) (T := m) hm le_rfl
  have hlast : rowLayerOne m m = 1 := by
    unfold rowLayerOne
    simp [show m ≠ 0 by omega]
  rw [hlast]
  zify [hm, show 1 ≤ 2 * m by omega] at hm_sum ⊢
  nlinarith

/-- Source column layer at `M = 1` and total jet degree `t`. -/
def colLayerOne (D A m t : ℕ) : ℕ :=
  ∑ b ∈ range (min t 1 + 1), (m * A + b - D * t)

private theorem colLayerOne_zero (D A m : ℕ) : colLayerOne D A m 0 = m * A := by
  simp [colLayerOne]

private theorem colLayerOne_succ (D A m t : ℕ) :
    colLayerOne D A m (t + 1) = (m * A - D * (t + 1)) + (m * A + 1 - D * (t + 1)) := by
  simp [colLayerOne, sum_range_succ]

private def ramp (x d T : ℕ) : ℕ := ∑ t ∈ range T, (x - d * t)

private theorem ramp_id (x d T : ℕ) (h : ∀ t < T, d * t ≤ x) :
    2 * ramp x d T + d * T * T = 2 * T * x + d * T := by
  induction T with
  | zero => simp [ramp]
  | succ T ih =>
    have hi := ih (fun t ht => h t (by omega))
    have hc := Nat.sub_add_cancel (h T (by omega))
    have hs : ramp x d (T + 1) = ramp x d T + (x - d * T) := sum_range_succ ..
    rw [hs]
    nlinarith

private theorem ramp_stable {x d s t : ℕ} (hst : s ≤ t) (hstop : x ≤ d * s) :
    ramp x d t = ramp x d s := by
  symm
  apply sum_subset_zero_on_sdiff (range_mono hst)
  · intro i hi
    have hi : s ≤ i := by simpa using (mem_sdiff.mp hi).2
    exact Nat.sub_eq_zero_of_le (hstop.trans (Nat.mul_le_mul_left _ hi))
  · simp

private theorem ramp_upper_cut {x d T : ℕ} (hd : 0 < d) :
    ramp x d T ≤ ramp x d (x / d + 1) := by
  rcases le_total T (x / d + 1) with hs | hs
  · exact sum_le_sum_of_subset_of_nonneg (range_mono hs) (by intros; omega)
  · exact (ramp_stable hs (Nat.lt_mul_div_succ x hd).le).le

private theorem ramp_integral (x D u r : ℕ) (hx : x = D * u + r) (hr : r < D) :
    2 * D * ramp x D (u + 1) = x ^ 2 + D * x + r * (D - r) := by
  subst x
  have h := ramp_id (D * u + r) D (u + 1) (fun t ht =>
    (Nat.mul_le_mul_left D (show t ≤ u by omega)).trans (by omega))
  have hmul := congrArg (fun v : ℕ => D * v) h
  have hrem := congrArg (fun v : ℕ => r * v) (Nat.sub_add_cancel hr.le)
  nlinarith

private theorem four_mul_rem_le_sq {r D : ℕ} (hr : r ≤ D) : 4 * (r * (D - r)) ≤ D ^ 2 := by
  zify [hr]
  nlinarith [sq_nonneg ((D : ℤ) - 2 * r)]

private theorem four_D_ramp_le {x D T : ℕ} (hD : 0 < D) :
    4 * D * ramp x D T ≤ 2 * x ^ 2 + 2 * D * x + D ^ 2 := by
  let u := x / D
  let r := x % D
  have hmod : x = D * u + r := by simpa [u, r, Nat.add_comm] using (Nat.mod_add_div x D).symm
  have hr : r < D := Nat.mod_lt _ hD
  have hcut := Nat.mul_le_mul_left (4 * D) (ramp_upper_cut (x := x) (T := T) hD)
  have hint := ramp_integral x D u r hmod hr
  have hrem := four_mul_rem_le_sq hr.le
  calc
    4 * D * ramp x D T ≤ 4 * D * ramp x D (u + 1) := hcut
    _ = 2 * (2 * D * ramp x D (u + 1)) := by ring
    _ = 2 * (x ^ 2 + D * x + r * (D - r)) := by rw [hint]
    _ ≤ 2 * x ^ 2 + 2 * D * x + D ^ 2 := by nlinarith

private theorem colLayerOne_sum_split (D A m T : ℕ) :
    ∑ t ∈ range (T + 1), colLayerOne D A m t =
      ramp (m * A) D (T + 1) + ramp (m * A + 1 - D) D T := by
  induction T with
  | zero => simp [colLayerOne_zero, ramp]
  | succ k ih =>
    rw [sum_range_succ, ih, colLayerOne_succ]
    have hr1 : ramp (m * A) D (k + 2) = ramp (m * A) D (k + 1) + (m * A - D * (k + 1)) :=
      sum_range_succ ..
    have hr2 : ramp (m * A + 1 - D) D (k + 1) =
        ramp (m * A + 1 - D) D k + (m * A + 1 - D - D * k) :=
      sum_range_succ ..
    have heq : m * A + 1 - D - D * k = m * A + 1 - D * (k + 1) := by
      rw [Nat.sub_sub, show D + D * k = D * (k + 1) by ring]
    rw [hr1, hr2, heq]
    ring

private theorem colLayerOne_sum_le_m {D A m T : ℕ} (hDA : D ≤ A) (hT : 1 ≤ T) (hTm : T ≤ m) :
    ∑ t ∈ range T, colLayerOne D A m t + D * T * (T - 1) = (2 * T - 1) * (m * A) + (T - 1) := by
  induction T with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simp [colLayerOne_zero]
    | succ j =>
      have hj := ih (by omega) (by omega)
      rw [sum_range_succ, colLayerOne_succ]
      have hle : D * (j + 1) ≤ m * A :=
        (Nat.mul_le_mul hDA (by omega : j + 1 ≤ m)).trans_eq (Nat.mul_comm ..)
      have hle' : D * (j + 1) ≤ m * A + 1 := hle.trans (Nat.le_succ _)
      zify [hle, hle', show 1 ≤ 2 * (j + 1) by omega, show 1 ≤ 2 * (j + 1 + 1) by omega,
        show 1 ≤ j + 1 by omega, show 1 ≤ j + 1 + 1 by omega] at hj ⊢
      nlinarith

/-- Every prefix of the `M = 1` first-order column profile is dominated by the
corresponding prefix of the row profile throughout the strictly beyond-Johnson
region `A² < n D`. -/
theorem prefix_bound_cap_one {n D A m : ℕ} (hD : 0 < D) (hDA : D ≤ A) (hAn : A ≤ n)
    (hJ : A ^ 2 < n * D) (T : ℕ) :
    ∑ t ∈ range T, colLayerOne D A m t ≤ ∑ t ∈ range T, n * rowLayerOne m t := by
  rw [← mul_sum]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hzero : ∑ t ∈ range T, colLayerOne D A 0 t = 0 := by
      apply sum_eq_zero
      intro t _
      unfold colLayerOne
      apply sum_eq_zero
      intro b hb
      simp only [mem_range] at hb
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · omega
      · have : 1 ≤ D * t := Nat.mul_pos hD ht
        omega
    rw [hzero]
    exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  by_cases hTm : T ≤ m
  · have hcol := colLayerOne_sum_le_m hDA hT hTm
    have hrow := rowLayerOne_sum_le hT hTm
    have hmean : 2 * A + 1 ≤ n + D := by
      by_contra! hh
      have h1 : (n + D : ℤ) ≤ 2 * A := by omega
      have h2 : ((n : ℤ) - D) ^ 2 ≥ 0 := sq_nonneg _
      have h3 : (A : ℤ) ^ 2 < n * D := by exact_mod_cast hJ
      nlinarith
    have hnd : D ≤ n := hDA.trans hAn
    zify [hT, hTm, hAn, hnd, show 1 ≤ 2 * T by omega] at hcol hrow hmean ⊢
    have hmul := congrArg (fun z : ℤ => (n : ℤ) * z) hrow
    have h1 : 0 ≤ ((2 * (T : ℤ) - 1) * ((m : ℤ) - T)) * ((n : ℤ) - A) :=
      mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
    have h2 : 0 ≤ ((T : ℤ) - 1) * ((T : ℤ) - 1) := mul_self_nonneg _
    have h3 : 0 ≤ (T : ℤ) * ((n : ℤ) - A) := mul_nonneg (by omega) (by omega)
    nlinarith
  · have hTm' : m + 1 ≤ T := by omega
    rw [rowLayerOne_sum_full hm hTm']
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hT.ne'
    rw [colLayerOne_sum_split]
    have h1 := four_D_ramp_le (x := m * A) (T := k + 1) hD
    have h2 := four_D_ramp_le (x := m * A + 1 - D) (T := k) hD
    have hDmA : D ≤ m * A := hDA.trans (Nat.le_mul_of_pos_left A hm)
    have hsub : m * A + 1 - D + D = m * A + 1 := by omega
    have hsum : 4 * D * (ramp (m * A) D (k + 1) + ramp (m * A + 1 - D) D k) + 2 * D ≤
        4 * (m * A) ^ 2 + 4 * (m * A) + 2 + 2 * D ^ 2 := by
      zify at h1 h2 hsub ⊢
      nlinarith
    have hgoal : 4 * (m * A) ^ 2 + 4 * (m * A) + 2 + 2 * D ^ 2 ≤
        4 * D * (n * (m ^ 2 + 1)) + 2 * D := by
      zify at hJ hDA hD ⊢
      have hsq : (D : ℤ) ^ 2 ≤ A ^ 2 := by nlinarith
      have hgap : (1 : ℤ) ≤ n * D - A ^ 2 := by omega
      have hm2 : (4 : ℤ) * (m : ℤ) ^ 2 ≤ 4 * (m : ℤ) ^ 2 * ((n : ℤ) * D - A ^ 2) := by
        nlinarith [sq_nonneg (m : ℤ)]
      nlinarith [sq_nonneg (2 * (m : ℤ) - A)]
    have hcomb : 4 * D * (ramp (m * A) D (k + 1) + ramp (m * A + 1 - D) D k) ≤
        4 * D * (n * (m ^ 2 + 1)) := by omega
    exact Nat.le_of_mul_le_mul_left hcomb (by omega)

/-- Strictly beyond Johnson (`A² < n D`), no choice of multiplicity `m`, total jet
degree `μ`, challenge weight `ℓ`, or height `h` gives a shifted first-order slot
surplus with derivative cap `M = 1`. -/
theorem no_surplus_cap_one {n D A m : ℕ} (hD : 0 < D) (hDA : D ≤ A) (hAn : A ≤ n)
    (hJ : A ^ 2 < n * D) (μ ℓ h : ℕ) :
    firstOrderCurveShiftedHeightSlotCount D A m 1 μ ℓ h ≤
      firstOrderCurveShiftedRowSlotBound D A m 1 μ n ℓ h := by
  have hcol : firstOrderCurveShiftedHeightSlotCount D A m 1 μ ℓ h =
      ∑ t ∈ range (μ + 1), colLayerOne D A m t * (h + 1 - ℓ * t) := by
    unfold firstOrderCurveShiftedHeightSlotCount colLayerOne
    apply sum_congr rfl
    intro t _
    rw [sum_mul]
  have hrow : firstOrderCurveShiftedRowSlotBound D A m 1 μ n ℓ h =
      ∑ t ∈ range (μ + 1), (n * rowLayerOne m t) * (h + 1 - ℓ * t) := by
    unfold firstOrderCurveShiftedRowSlotBound
    apply sum_congr rfl
    intro t _
    rw [rank_one_cap hD hDA]
  rw [hcol, hrow]
  let f (t : ℕ) : ℤ := (colLayerOne D A m t : ℕ)
  let c (t : ℕ) : ℤ := (n * rowLayerOne m t : ℕ)
  let w (t : ℕ) : ℤ := (h + 1 - ℓ * t : ℕ)
  have hw : 0 ≤ w := fun _ => Int.natCast_nonneg _
  have ha : AntitoneOn w (Set.Iio (μ + 1)) := by
    intro i _ j _ hij
    dsimp [w]
    exact_mod_cast Nat.sub_le_sub_left (Nat.mul_le_mul_left ℓ hij) (h + 1)
  have hb := Finset.sum_mul_le_sum_mul_of_sum_range_le (f := f) (c := c)
    (fun T _ => (by dsimp [f, c]; exact_mod_cast prefix_bound_cap_one hD hDA hAn hJ (m := m) T))
    hw ha
  dsimp [f, c, w] at hb
  exact_mod_cast hb

private theorem surplus_height (c r : ℕ → ℕ) (ℓ μ : ℕ)
    (hs : (∑ i ∈ range (μ + 1), r i) < ∑ i ∈ range (μ + 1), c i) :
    ∃ h : ℕ, (∑ i ∈ range (μ + 1), r i * (h + 1 - ℓ * i)) <
      ∑ i ∈ range (μ + 1), c i * (h + 1 - ℓ * i) := by
  let R := ∑ i ∈ range (μ + 1), r i
  let C := ∑ i ∈ range (μ + 1), c i
  have hRC : R + 1 ≤ C := hs
  let h := ℓ * μ * C
  have hbase : ℓ * μ ≤ h + 1 := (Nat.le_mul_of_pos_right _ (show 0 < C by omega)).trans (by omega)
  refine ⟨h, ?_⟩
  calc _ ≤ R * (h + 1) := by
         dsimp [R]
         rw [sum_mul]
         exact sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.sub_le ..)
    _ < C * (h + 1 - ℓ * μ) := by
         have hd := congrArg (fun a : ℕ => C * a) (Nat.sub_add_cancel hbase)
         have hscaled := Nat.mul_le_mul_right (h + 1) hRC
         have he : h = ℓ * μ * C := rfl
         nlinarith
    _ ≤ _ := by
         dsimp [C]
         rw [sum_mul]
         apply sum_le_sum
         intro i hi
         exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_left
           (Nat.mul_le_mul_left ℓ (Nat.le_of_lt_succ (mem_range.mp hi))) _)

/-- **Exact `M = 1` boundary characterization.** A linear-in-`Y₁` shifted first-order
interpolation certificate achieves a strict slot surplus at some finite multiplicity,
jet degree, and height if and only if `n D ≤ A²` (at or below the Johnson radius).
Unlike `M = 0` (`n D < A²`), `M = 1` includes the exact Johnson equality line `A² = n D`
via the weight drop `wt(Y₁) = D - 1`, but still cannot cross strictly beyond Johnson. -/
theorem cap_one_exact {n D A : ℕ} (hD : 0 < D) (hDA : D ≤ A) (hAn : A ≤ n) (ℓ : ℕ) :
    (∃ (m μ h : ℕ), 0 < m ∧ firstOrderCurveShiftedRowSlotBound D A m 1 μ n ℓ h <
      firstOrderCurveShiftedHeightSlotCount D A m 1 μ ℓ h) ↔ n * D ≤ A ^ 2 := by
  constructor
  · rintro ⟨m, μ, h, _, hs⟩
    exact le_of_not_gt fun hj => (not_lt_of_ge (no_surplus_cap_one hD hDA hAn hj μ ℓ h)) hs
  · intro hJ
    let m := D * (A + 1)
    let u := A * (A + 1)
    let μ := u
    have hm : 0 < m := by dsimp [m]; positivity
    have hApos : 0 < A := lt_of_lt_of_le hD hDA
    have hmμ : m ≤ μ := Nat.mul_le_mul_right (A + 1) hDA
    have hma : m * A = D * u := by dsimp [m, u]; ring
    have hr0 : 2 * ramp (m * A) D (u + 1) + D * (u + 1) * (u + 1) =
        2 * (u + 1) * (m * A) + D * (u + 1) :=
      ramp_id (m * A) D (u + 1) (fun t ht => by
        rw [hma]; exact Nat.mul_le_mul_left D (by omega))
    have hDmA : D ≤ m * A := hDA.trans (Nat.le_mul_of_pos_left A hm)
    have hr1 : 2 * ramp (m * A + 1 - D) D u + D * u * u =
        2 * u * (m * A + 1 - D) + D * u :=
      ramp_id (m * A + 1 - D) D u (fun t ht => by
        have h1 : D * t + D ≤ D * u := by
          have : t + 1 ≤ u := ht
          nlinarith
        omega)
    have hcol_sum : ∑ t ∈ range (μ + 1), colLayerOne D A m t = D * u ^ 2 + u := by
      rw [colLayerOne_sum_split]
      have hsub : m * A + 1 - D + D = m * A + 1 := by omega
      have h2 := congrArg (fun z : ℕ => 2 * u * z) hsub
      nlinarith
    have hrow_sum : ∑ t ∈ range (μ + 1), n * rowLayerOne m t = n * (m ^ 2 + 1) := by
      rw [← mul_sum, rowLayerOne_sum_full hm (by omega)]
    have hcrit : (∑ t ∈ range (μ + 1), n * rowLayerOne m t) <
        ∑ t ∈ range (μ + 1), colLayerOne D A m t := by
      rw [hrow_sum, hcol_sum]
      have h1 : n * m ^ 2 ≤ D * u ^ 2 := by
        have hm2 : m ^ 2 = D ^ 2 * (A + 1) ^ 2 := by dsimp [m]; ring
        have hu2 : D * u ^ 2 = D * A ^ 2 * (A + 1) ^ 2 := by dsimp [u]; ring
        rw [hm2, hu2]
        have hmul := Nat.mul_le_mul_right ((A + 1) ^ 2) (Nat.mul_le_mul_left D hJ)
        nlinarith
      have h2 : n < u := by
        have : n ≤ n * D := Nat.le_mul_of_pos_right n hD
        dsimp [u]
        nlinarith
      nlinarith
    obtain ⟨h, hh⟩ := surplus_height (fun t => colLayerOne D A m t)
      (fun t => n * rowLayerOne m t) ℓ μ hcrit
    refine ⟨m, μ, h, hm, ?_⟩
    have hcol_eq : firstOrderCurveShiftedHeightSlotCount D A m 1 μ ℓ h =
        ∑ t ∈ range (μ + 1), colLayerOne D A m t * (h + 1 - ℓ * t) := by
      unfold firstOrderCurveShiftedHeightSlotCount colLayerOne
      apply sum_congr rfl; intro t _; rw [sum_mul]
    have hrow_eq : firstOrderCurveShiftedRowSlotBound D A m 1 μ n ℓ h =
        ∑ t ∈ range (μ + 1), (n * rowLayerOne m t) * (h + 1 - ℓ * t) := by
      unfold firstOrderCurveShiftedRowSlotBound
      apply sum_congr rfl; intro t _; rw [rank_one_cap hD hDA]
    rw [hcol_eq, hrow_eq]
    exact hh

/-- Every passing shifted first-order slot certificate strictly beyond Johnson (`A² < n D`)
must have first-derivative cap at least `2` (nonlinear in `Y₁`) and total jet degree at
least `2`. This rules out all linear-in-`Y₁` (including linear and Riccati) ODE
interpolants beyond Johnson. -/
theorem two_le_cap_of_beyond_johnson {n D A m M μ ℓ h : ℕ}
    (hD : 0 < D) (hDA : D < A) (hAn : A ≤ n) (hJ : A ^ 2 < n * D)
    (hs : firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h <
      firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h) :
    2 ≤ M ∧ 2 ≤ μ := by
  have hM : 2 ≤ M := by
    by_contra! hsmall
    interval_cases M
    · exact (not_lt_of_ge (FirstOrderZeroCapJohnson.no_surplus hD hDA.le hAn hJ.le μ ℓ h)) hs
    · exact (not_lt_of_ge (no_surplus_cap_one hD hDA.le hAn hJ μ ℓ h)) hs
  have hm : 0 < m := by
    by_contra! hz
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hz
    subst hm0
    have hzero : firstOrderCurveShiftedHeightSlotCount D A 0 M μ ℓ h = 0 := by
      unfold firstOrderCurveShiftedHeightSlotCount
      apply sum_eq_zero; intro t _
      apply sum_eq_zero; intro b hb
      have hbt := (Nat.le_of_lt_succ (mem_range.mp hb)).trans (min_le_left ..)
      have hbd := hbt.trans (Nat.le_mul_of_pos_left t hD)
      simp [Nat.sub_eq_zero_of_le hbd]
    omega
  exact ⟨hM, FirstOrderDegreeOneBoundary.two_le_degree_of_beyond_johnson hDA hAn hm (by omega) hJ hs⟩

#print axioms rank_one_cap
#print axioms prefix_bound_cap_one
#print axioms no_surplus_cap_one
#print axioms cap_one_exact
#print axioms two_le_cap_of_beyond_johnson
end ProximityGap.DrdosCapOneBarrier
