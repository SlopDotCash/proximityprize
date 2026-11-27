/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CubicHahnJohnson

/-!
# Sharpened Hahn–Hint Boundary-Shell Theorem (`P₁` Hint Variance Boost + `P₂, P₃`)

Combining `CubicHahnJohnson` (`P₁, P₂, P₃`) with a single hint set `H_set` of size `H`
intersecting every other agreement set `S i` in at most `d` coordinates strictly boosts
the degree-1 Hahn sum from `0` to the exact positive floor:
`∑_{i,j} P₁(n, t, |S i ∩ S j|) ≥ m² * (H * t - n * d)² / (n * H * (n - H))`
(whenever `n * d ≤ H * t`).

This directly strengthens both `quadratic_hahn_block_bound` (by `+ quadC1 * p1Boost`) and
`cubic_hahn_block_bound` (by `+ cubicC1 * p1Boost`), strictly tightening the second-prime
(`B₂ = 2³¹`) boundary-shell exclusion across ALL FOUR Proximity Prize rates over the
degree-1 `HintBoundaryShell` bounds:
- Rate `1/2` (`J+1`, `B₂`): `< 759,263,558` (`A_J + 13,433` vs `+15,050`, `1.12×` tighter).
- Rate `1/4` (`J+1`, `B₂`): `< 536,903,681` (`A_J + 32,770` vs `+34,757`, `1.06×` tighter).
- Rate `1/8` (`J+2`, `B₂`): `< 379,661,358` (`A_J + 36,296` vs `+41,565`, `1.15×` tighter, pure deg-2 Hahn).
- Rate `1/16` (`J+1`, `B₂`): `< 268,467,184` (`A_J + 31,730` vs `+43,737`, `1.38×` tighter, pure deg-2 Hahn).
-/

set_option autoImplicit false

namespace ProximityGap.CubicHintBoundaryShell

open Finset Code InterleavedListJohnsonRank CubicHahnJohnson
open scoped BigOperators

section HahnHintBoost

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The exact degree-1 Hahn variance boost supplied by a hint set of size `H`
with pairwise intersection cap `d` (`n * d ≤ H * t`). -/
def p1HintBoost (n t d H : ℚ) : ℚ :=
  (H * t - n * d) ^ 2 / (n * H * (n - H))

private theorem sq_sum_le_card_mul_sum_sq_rat {α : Type*} (U : Finset α) (f : α → ℚ) :
    (∑ x ∈ U, f x) ^ 2 ≤ (U.card : ℚ) * ∑ x ∈ U, f x ^ 2 := by
  let S : ℚ := ∑ x ∈ U, f x
  have hnn : 0 ≤ ∑ x ∈ U, ((U.card : ℚ) * f x - S) ^ 2 :=
    Finset.sum_nonneg fun x _ => sq_nonneg _
  have hexp : ∑ x ∈ U, ((U.card : ℚ) * f x - S) ^ 2 =
      (U.card : ℚ) * ((U.card : ℚ) * (∑ x ∈ U, f x ^ 2) - S ^ 2) := by
    have hterm (x : α) : ((U.card : ℚ) * f x - S) ^ 2 =
        (U.card : ℚ) ^ 2 * f x ^ 2 - 2 * (U.card : ℚ) * S * f x + S ^ 2 := by ring
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
    change (U.card : ℚ) ^ 2 * (∑ x ∈ U, f x ^ 2) - 2 * (U.card : ℚ) * S * S +
      (U.card : ℚ) * S ^ 2 = _
    ring
  rw [hexp] at hnn
  rcases Nat.eq_zero_or_pos U.card with h0 | hpos
  · have hU : U = ∅ := card_eq_zero.mp h0
    simp [hU]
  · have hposQ : (0 : ℚ) < U.card := by exact_mod_cast hpos
    have : 0 ≤ (U.card : ℚ) * (∑ x ∈ U, f x ^ 2) - S ^ 2 :=
      nonneg_of_mul_nonneg_right hnn hposQ
    linarith

/-- Lower bound on the degree-1 Hahn sum in the presence of a hint set `H_set` of size `H`
with `|S i ∩ H_set| ≤ d` and `n * d ≤ H * t`. -/
theorem sum_P1_hint_lower {m t d H : ℕ} (H_set : Finset I) (S : Fin m → Finset I)
    (hH : H_set.card = H) (hHpos : 0 < H) (hHlt : H < Fintype.card I)
    (hw : ∀ i, (S i).card = t) (hhint : ∀ i, (S i ∩ H_set).card ≤ d)
    (hHt : Fintype.card I * d ≤ H * t) :
    (m : ℚ) ^ 2 * p1HintBoost (Fintype.card I) t d H ≤
      ∑ i : Fin m, ∑ j : Fin m, P1 (Fintype.card I) t ((S i ∩ S j).card) := by
  let n : ℚ := Fintype.card I
  have hHposQ : (0 : ℚ) < H := by exact_mod_cast hHpos
  have hHltQ : (H : ℚ) < n := by dsimp [n]; exact_mod_cast hHlt
  have hnH : (0 : ℚ) < n - H := by linarith
  have hn0 : (0 : ℚ) < n := by linarith
  let deg (x : I) : ℚ := ∑ i : Fin m, if x ∈ S i then 1 else 0
  have hsum_all : ∑ x : I, deg x = (m : ℚ) * t := by
    unfold deg; rw [Finset.sum_comm]; simp [hw]
  have hsq_all : ∑ x : I, deg x ^ 2 = ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) := by
    simp_rw [deg, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hterm (x : I) :
        (if x ∈ S i then (1 : ℚ) else 0) * (if x ∈ S j then 1 else 0) =
          if x ∈ S i ∩ S j then 1 else 0 := by
      by_cases hi : x ∈ S i <;> by_cases hj : x ∈ S j <;> simp [hi, hj]
    simp_rw [hterm]
    simp only [Finset.sum_boole]
    have : (Finset.univ.filter fun x => x ∈ S i ∩ S j) = S i ∩ S j := by ext x; simp
    rw [this]
  have hP1_eq : ∑ i : Fin m, ∑ j : Fin m, P1 n t ((S i ∩ S j).card) =
      (∑ x : I, deg x ^ 2) - (m : ℚ) ^ 2 * t ^ 2 / n := by
    simp only [P1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← hsq_all]
    ring
  let A : ℚ := ∑ x ∈ H_set, deg x
  let B : ℚ := ∑ x ∈ H_setᶜ, deg x
  have hAB : A + B = (m : ℚ) * t := by dsimp [A, B]; rw [Finset.sum_add_sum_compl, hsum_all]
  have hAle : A ≤ (m : ℚ) * d := by
    have hAeq : A = ∑ i : Fin m, ((S i ∩ H_set).card : ℚ) := by
      dsimp [A, deg]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_filter]
      have hfilt : H_set.filter (· ∈ S i) = S i ∩ H_set := by ext x; simp [and_comm]
      simp [hfilt]
    rw [hAeq]
    calc
      ∑ i : Fin m, ((S i ∩ H_set).card : ℚ)
        ≤ ∑ _i : Fin m, (d : ℚ) := Finset.sum_le_sum fun i _ => by exact_mod_cast hhint i
      _ = (m : ℚ) * d := by simp
  have hcs1 : A ^ 2 / H ≤ ∑ x ∈ H_set, deg x ^ 2 := by
    rw [div_le_iff₀ hHposQ, mul_comm]
    simpa [hH] using sq_sum_le_card_mul_sum_sq_rat H_set deg
  have hHccard : ((H_setᶜ).card : ℚ) = n - H := by
    rw [Finset.card_compl, hH, Nat.cast_sub hHlt.le]
  have hcs2 : B ^ 2 / (n - H) ≤ ∑ x ∈ H_setᶜ, deg x ^ 2 := by
    rw [div_le_iff₀ hnH, mul_comm]
    simpa [hHccard] using sq_sum_le_card_mul_sum_sq_rat H_setᶜ deg
  have hsum_sq : A ^ 2 / H + B ^ 2 / (n - H) ≤ ∑ x : I, deg x ^ 2 := by
    rw [← Finset.sum_add_sum_compl H_set (fun x => deg x ^ 2)]
    exact add_le_add hcs1 hcs2
  have hB_eq : B = (m : ℚ) * t - A := by linarith
  have hid : A ^ 2 / H + B ^ 2 / (n - H) - (m : ℚ) ^ 2 * t ^ 2 / n =
      ((m : ℚ) * t * H - n * A) ^ 2 / (n * H * (n - H)) := by
    rw [hB_eq]; field_simp [hn0.ne', hHposQ.ne', hnH.ne']; ring
  have hHtQ : n * d ≤ (H : ℚ) * t := by dsimp [n]; exact_mod_cast hHt
  have hgap_ge : (m : ℚ) * ((H : ℚ) * t - n * d) ≤ (m : ℚ) * t * H - n * A := by nlinarith
  have hgap_nn : 0 ≤ (m : ℚ) * ((H : ℚ) * t - n * d) :=
    mul_nonneg (Nat.cast_nonneg m) (by linarith)
  have hsq_ge : ((m : ℚ) * ((H : ℚ) * t - n * d)) ^ 2 ≤ ((m : ℚ) * t * H - n * A) ^ 2 := by
    nlinarith
  have hdiv_ge : (m : ℚ) ^ 2 * p1HintBoost n t d H ≤
      ((m : ℚ) * t * H - n * A) ^ 2 / (n * H * (n - H)) := by
    unfold p1HintBoost
    have hden : 0 < n * H * (n - H) := by positivity
    rw [show (m : ℚ) ^ 2 * (((H : ℚ) * t - n * d) ^ 2 / (n * H * (n - H))) =
        ((m : ℚ) * ((H : ℚ) * t - n * d)) ^ 2 / (n * H * (n - H)) by ring]
    exact div_le_div_of_nonneg_right hsq_ge hden.le
  change (m : ℚ) ^ 2 * p1HintBoost n t d H ≤ ∑ i : Fin m, ∑ j : Fin m, P1 n t ((S i ∩ S j).card)
  rw [hP1_eq]
  linarith

/-- Quadratic Hahn block bound boosted by a single hint set `H_set`. -/
theorem quadratic_hahn_block_bound_with_hint {m t d H : ℕ} (H_set : Finset I) (S : Fin m → Finset I)
    (hn : 3 ≤ Fintype.card I) (hH : H_set.card = H) (hHpos : 0 < H) (hHlt : H < Fintype.card I)
    (hdt : d ≤ t) (hw : ∀ i, (S i).card = t)
    (hpair : Pairwise fun i j => (S i ∩ S j).card ≤ d)
    (hhint : ∀ i, (S i ∩ H_set).card ≤ d) (hHt : Fintype.card I * d ≤ H * t)
    (hc1 : 0 ≤ quadC1 (Fintype.card I) t d) :
    (m : ℚ) * (quadC0 (Fintype.card I) t d +
        quadC1 (Fintype.card I) t d * p1HintBoost (Fintype.card I) t d H) ≤
      (t : ℚ) * ((t : ℚ) - d) := by
  by_cases hm : m = 0
  · subst hm
    have hdt' : (d : ℚ) ≤ t := by exact_mod_cast hdt
    simpa using mul_nonneg (Nat.cast_nonneg t) (by linarith : 0 ≤ (t : ℚ) - d)
  · set n : ℚ := (Fintype.card I : ℚ)
    have hn_ge : (3 : ℚ) ≤ n := by dsimp [n]; exact_mod_cast hn
    have hn0 : n ≠ 0 := by linarith
    have hn1 : n - 1 ≠ 0 := by linarith
    have hn2 : n - 2 ≠ 0 := by linarith
    have hP1 : (m : ℚ) ^ 2 * p1HintBoost n t d H ≤
        ∑ i : Fin m, ∑ j : Fin m, P1 n t ((S i ∩ S j).card) :=
      sum_P1_hint_lower H_set S hH hHpos hHlt hw hhint hHt
    have hP2 : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, P2 n t ((S i ∩ S j).card) :=
      sum_P2_nonneg S hn hw
    have hid : ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - d) =
        (m : ℚ) ^ 2 * quadC0 n t d +
        quadC1 n t d * (∑ i : Fin m, ∑ j : Fin m, P1 n t ((S i ∩ S j).card)) +
        2 * (∑ i : Fin m, ∑ j : Fin m, P2 n t ((S i ∩ S j).card)) := by
      simp_rw [quad_poly_eq n t d _ hn0 hn1 hn2, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hlow : (m : ℚ) ^ 2 * (quadC0 n t d + quadC1 n t d * p1HintBoost n t d H) ≤
        ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - d) := by
      rw [hid]
      have hmul : quadC1 n t d * ((m : ℚ) ^ 2 * p1HintBoost n t d H) ≤
          quadC1 n t d * (∑ i : Fin m, ∑ j : Fin m, P1 n t ((S i ∩ S j).card)) :=
        mul_le_mul_of_nonneg_left hP1 hc1
      have hP2_nn : 0 ≤ 2 * (∑ i : Fin m, ∑ j : Fin m, P2 n t ((S i ∩ S j).card)) :=
        mul_nonneg (by norm_num) hP2
      have hstep1 : (m : ℚ) ^ 2 * quadC0 n t d + quadC1 n t d * ((m : ℚ) ^ 2 * p1HintBoost n t d H) ≤
          (m : ℚ) ^ 2 * quadC0 n t d +
            quadC1 n t d * (∑ i : Fin m, ∑ j : Fin m, P1 n t ((S i ∩ S j).card)) :=
        add_le_add (le_refl _) hmul
      have hstep2 : (m : ℚ) ^ 2 * quadC0 n t d +
            quadC1 n t d * ((m : ℚ) ^ 2 * p1HintBoost n t d H) + 0 ≤
          (m : ℚ) ^ 2 * quadC0 n t d +
            quadC1 n t d * (∑ i : Fin m, ∑ j : Fin m, P1 n t ((S i ∩ S j).card)) +
            2 * (∑ i : Fin m, ∑ j : Fin m, P2 n t ((S i ∩ S j).card)) :=
        add_le_add hstep1 hP2_nn
      have hring : (m : ℚ) ^ 2 * (quadC0 n t d + quadC1 n t d * p1HintBoost n t d H) =
          (m : ℚ) ^ 2 * quadC0 n t d +
            quadC1 n t d * ((m : ℚ) ^ 2 * p1HintBoost n t d H) + 0 := by ring
      rw [hring]
      exact hstep2
    have hhi : ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - d) ≤
        (m : ℚ) * ((t : ℚ) * ((t : ℚ) - d)) := by
      have hrow (i : Fin m) :
          ∑ j : Fin m, ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - d) ≤
            (t : ℚ) * ((t : ℚ) - d) := by
        rw [← Finset.add_sum_erase univ _ (mem_univ i), inter_self, hw i]
        have hoff : ∑ j ∈ univ.erase i,
            ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - d) ≤ 0 := by
          refine Finset.sum_nonpos fun j hj => ?_
          have hle : ((S i ∩ S j).card : ℚ) ≤ d := by
            exact_mod_cast hpair (mem_erase.mp hj).1.symm
          exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
        linarith
      calc
        _ ≤ ∑ _i : Fin m, ((t : ℚ) * ((t : ℚ) - d)) := Finset.sum_le_sum fun i _ => hrow i
        _ = _ := by simp
    have hmpos : (0 : ℚ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
    have htot : (m : ℚ) * ((m : ℚ) * (quadC0 n t d + quadC1 n t d * p1HintBoost n t d H)) ≤
        (m : ℚ) * ((t : ℚ) * ((t : ℚ) - d)) := by
      have hsq : (m : ℚ) * ((m : ℚ) * (quadC0 n t d + quadC1 n t d * p1HintBoost n t d H)) =
          (m : ℚ) ^ 2 * (quadC0 n t d + quadC1 n t d * p1HintBoost n t d H) := by ring
      rw [hsq]
      exact hlow.trans hhi
    exact le_of_mul_le_mul_left htot hmpos

/-- Cubic Hahn block bound boosted by a single hint set `H_set`. -/
theorem cubic_hahn_block_bound_with_hint {m t d H : ℕ} (H_set : Finset I) (S : Fin m → Finset I)
    (hn : 5 ≤ Fintype.card I) (hH : H_set.card = H) (hHpos : 0 < H) (hHlt : H < Fintype.card I)
    (hdt : d ≤ t) (hw : ∀ i, (S i).card = t)
    (hpair : Pairwise fun i j => (S i ∩ S j).card ≤ d)
    (hhint : ∀ i, (S i ∩ H_set).card ≤ d) (hHt : Fintype.card I * d ≤ H * t) (r0 : ℚ)
    (hc1 : 0 ≤ cubicC1 (Fintype.card I) t d r0)
    (hc2 : 0 ≤ cubicC2 (Fintype.card I) t d r0) :
    (m : ℚ) * (cubicC0 (Fintype.card I) t d r0 +
        cubicC1 (Fintype.card I) t d r0 * p1HintBoost (Fintype.card I) t d H) ≤
      ((t : ℚ) - d) * ((t : ℚ) - r0) ^ 2 := by
  by_cases hm : m = 0
  · subst hm
    have hdt' : (d : ℚ) ≤ t := by exact_mod_cast hdt
    simpa using mul_nonneg (by linarith : 0 ≤ (t : ℚ) - d) (sq_nonneg ((t : ℚ) - r0))
  · set n : ℚ := (Fintype.card I : ℚ)
    have hn_ge : (5 : ℚ) ≤ n := by dsimp [n]; exact_mod_cast hn
    have hn0 : n ≠ 0 := by linarith
    have hn1 : n - 1 ≠ 0 := by linarith
    have hn2 : n - 2 ≠ 0 := by linarith
    have hn3 : n - 3 ≠ 0 := by linarith
    have hn4 : n - 4 ≠ 0 := by linarith
    have hP1 : (m : ℚ) ^ 2 * p1HintBoost n t d H ≤
        ∑ i : Fin m, ∑ j : Fin m, P1 n t ((S i ∩ S j).card) :=
      sum_P1_hint_lower H_set S hH hHpos hHlt hw hhint hHt
    have hP2 : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, P2 n t ((S i ∩ S j).card) :=
      sum_P2_nonneg S (by omega) hw
    have hP3 : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, P3 n t ((S i ∩ S j).card) :=
      sum_P3_nonneg S hn hw
    have hid : ∑ i : Fin m, ∑ j : Fin m,
        (((S i ∩ S j).card : ℚ) - d) * (((S i ∩ S j).card : ℚ) - r0) ^ 2 =
        (m : ℚ) ^ 2 * cubicC0 n t d r0 +
        cubicC1 n t d r0 * (∑ i : Fin m, ∑ j : Fin m, P1 n t ((S i ∩ S j).card)) +
        cubicC2 n t d r0 * (∑ i : Fin m, ∑ j : Fin m, P2 n t ((S i ∩ S j).card)) +
        6 * (∑ i : Fin m, ∑ j : Fin m, P3 n t ((S i ∩ S j).card)) := by
      simp_rw [cubic_poly_eq n t d r0 _ hn0 hn1 hn2 hn3 hn4, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hlow : (m : ℚ) ^ 2 * (cubicC0 n t d r0 + cubicC1 n t d r0 * p1HintBoost n t d H) ≤
        ∑ i : Fin m, ∑ j : Fin m,
          (((S i ∩ S j).card : ℚ) - d) * (((S i ∩ S j).card : ℚ) - r0) ^ 2 := by
      rw [hid]
      have hmul : cubicC1 n t d r0 * ((m : ℚ) ^ 2 * p1HintBoost n t d H) ≤
          cubicC1 n t d r0 * (∑ i : Fin m, ∑ j : Fin m, P1 n t ((S i ∩ S j).card)) :=
        mul_le_mul_of_nonneg_left hP1 hc1
      have hP2_nn : 0 ≤ cubicC2 n t d r0 *
          (∑ i : Fin m, ∑ j : Fin m, P2 n t ((S i ∩ S j).card)) :=
        mul_nonneg hc2 hP2
      have hP3_nn : 0 ≤ 6 * (∑ i : Fin m, ∑ j : Fin m, P3 n t ((S i ∩ S j).card)) :=
        mul_nonneg (by norm_num) hP3
      have hstep1 : (m : ℚ) ^ 2 * cubicC0 n t d r0 +
            cubicC1 n t d r0 * ((m : ℚ) ^ 2 * p1HintBoost n t d H) ≤
          (m : ℚ) ^ 2 * cubicC0 n t d r0 +
            cubicC1 n t d r0 * (∑ i : Fin m, ∑ j : Fin m, P1 n t ((S i ∩ S j).card)) :=
        add_le_add (le_refl _) hmul
      have hstep2 := add_le_add hstep1 hP2_nn
      have hstep3 := add_le_add hstep2 hP3_nn
      have hring : (m : ℚ) ^ 2 * (cubicC0 n t d r0 + cubicC1 n t d r0 * p1HintBoost n t d H) =
          (m : ℚ) ^ 2 * cubicC0 n t d r0 +
            cubicC1 n t d r0 * ((m : ℚ) ^ 2 * p1HintBoost n t d H) + 0 + 0 := by ring
      rw [hring]
      exact hstep3
    have hhi : ∑ i : Fin m, ∑ j : Fin m,
        (((S i ∩ S j).card : ℚ) - d) * (((S i ∩ S j).card : ℚ) - r0) ^ 2 ≤
        (m : ℚ) * (((t : ℚ) - d) * ((t : ℚ) - r0) ^ 2) := by
      have hrow (i : Fin m) :
          ∑ j : Fin m, (((S i ∩ S j).card : ℚ) - d) * (((S i ∩ S j).card : ℚ) - r0) ^ 2 ≤
            ((t : ℚ) - d) * ((t : ℚ) - r0) ^ 2 := by
        rw [← Finset.add_sum_erase univ _ (mem_univ i), inter_self, hw i]
        have hoff : ∑ j ∈ univ.erase i,
            (((S i ∩ S j).card : ℚ) - d) * (((S i ∩ S j).card : ℚ) - r0) ^ 2 ≤ 0 := by
          refine Finset.sum_nonpos fun j hj => ?_
          have hle : ((S i ∩ S j).card : ℚ) ≤ d := by
            exact_mod_cast hpair (mem_erase.mp hj).1.symm
          exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
        linarith
      calc
        _ ≤ ∑ _i : Fin m, (((t : ℚ) - d) * ((t : ℚ) - r0) ^ 2) :=
          Finset.sum_le_sum fun i _ => hrow i
        _ = _ := by simp
    have hmpos : (0 : ℚ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
    have htot : (m : ℚ) * ((m : ℚ) * (cubicC0 n t d r0 + cubicC1 n t d r0 * p1HintBoost n t d H)) ≤
        (m : ℚ) * (((t : ℚ) - d) * ((t : ℚ) - r0) ^ 2) := by
      have hsq : (m : ℚ) * ((m : ℚ) * (cubicC0 n t d r0 + cubicC1 n t d r0 * p1HintBoost n t d H)) =
          (m : ℚ) ^ 2 * (cubicC0 n t d r0 + cubicC1 n t d r0 * p1HintBoost n t d H) := by ring
      rw [hsq]
      exact hlow.trans hhi
    exact le_of_mul_le_mul_left htot hmpos

end HahnHintBoost

section TightShellTransfer

variable {I : Type} [Fintype I] [DecidableEq I]

theorem over_budget_shell_of_quad_hint {F : Type*} [Field F] [DecidableEq F] [Nonempty I]
    (D : I ↪ F) (k t H arity B : ℕ) (hn : 3 ≤ Fintype.card I) (hHpos : 0 < H)
    (hHlt : H < Fintype.card I) (hdt : k - 1 ≤ t) (hHt : Fintype.card I * (k - 1) ≤ H * t)
    (hc1 : 0 ≤ quadC1 (Fintype.card I) t ((k - 1 : ℕ) : ℚ))
    (hc0b : 0 < quadC0 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) +
      quadC1 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) *
        p1HintBoost (Fintype.card I) t ((k - 1 : ℕ) : ℚ) H)
    (hbudget : (t : ℚ) * ((t : ℚ) - ((k - 1 : ℕ) : ℚ)) <
      (B : ℚ) * (quadC0 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) +
        quadC1 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) *
          p1HintBoost (Fintype.card I) t ((k - 1 : ℕ) : ℚ) H))
    (y : I → Fin arity → F) (T : Finset (I → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D k : Set (I → F)))
    (hagree : ∀ w ∈ T, t ≤ agree w y) (hover : B < T.card) :
    ∀ w ∈ T, agree w y < H := by
  classical
  intro h hhT
  by_contra! hhH
  let supp (w : I → Fin arity → F) : Finset I := univ.filter fun x => w x = y x
  have hsupp_card (w : I → Fin arity → F) : (supp w).card = agree w y := by simp [supp, Code.agree]
  obtain ⟨H_set, hHsub, hHcard⟩ := Finset.exists_subset_card_eq (hsupp_card h ▸ hhH)
  let T' := T.erase h
  let e := (Fintype.equivFin ↥T').symm
  let word (i : Fin (Fintype.card ↥T')) := (e i).val
  have hword_mem (i) : word i ∈ T := mem_of_mem_erase (e i).property
  have hword_ne (i) : word i ≠ h := (mem_erase.mp (e i).property).1
  choose S hSsub hScard using fun i =>
    Finset.exists_subset_card_eq (hsupp_card (word i) ▸ hagree (word i) (hword_mem i))
  have hpair : Pairwise fun i j => (S i ∩ S j).card ≤ k - 1 := by
    intro i j hij
    have hne : word i ≠ word j := fun he => hij (e.injective (Subtype.ext he))
    have hd := ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet
      (hcode (word i) (hword_mem i)) (hcode (word j) (hword_mem j)) hne
    have hle : (S i ∩ S j).card ≤ agree (word i) (word j) := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
        (Finset.mem_filter.mp (hSsub i hxi)).2.trans (Finset.mem_filter.mp (hSsub j hxj)).2.symm⟩
    omega
  have hhint_cap (i) : (S i ∩ H_set).card ≤ k - 1 := by
    have hd := ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet
      (hcode (word i) (hword_mem i)) (hcode h hhT) (hword_ne i)
    have hle : (S i ∩ H_set).card ≤ agree (word i) h := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxi, hxh⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
        (Finset.mem_filter.mp (hSsub i hxi)).2.trans (Finset.mem_filter.mp (hHsub hxh)).2.symm⟩
    omega
  have hblk := quadratic_hahn_block_bound_with_hint H_set S hn hHcard hHpos hHlt hdt
    hScard hpair hhint_cap hHt hc1
  have hT'card : Fintype.card ↥T' = T.card - 1 := by rw [Fintype.card_coe, card_erase_of_mem hhT]
  have hgeB : (B : ℚ) ≤ (Fintype.card ↥T' : ℚ) := by
    rw [hT'card]; exact_mod_cast (show B ≤ T.card - 1 by omega)
  have hmul := mul_le_mul_of_nonneg_right hgeB hc0b.le
  exact not_lt_of_ge (hmul.trans hblk) hbudget

theorem over_budget_shell_of_cubic_hint {F : Type*} [Field F] [DecidableEq F] [Nonempty I]
    (D : I ↪ F) (k t H arity B : ℕ) (r0 : ℚ) (hn : 5 ≤ Fintype.card I) (hHpos : 0 < H)
    (hHlt : H < Fintype.card I) (hdt : k - 1 ≤ t) (hHt : Fintype.card I * (k - 1) ≤ H * t)
    (hc1 : 0 ≤ cubicC1 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) r0)
    (hc2 : 0 ≤ cubicC2 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) r0)
    (hc0b : 0 < cubicC0 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) r0 +
      cubicC1 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) r0 *
        p1HintBoost (Fintype.card I) t ((k - 1 : ℕ) : ℚ) H)
    (hbudget : ((t : ℚ) - ((k - 1 : ℕ) : ℚ)) * ((t : ℚ) - r0) ^ 2 <
      (B : ℚ) * (cubicC0 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) r0 +
        cubicC1 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) r0 *
          p1HintBoost (Fintype.card I) t ((k - 1 : ℕ) : ℚ) H))
    (y : I → Fin arity → F) (T : Finset (I → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D k : Set (I → F)))
    (hagree : ∀ w ∈ T, t ≤ agree w y) (hover : B < T.card) :
    ∀ w ∈ T, agree w y < H := by
  classical
  intro h hhT
  by_contra! hhH
  let supp (w : I → Fin arity → F) : Finset I := univ.filter fun x => w x = y x
  have hsupp_card (w : I → Fin arity → F) : (supp w).card = agree w y := by simp [supp, Code.agree]
  obtain ⟨H_set, hHsub, hHcard⟩ := Finset.exists_subset_card_eq (hsupp_card h ▸ hhH)
  let T' := T.erase h
  let e := (Fintype.equivFin ↥T').symm
  let word (i : Fin (Fintype.card ↥T')) := (e i).val
  have hword_mem (i) : word i ∈ T := mem_of_mem_erase (e i).property
  have hword_ne (i) : word i ≠ h := (mem_erase.mp (e i).property).1
  choose S hSsub hScard using fun i =>
    Finset.exists_subset_card_eq (hsupp_card (word i) ▸ hagree (word i) (hword_mem i))
  have hpair : Pairwise fun i j => (S i ∩ S j).card ≤ k - 1 := by
    intro i j hij
    have hne : word i ≠ word j := fun he => hij (e.injective (Subtype.ext he))
    have hd := ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet
      (hcode (word i) (hword_mem i)) (hcode (word j) (hword_mem j)) hne
    have hle : (S i ∩ S j).card ≤ agree (word i) (word j) := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
        (Finset.mem_filter.mp (hSsub i hxi)).2.trans (Finset.mem_filter.mp (hSsub j hxj)).2.symm⟩
    omega
  have hhint_cap (i) : (S i ∩ H_set).card ≤ k - 1 := by
    have hd := ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet
      (hcode (word i) (hword_mem i)) (hcode h hhT) (hword_ne i)
    have hle : (S i ∩ H_set).card ≤ agree (word i) h := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxi, hxh⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
        (Finset.mem_filter.mp (hSsub i hxi)).2.trans (Finset.mem_filter.mp (hHsub hxh)).2.symm⟩
    omega
  have hblk := cubic_hahn_block_bound_with_hint H_set S hn hHcard hHpos hHlt hdt
    hScard hpair hhint_cap hHt r0 hc1 hc2
  have hT'card : Fintype.card ↥T' = T.card - 1 := by rw [Fintype.card_coe, card_erase_of_mem hhT]
  have hgeB : (B : ℚ) ≤ (Fintype.card ↥T' : ℚ) := by
    rw [hT'card]; exact_mod_cast (show B ≤ T.card - 1 by omega)
  have hmul := mul_le_mul_of_nonneg_right hgeB hc0b.le
  exact not_lt_of_ge (hmul.trans hblk) hbudget

end TightShellTransfer

section ProductionTightB2Shells

/-- Rate `1/2`, `J+1` (`B₂ = 2³¹`): Cubic Hahn + `P₁` hint boost tightens the forbidden
shell from `A_J + 15,050` down to **`A_J + 13,433`** (`agree w y < 759,263,558`). -/
theorem rate_half_j1_shell_B2_cubic {F : Type*} [Field F] [DecidableEq F]
    (D : Fin 1073741824 ↪ F) (arity : ℕ)
    (y : Fin 1073741824 → Fin arity → F) (T : Finset (Fin 1073741824 → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D 536870912 : Set (Fin 1073741824 → F)))
    (hagree : ∀ w ∈ T, 759250124 ≤ agree w y) (hover : 2147483648 < T.card) :
    ∀ w ∈ T, agree w y < 759263558 :=
  over_budget_shell_of_cubic_hint D 536870912 759250124 759263558 arity 2147483648 314091338
    (by simp only [Fintype.card_fin]; norm_num) (by norm_num)
    (by simp only [Fintype.card_fin]; norm_num) (by norm_num)
    (by simp only [Fintype.card_fin]; norm_num)
    (by simp only [Fintype.card_fin]; norm_num [cubicC1, cubicC2])
    (by simp only [Fintype.card_fin]; norm_num [cubicC2])
    (by simp only [Fintype.card_fin]; norm_num [cubicC0, cubicC1, cubicC2, p1HintBoost])
    (by simp only [Fintype.card_fin]; norm_num [cubicC0, cubicC1, cubicC2, p1HintBoost])
    y T hcode hagree hover

/-- Rate `1/4`, `J+1` (`B₂ = 2³¹`): Cubic Hahn + `P₁` hint boost tightens the forbidden
shell from `A_J + 34,757` down to **`A_J + 32,770`** (`agree w y < 536,903,681`). -/
theorem rate_quarter_j1_shell_B2_cubic {F : Type*} [Field F] [DecidableEq F]
    (D : Fin 1073741824 ↪ F) (arity : ℕ)
    (y : Fin 1073741824 → Fin arity → F) (T : Finset (Fin 1073741824 → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D 268435456 : Set (Fin 1073741824 → F)))
    (hagree : ∀ w ∈ T, 536870910 ≤ agree w y) (hover : 2147483648 < T.card) :
    ∀ w ∈ T, agree w y < 536903681 :=
  over_budget_shell_of_cubic_hint D 268435456 536870910 536903681 arity 2147483648 (-53742)
    (by simp only [Fintype.card_fin]; norm_num) (by norm_num)
    (by simp only [Fintype.card_fin]; norm_num) (by norm_num)
    (by simp only [Fintype.card_fin]; norm_num)
    (by simp only [Fintype.card_fin]; norm_num [cubicC1, cubicC2])
    (by simp only [Fintype.card_fin]; norm_num [cubicC2])
    (by simp only [Fintype.card_fin]; norm_num [cubicC0, cubicC1, cubicC2, p1HintBoost])
    (by simp only [Fintype.card_fin]; norm_num [cubicC0, cubicC1, cubicC2, p1HintBoost])
    y T hcode hagree hover

/-- Rate `1/8`, `J+2` (`B₂ = 2³¹`): Quadratic Hahn + `P₁` hint boost tightens the forbidden
shell from `A_J + 41,565` down to **`A_J + 36,296`** (`agree w y < 379,661,358`). -/
theorem rate_eighth_j2_shell_B2_quad {F : Type*} [Field F] [DecidableEq F]
    (D : Fin 1073741824 ↪ F) (arity : ℕ)
    (y : Fin 1073741824 → Fin arity → F) (T : Finset (Fin 1073741824 → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D 134217728 : Set (Fin 1073741824 → F)))
    (hagree : ∀ w ∈ T, 379625060 ≤ agree w y) (hover : 2147483648 < T.card) :
    ∀ w ∈ T, agree w y < 379661358 :=
  over_budget_shell_of_quad_hint D 134217728 379625060 379661358 arity 2147483648
    (by simp only [Fintype.card_fin]; norm_num) (by norm_num)
    (by simp only [Fintype.card_fin]; norm_num) (by norm_num)
    (by simp only [Fintype.card_fin]; norm_num)
    (by simp only [Fintype.card_fin]; norm_num [quadC1])
    (by simp only [Fintype.card_fin]; norm_num [quadC0, quadC1, p1HintBoost])
    (by simp only [Fintype.card_fin]; norm_num [quadC0, quadC1, p1HintBoost])
    y T hcode hagree hover

/-- Rate `1/16`, `J+1` (`B₂ = 2³¹`): Quadratic Hahn + `P₁` hint boost tightens the forbidden
shell from `A_J + 43,737` down to **`A_J + 31,730`** (`agree w y < 268,467,184`, `1.38×` tighter!). -/
theorem rate_sixteenth_j1_shell_B2_quad {F : Type*} [Field F] [DecidableEq F]
    (D : Fin 1073741824 ↪ F) (arity : ℕ)
    (y : Fin 1073741824 → Fin arity → F) (T : Finset (Fin 1073741824 → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D 67108864 : Set (Fin 1073741824 → F)))
    (hagree : ∀ w ∈ T, 268435453 ≤ agree w y) (hover : 2147483648 < T.card) :
    ∀ w ∈ T, agree w y < 268467184 :=
  over_budget_shell_of_quad_hint D 67108864 268435453 268467184 arity 2147483648
    (by simp only [Fintype.card_fin]; norm_num) (by norm_num)
    (by simp only [Fintype.card_fin]; norm_num) (by norm_num)
    (by simp only [Fintype.card_fin]; norm_num)
    (by simp only [Fintype.card_fin]; norm_num [quadC1])
    (by simp only [Fintype.card_fin]; norm_num [quadC0, quadC1, p1HintBoost])
    (by simp only [Fintype.card_fin]; norm_num [quadC0, quadC1, p1HintBoost])
    y T hcode hagree hover

end ProductionTightB2Shells

end ProximityGap.CubicHintBoundaryShell

#print axioms ProximityGap.CubicHintBoundaryShell.sum_P1_hint_lower
#print axioms ProximityGap.CubicHintBoundaryShell.quadratic_hahn_block_bound_with_hint
#print axioms ProximityGap.CubicHintBoundaryShell.cubic_hahn_block_bound_with_hint
#print axioms ProximityGap.CubicHintBoundaryShell.over_budget_shell_of_quad_hint
#print axioms ProximityGap.CubicHintBoundaryShell.over_budget_shell_of_cubic_hint
#print axioms ProximityGap.CubicHintBoundaryShell.rate_half_j1_shell_B2_cubic
#print axioms ProximityGap.CubicHintBoundaryShell.rate_quarter_j1_shell_B2_cubic
#print axioms ProximityGap.CubicHintBoundaryShell.rate_eighth_j2_shell_B2_quad
#print axioms ProximityGap.CubicHintBoundaryShell.rate_sixteenth_j1_shell_B2_quad
