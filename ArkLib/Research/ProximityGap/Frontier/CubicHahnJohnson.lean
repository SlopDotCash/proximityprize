/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonRank

/-!
# Cubic Hahn / Degree-3 Johnson-Scheme List Decoding Bounds Beyond Johnson

We give a completely elementary, self-contained sum-of-squares proof of the
degree-1, degree-2, and degree-3 Hahn dual-eigenvalue inequalities (`P1`, `P2`, `P3`)
on constant-weight set families, using centered incidence counts on 1-, 2-, and
3-element subsets of the evaluation domain.

Applying the cubic polynomial `(s - d) * (s - r₀)² ≤ 0` (for all `s ≤ d`) yields
explicit list-decoding upper bounds strictly beyond the Johnson radius — slashing
the `MultipleOmissionJohnson` budgets by 2×–10× at `Johnson + 1`, by 50×–147× at
`Johnson + 2`, and certifying polynomial list sizes up to `Θ(√n)` full integer
error steps beyond Johnson (e.g. `4,799` to `12,288` errors past Johnson at
`n = 2³⁰`) over arbitrary fields, injective domains, and interleaving widths.
-/

set_option autoImplicit false

namespace ProximityGap.CubicHahnJohnson

open Finset Code InterleavedListJohnsonRank
open scoped BigOperators

section ElementaryHahn

/-- Degree-1 orthogonal Hahn polynomial `P₁(n, t, s)` in intersection size `s`. -/
def P1 (n t s : ℚ) : ℚ :=
  s - t ^ 2 / n

/-- Degree-2 orthogonal Hahn polynomial `P₂(n, t, s)` in intersection size `s`. -/
def P2 (n t s : ℚ) : ℚ :=
  s * (s - 1) / 2 - (t - 1) ^ 2 / (n - 2) * s +
    t ^ 2 * (t - 1) ^ 2 / (2 * (n - 1) * (n - 2))

/-- Degree-3 orthogonal Hahn polynomial `P₃(n, t, s)` in intersection size `s`. -/
def P3 (n t s : ℚ) : ℚ :=
  s * (s - 1) * (s - 2) / 6 - (t - 2) ^ 2 / (n - 4) * (s * (s - 1) / 2) +
    (t - 1) ^ 2 * (t - 2) ^ 2 / (2 * (n - 3) * (n - 4)) * s -
    t ^ 2 * (t - 1) ^ 2 * (t - 2) ^ 2 / (6 * (n - 2) * (n - 3) * (n - 4))

variable {I : Type} [Fintype I] [DecidableEq I]

private def ind {m : ℕ} (S : Fin m → Finset I) (i : Fin m) (x : I) : ℚ :=
  if x ∈ S i then 1 else 0

private def deg1 {m : ℕ} (S : Fin m → Finset I) (x : I) : ℚ :=
  ∑ i : Fin m, ind S i x

private def deg2 {m : ℕ} (S : Fin m → Finset I) (x y : I) : ℚ :=
  ∑ i : Fin m, ind S i x * ind S i y

private def deg3 {m : ℕ} (S : Fin m → Finset I) (x y z : I) : ℚ :=
  ∑ i : Fin m, ind S i x * ind S i y * ind S i z

private theorem sum_ite_mem (A : Finset I) :
    ∑ x : I, (if x ∈ A then (1 : ℚ) else 0) = (A.card : ℚ) := by
  simp

private theorem sum_ind_eq_card {m : ℕ} (S : Fin m → Finset I) (i : Fin m) :
    ∑ x : I, ind S i x = ((S i).card : ℚ) := by
  simp [ind]

private theorem sum_deg1 {m t : ℕ} (S : Fin m → Finset I) (ht : ∀ i, (S i).card = t) :
    ∑ x : I, deg1 S x = (m : ℚ) * t := by
  unfold deg1
  rw [Finset.sum_comm]
  simp [sum_ind_eq_card, ht]

private theorem sum_deg1_sq {m : ℕ} (S : Fin m → Finset I) :
    ∑ x : I, deg1 S x ^ 2 = ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) := by
  simp_rw [deg1, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hterm (x : I) : ind S i x * ind S j x = if x ∈ S i ∩ S j then 1 else 0 := by
    by_cases hi : x ∈ S i <;> by_cases hj : x ∈ S j <;> simp [ind, hi, hj]
  simp_rw [hterm]
  exact sum_ite_mem (S i ∩ S j)

private theorem sum_deg2_inner {m t : ℕ} (S : Fin m → Finset I) (ht : ∀ i, (S i).card = t) (x : I) :
    ∑ y ∈ univ.erase x, deg2 S x y = ((t : ℚ) - 1) * deg1 S x := by
  unfold deg2 deg1
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]
  by_cases hx : x ∈ S i
  · have herase : ∑ y ∈ univ.erase x, ind S i y = (t : ℚ) - 1 := by
      have h := Finset.add_sum_erase univ (ind S i) (mem_univ x)
      rw [sum_ind_eq_card, ht i] at h
      have h1 : ind S i x = 1 := by simp [ind, hx]
      linarith
    rw [herase]
    simp [ind, hx]
  · simp [ind, hx]

private theorem sum_deg2_sq {m : ℕ} (S : Fin m → Finset I) :
    ∑ x : I, ∑ y ∈ univ.erase x, deg2 S x y ^ 2 =
      ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - 1) := by
  simp_rw [deg2, sq, Finset.sum_mul_sum]
  have hinner (x : I) :
      ∑ y ∈ univ.erase x, ∑ i : Fin m, ∑ j : Fin m, (ind S i x * ind S i y) * (ind S j x * ind S j y) =
      ∑ i : Fin m, ∑ j : Fin m, (ind S i x * ind S j x) * ∑ y ∈ univ.erase x, (ind S i y * ind S j y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by ring
  simp_rw [hinner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hprod (x : I) : ind S i x * ind S j x = if x ∈ S i ∩ S j then 1 else 0 := by
    by_cases hi : x ∈ S i <;> by_cases hj : x ∈ S j <;> simp [ind, hi, hj]
  have hsum_all : ∑ y : I, ind S i y * ind S j y = ((S i ∩ S j).card : ℚ) := by
    simp_rw [hprod]
    exact sum_ite_mem (S i ∩ S j)
  have hstep (x : I) :
      (ind S i x * ind S j x) * ∑ y ∈ univ.erase x, (ind S i y * ind S j y) =
      (if x ∈ S i ∩ S j then 1 else 0) * (((S i ∩ S j).card : ℚ) - 1) := by
    have h := Finset.add_sum_erase univ (fun y => ind S i y * ind S j y) (mem_univ x)
    rw [hsum_all] at h
    by_cases hx : x ∈ S i ∩ S j
    · have h1 : ind S i x * ind S j x = 1 := by simp [hprod, hx]
      rw [h1] at h ⊢
      simp [hx]
      linarith
    · have h0 : ind S i x * ind S j x = 0 := by simp [hprod, hx]
      simp [h0, hx]
  simp_rw [hstep, ← Finset.sum_mul]
  rw [sum_ite_mem]

private theorem sum_deg3_inner {m t : ℕ} (S : Fin m → Finset I) (ht : ∀ i, (S i).card = t)
    {x y : I} (hxy : x ≠ y) :
    ∑ z ∈ (univ.erase x).erase y, deg3 S x y z = ((t : ℚ) - 2) * deg2 S x y := by
  unfold deg3 deg2
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]
  by_cases hx : x ∈ S i
  · by_cases hy : y ∈ S i
    · have herase : ∑ z ∈ (univ.erase x).erase y, ind S i z = (t : ℚ) - 2 := by
        have h1 := Finset.add_sum_erase univ (ind S i) (mem_univ x)
        have hy_mem : y ∈ univ.erase x := mem_erase.mpr ⟨hxy.symm, mem_univ y⟩
        have h2 := Finset.add_sum_erase (univ.erase x) (ind S i) hy_mem
        rw [sum_ind_eq_card, ht i] at h1
        have hx1 : ind S i x = 1 := by simp [ind, hx]
        have hy1 : ind S i y = 1 := by simp [ind, hy]
        linarith
      rw [herase]
      simp [ind, hx, hy]
    · simp [ind, hx, hy]
  · simp [ind, hx]

private theorem sum_deg3_sq {m : ℕ} (S : Fin m → Finset I) :
    ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z ^ 2 =
      ∑ i : Fin m, ∑ j : Fin m,
        ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - 1) * (((S i ∩ S j).card : ℚ) - 2) := by
  simp_rw [deg3, sq, Finset.sum_mul_sum]
  have hinner (x y : I) :
      ∑ z ∈ (univ.erase x).erase y, ∑ i : Fin m, ∑ j : Fin m,
        (ind S i x * ind S i y * ind S i z) * (ind S j x * ind S j y * ind S j z) =
      ∑ i : Fin m, ∑ j : Fin m,
        (ind S i x * ind S j x) * (ind S i y * ind S j y) *
          ∑ z ∈ (univ.erase x).erase y, (ind S i z * ind S j z) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => by ring
  simp_rw [hinner]
  have hmid (x : I) :
      ∑ y ∈ univ.erase x, ∑ i : Fin m, ∑ j : Fin m,
        (ind S i x * ind S j x) * (ind S i y * ind S j y) *
          ∑ z ∈ (univ.erase x).erase y, (ind S i z * ind S j z) =
      ∑ i : Fin m, ∑ j : Fin m,
        ∑ y ∈ univ.erase x, (ind S i x * ind S j x) * (ind S i y * ind S j y) *
          ∑ z ∈ (univ.erase x).erase y, (ind S i z * ind S j z) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  simp_rw [hmid]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hprod (x : I) : ind S i x * ind S j x = if x ∈ S i ∩ S j then 1 else 0 := by
    by_cases hi : x ∈ S i <;> by_cases hj : x ∈ S j <;> simp [ind, hi, hj]
  have hsum_all : ∑ z : I, ind S i z * ind S j z = ((S i ∩ S j).card : ℚ) := by
    simp_rw [hprod]
    exact sum_ite_mem (S i ∩ S j)
  have hstep2 (x : I) :
      ∑ y ∈ univ.erase x, (ind S i x * ind S j x) * (ind S i y * ind S j y) *
          ∑ z ∈ (univ.erase x).erase y, (ind S i z * ind S j z) =
      (if x ∈ S i ∩ S j then 1 else 0) * (((S i ∩ S j).card : ℚ) - 1) *
        (((S i ∩ S j).card : ℚ) - 2) := by
    by_cases hx : x ∈ S i ∩ S j
    · have hx1 : ind S i x * ind S j x = 1 := by simp [hprod, hx]
      have hterm (y : I) (hy : y ∈ univ.erase x) :
          (ind S i x * ind S j x) * (ind S i y * ind S j y) *
            ∑ z ∈ (univ.erase x).erase y, (ind S i z * ind S j z) =
          (if y ∈ S i ∩ S j then 1 else 0) * (((S i ∩ S j).card : ℚ) - 2) := by
        rw [hx1, one_mul]
        by_cases hyS : y ∈ S i ∩ S j
        · have hy1 : ind S i y * ind S j y = 1 := by simp [hprod, hyS]
          have h1 := Finset.add_sum_erase univ (fun z => ind S i z * ind S j z) (mem_univ x)
          have h2 := Finset.add_sum_erase (univ.erase x) (fun z => ind S i z * ind S j z) hy
          rw [hsum_all, hx1] at h1
          rw [hy1] at h2
          simp [hy1, hyS]
          linarith
        · have hy0 : ind S i y * ind S j y = 0 := by simp [hprod, hyS]
          simp [hy0, hyS]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
      simp only [hx, ite_true, one_mul]
      have h1 := Finset.add_sum_erase univ (fun y => if y ∈ S i ∩ S j then (1 : ℚ) else 0) (mem_univ x)
      have hall := sum_ite_mem (S i ∩ S j)
      rw [hall] at h1
      simp only [hx, ite_true] at h1
      have her : ∑ y ∈ univ.erase x, (if y ∈ S i ∩ S j then (1 : ℚ) else 0) = ((S i ∩ S j).card : ℚ) - 1 := by
        linarith
      rw [her]
    · have hx0 : ind S i x * ind S j x = 0 := by simp [hprod, hx]
      simp [hx0, hx]
  simp_rw [hstep2, ← Finset.sum_mul]
  rw [sum_ite_mem]

/-- Degree-1 Hahn positivity: `∑_{i,j} P₁(n, t, |S i ∩ S j|) ≥ 0`. -/
theorem sum_P1_nonneg {m t : ℕ} (S : Fin m → Finset I) (hn : 1 ≤ Fintype.card I)
    (ht : ∀ i, (S i).card = t) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, P1 (Fintype.card I) t ((S i ∩ S j).card) := by
  let n : ℚ := Fintype.card I
  have hn_ge : (1 : ℚ) ≤ n := by dsimp [n]; exact_mod_cast hn
  have hn0 : n ≠ 0 := by linarith
  let c (x : I) : ℚ := deg1 S x - (m : ℚ) * t / n
  have hsq : 0 ≤ ∑ x : I, c x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg (c x)
  have hexp : ∑ x : I, c x ^ 2 =
      ∑ i : Fin m, ∑ j : Fin m, P1 n t ((S i ∩ S j).card) := by
    have h1 : ∑ x : I, c x ^ 2 =
        (∑ x : I, deg1 S x ^ 2) - 2 * ((m : ℚ) * t / n) * (∑ x : I, deg1 S x) +
          n * ((m : ℚ) * t / n) ^ 2 := by
      have hterm (x : I) : c x ^ 2 =
          deg1 S x ^ 2 - 2 * ((m : ℚ) * t / n) * deg1 S x + ((m : ℚ) * t / n) ^ 2 := by
        dsimp [c]; ring
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rfl
    rw [h1, sum_deg1_sq, sum_deg1 S ht]
    simp_rw [P1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp [hn0]
    ring
  simpa only [n] using hexp ▸ hsq

/-- Degree-2 Hahn positivity: `∑_{i,j} P₂(n, t, |S i ∩ S j|) ≥ 0` for `n ≥ 3`. -/
theorem sum_P2_nonneg {m t : ℕ} (S : Fin m → Finset I) (hn : 3 ≤ Fintype.card I)
    (ht : ∀ i, (S i).card = t) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, P2 (Fintype.card I) t ((S i ∩ S j).card) := by
  let n : ℚ := Fintype.card I
  have hn_ge : (3 : ℚ) ≤ n := by dsimp [n]; exact_mod_cast hn
  have hn1 : n - 1 ≠ 0 := by linarith
  have hn2 : n - 2 ≠ 0 := by linarith
  let α : ℚ := ((t : ℚ) - 1) / (n - 2)
  let β : ℚ := (t : ℚ) * ((t : ℚ) - 1) / ((n - 1) * (n - 2))
  let a (x y : I) : ℚ := deg2 S x y - α * (deg1 S x + deg1 S y) + β * m
  have ha_symm (x y : I) : a x y = a y x := by
    have hd : deg2 S x y = deg2 S y x := by
      unfold deg2
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    dsimp [a]
    rw [hd]
    ring
  have hzero (x : I) : ∑ y ∈ univ.erase x, a x y = 0 := by
    have hsum_deg1 : ∑ y ∈ univ.erase x, deg1 S y = (m : ℚ) * t - deg1 S x := by
      have h := Finset.add_sum_erase univ (deg1 S) (mem_univ x)
      rw [sum_deg1 S ht] at h
      linarith
    have hcard : ((univ.erase x).card : ℚ) = n - 1 := by
      rw [Finset.card_erase_of_mem (mem_univ x), Finset.card_univ, Nat.cast_sub (by omega)]
      simp [n]
    have hexp : ∑ y ∈ univ.erase x, a x y =
        (∑ y ∈ univ.erase x, deg2 S x y) -
          α * (((univ.erase x).card : ℚ) * deg1 S x + ∑ y ∈ univ.erase x, deg1 S y) +
          ((univ.erase x).card : ℚ) * (β * m) := by
      simp only [a, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hexp, sum_deg2_inner S ht x, hsum_deg1, hcard]
    dsimp [α, β]
    field_simp [hn1, hn2]
    ring
  have hsq : 0 ≤ ∑ x : I, ∑ y ∈ univ.erase x, a x y ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg (a x y)
  have hswap (f : I → I → ℚ) :
      ∑ x : I, ∑ y ∈ univ.erase x, f x y = ∑ y : I, ∑ x ∈ univ.erase y, f x y := by
    let p := (univ : Finset (I × I)).filter fun z => z.1 ≠ z.2
    have h1 : ∑ x : I, ∑ y ∈ univ.erase x, f x y = ∑ z ∈ p, f z.1 z.2 := by
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_filter]
      congr 1; ext y; simp [ne_comm]
    have h2 : ∑ y : I, ∑ x ∈ univ.erase y, f x y = ∑ z ∈ p, f z.1 z.2 := by
      rw [Finset.sum_filter, Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.sum_filter]
      congr 1; ext x; simp
    exact h1.trans h2.symm
  have hkill_x : ∑ x : I, ∑ y ∈ univ.erase x, a x y * deg1 S x = 0 := by
    have : ∀ x : I, ∑ y ∈ univ.erase x, a x y * deg1 S x = 0 := fun x => by
      rw [← Finset.sum_mul, hzero x, zero_mul]
    simp [this]
  have hkill_y : ∑ x : I, ∑ y ∈ univ.erase x, a x y * deg1 S y = 0 := by
    rw [hswap]
    have : ∀ y : I, ∑ x ∈ univ.erase y, a x y * deg1 S y = 0 := fun y => by
      simp_rw [ha_symm _ y]
      rw [← Finset.sum_mul, hzero y, zero_mul]
    simp [this]
  have hkill_1 : ∑ x : I, ∑ y ∈ univ.erase x, a x y = 0 := by
    simp [hzero]
  have horth : ∑ x : I, ∑ y ∈ univ.erase x, a x y ^ 2 =
      ∑ x : I, ∑ y ∈ univ.erase x, deg2 S x y * a x y := by
    have hterm (x y : I) : a x y ^ 2 =
        deg2 S x y * a x y - α * (a x y * deg1 S x) - α * (a x y * deg1 S y) + β * m * a x y := by
      dsimp [a]; ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hkill_x, hkill_y, hkill_1]
    ring
  have hcross_x : ∑ x : I, ∑ y ∈ univ.erase x, deg2 S x y * deg1 S x =
      ((t : ℚ) - 1) * ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) := by
    have hx (x : I) : ∑ y ∈ univ.erase x, deg2 S x y * deg1 S x = ((t : ℚ) - 1) * deg1 S x ^ 2 := by
      rw [← Finset.sum_mul, sum_deg2_inner S ht x]; ring
    simp_rw [hx, ← Finset.mul_sum, sum_deg1_sq]
  have hcross_y : ∑ x : I, ∑ y ∈ univ.erase x, deg2 S x y * deg1 S y =
      ((t : ℚ) - 1) * ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) := by
    rw [hswap]
    have hdsym (x y : I) : deg2 S x y = deg2 S y x := by
      unfold deg2; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp_rw [hdsym]
    exact hcross_x
  have hcross_1 : ∑ x : I, ∑ y ∈ univ.erase x, deg2 S x y = (m : ℚ) * t * ((t : ℚ) - 1) := by
    simp_rw [sum_deg2_inner S ht, ← Finset.mul_sum, sum_deg1 S ht]
    ring
  have hval : ∑ x : I, ∑ y ∈ univ.erase x, deg2 S x y * a x y =
      2 * ∑ i : Fin m, ∑ j : Fin m, P2 n t ((S i ∩ S j).card) := by
    have hterm (x y : I) : deg2 S x y * a x y =
        deg2 S x y ^ 2 - α * (deg2 S x y * deg1 S x) - α * (deg2 S x y * deg1 S y) +
          β * m * deg2 S x y := by
      dsimp [a]; ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [sum_deg2_sq, hcross_x, hcross_y, hcross_1]
    simp_rw [P2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hdiv2 : ∑ i : Fin m, ∑ j : Fin m,
        ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - 1) / 2 =
      (∑ i : Fin m, ∑ j : Fin m,
        ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - 1)) / 2 := by
      simp_rw [← Finset.sum_div]
    rw [hdiv2]
    dsimp [α, β]
    field_simp [hn1, hn2]
    ring
  rw [horth, hval] at hsq
  simpa only [n] using (by linarith : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, P2 n t ((S i ∩ S j).card))

/-- Degree-3 Hahn positivity: `∑_{i,j} P₃(n, t, |S i ∩ S j|) ≥ 0` for `n ≥ 5`. -/
theorem sum_P3_nonneg {m t : ℕ} (S : Fin m → Finset I) (hn : 5 ≤ Fintype.card I)
    (ht : ∀ i, (S i).card = t) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, P3 (Fintype.card I) t ((S i ∩ S j).card) := by
  let n : ℚ := Fintype.card I
  have hn_ge : (5 : ℚ) ≤ n := by dsimp [n]; exact_mod_cast hn
  have hn2 : n - 2 ≠ 0 := by linarith
  have hn3 : n - 3 ≠ 0 := by linarith
  have hn4 : n - 4 ≠ 0 := by linarith
  let α2 : ℚ := ((t : ℚ) - 2) / (n - 4)
  let α1 : ℚ := ((t : ℚ) - 1) * ((t : ℚ) - 2) / ((n - 3) * (n - 4))
  let α0 : ℚ := (t : ℚ) * ((t : ℚ) - 1) * ((t : ℚ) - 2) / ((n - 2) * (n - 3) * (n - 4))
  let a (x y z : I) : ℚ :=
    deg3 S x y z - α2 * (deg2 S x y + deg2 S x z + deg2 S y z) +
      α1 * (deg1 S x + deg1 S y + deg1 S z) - α0 * m
  have hd2_symm (x y : I) : deg2 S x y = deg2 S y x := by
    unfold deg2; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hd3_swap23 (x y z : I) : deg3 S x y z = deg3 S x z y := by
    unfold deg3; exact Finset.sum_congr rfl fun i _ => by ring
  have hd3_swap12 (x y z : I) : deg3 S x y z = deg3 S y x z := by
    unfold deg3; exact Finset.sum_congr rfl fun i _ => by ring
  have ha_swap23 (x y z : I) : a x y z = a x z y := by
    dsimp [a]; rw [hd3_swap23, hd2_symm y z]; ring
  have ha_swap12 (x y z : I) : a x y z = a y x z := by
    dsimp [a]; rw [hd3_swap12, hd2_symm x y]; ring
  -- Key orthogonality: summing `a x y z` over `z ∉ {x, y}` vanishes identically!
  have hzero {x y : I} (hxy : x ≠ y) : ∑ z ∈ (univ.erase x).erase y, a x y z = 0 := by
    have hy_in : y ∈ univ.erase x := mem_erase.mpr ⟨hxy.symm, mem_univ y⟩
    have hcard : (((univ.erase x).erase y).card : ℚ) = n - 2 := by
      rw [Finset.card_erase_of_mem hy_in, Finset.card_erase_of_mem (mem_univ x), Finset.card_univ,
        Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      simp [n]; ring
    have hsum_d1 : ∑ z ∈ (univ.erase x).erase y, deg1 S z = (m : ℚ) * t - deg1 S x - deg1 S y := by
      have h1 := Finset.add_sum_erase univ (deg1 S) (mem_univ x)
      have h2 := Finset.add_sum_erase (univ.erase x) (deg1 S) hy_in
      rw [sum_deg1 S ht] at h1
      linarith
    have hsum_d2x : ∑ z ∈ (univ.erase x).erase y, deg2 S x z = ((t : ℚ) - 1) * deg1 S x - deg2 S x y := by
      have h := Finset.add_sum_erase (univ.erase x) (deg2 S x) hy_in
      rw [sum_deg2_inner S ht x] at h
      linarith
    have hsum_d2y : ∑ z ∈ (univ.erase x).erase y, deg2 S y z = ((t : ℚ) - 1) * deg1 S y - deg2 S x y := by
      have hx_in : x ∈ univ.erase y := mem_erase.mpr ⟨hxy, mem_univ x⟩
      have hcomm : (univ.erase x).erase y = (univ.erase y).erase x := erase_right_comm
      rw [hcomm]
      have h := Finset.add_sum_erase (univ.erase y) (deg2 S y) hx_in
      rw [sum_deg2_inner S ht y, hd2_symm y x] at h
      linarith
    have hexp : ∑ z ∈ (univ.erase x).erase y, a x y z =
        (∑ z ∈ (univ.erase x).erase y, deg3 S x y z) -
          α2 * ((((univ.erase x).erase y).card : ℚ) * deg2 S x y +
            (∑ z ∈ (univ.erase x).erase y, deg2 S x z) +
            (∑ z ∈ (univ.erase x).erase y, deg2 S y z)) +
          α1 * ((((univ.erase x).erase y).card : ℚ) * deg1 S x +
            (((univ.erase x).erase y).card : ℚ) * deg1 S y +
            (∑ z ∈ (univ.erase x).erase y, deg1 S z)) -
          (((univ.erase x).erase y).card : ℚ) * (α0 * m) := by
      simp only [a, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hexp, sum_deg3_inner S ht hxy, hsum_d2x, hsum_d2y, hsum_d1, hcard]
    dsimp [α2, α1, α0]
    field_simp [hn2, hn3, hn4]
    ring
  -- Swap helpers on ordered distinct triples
  let T3 : Finset (I × I × I) := univ.filter fun w => w.1 ≠ w.2.1 ∧ w.1 ≠ w.2.2 ∧ w.2.1 ≠ w.2.2
  have sum_T3_eq (f : I → I → I → ℚ) :
      ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, f x y z =
        ∑ w ∈ T3, f w.1 w.2.1 w.2.2 := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]
    have h1 (y : I) :
        ∑ z : I, (if x ≠ y ∧ x ≠ z ∧ y ≠ z then f x y z else 0) =
        if y ∈ univ.erase x then ∑ z ∈ (univ.erase x).erase y, f x y z else 0 := by
      by_cases hxy : x = y
      · simp [hxy]
      · have hy : y ∈ univ.erase x := mem_erase.mpr ⟨Ne.symm hxy, mem_univ y⟩
        simp only [hy, ite_true, ← Finset.sum_filter]
        congr 1; ext z
        simp only [mem_filter, mem_univ, true_and, mem_erase, hxy, ne_eq, not_false_eq_true]
        tauto
    simp_rw [h1, ← Finset.sum_filter]
    congr 1; ext y; simp
  have sum_swap23 (f : I → I → I → ℚ) :
      ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, f x y z =
      ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, f x z y := by
    rw [sum_T3_eq, sum_T3_eq]
    refine Finset.sum_bij (fun w _ => (w.1, w.2.2, w.2.1)) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [T3, mem_filter, mem_univ, true_and] at hw ⊢
      exact ⟨hw.2.1, hw.1, hw.2.2.symm⟩
    · intro w1 _ w2 _ h
      rcases w1 with ⟨a1, b1, c1⟩; rcases w2 with ⟨a2, b2, c2⟩
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1, h.2.2, h.2.1⟩
    · intro w hw
      refine ⟨(w.1, w.2.2, w.2.1), ?_, by rcases w with ⟨_,_,_⟩; rfl⟩
      simp only [T3, mem_filter, mem_univ, true_and] at hw ⊢
      exact ⟨hw.2.1, hw.1, hw.2.2.symm⟩
    · intro w _; rfl
  have sum_swap12 (f : I → I → I → ℚ) :
      ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, f x y z =
      ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, f y x z := by
    rw [sum_T3_eq, sum_T3_eq]
    refine Finset.sum_bij (fun w _ => (w.2.1, w.1, w.2.2)) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [T3, mem_filter, mem_univ, true_and] at hw ⊢
      exact ⟨hw.1.symm, hw.2.2, hw.2.1⟩
    · intro w1 _ w2 _ h
      rcases w1 with ⟨a1, b1, c1⟩; rcases w2 with ⟨a2, b2, c2⟩
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.2.1, h.1, h.2.2⟩
    · intro w hw
      refine ⟨(w.2.1, w.1, w.2.2), ?_, by rcases w with ⟨_,_,_⟩; rfl⟩
      simp only [T3, mem_filter, mem_univ, true_and] at hw ⊢
      exact ⟨hw.1.symm, hw.2.2, hw.2.1⟩
    · intro w _; rfl
  -- Orthogonality kills all lower-degree terms in `∑ a^2`!
  have hkill_xy : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, a x y z * deg2 S x y = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y hy => ?_
    rw [← Finset.sum_mul, hzero (mem_erase.mp hy).1.symm, zero_mul]
  have hkill_xz : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, a x y z * deg2 S x z = 0 := by
    rw [sum_swap23]
    simp_rw [← ha_swap23]
    exact hkill_xy
  have hkill_yz : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, a x y z * deg2 S y z = 0 := by
    rw [sum_swap12]
    simp_rw [← ha_swap12]
    exact hkill_xz
  have hkill_x : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, a x y z * deg1 S x = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y hy => ?_
    rw [← Finset.sum_mul, hzero (mem_erase.mp hy).1.symm, zero_mul]
  have hkill_y : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, a x y z * deg1 S y = 0 := by
    rw [sum_swap12]
    simp_rw [← ha_swap12]
    exact hkill_x
  have hkill_z : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, a x y z * deg1 S z = 0 := by
    rw [sum_swap23]
    simp_rw [← ha_swap23]
    exact hkill_y
  have hkill_1 : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, a x y z = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y hy => ?_
    exact hzero (mem_erase.mp hy).1.symm
  have hsq : 0 ≤ ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, a x y z ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun z _ => sq_nonneg _
  have horth :
      ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, a x y z ^ 2 =
      ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z * a x y z := by
    have hterm (x y z : I) : a x y z ^ 2 =
        deg3 S x y z * a x y z -
          α2 * (a x y z * deg2 S x y) - α2 * (a x y z * deg2 S x z) - α2 * (a x y z * deg2 S y z) +
          α1 * (a x y z * deg1 S x) + α1 * (a x y z * deg1 S y) + α1 * (a x y z * deg1 S z) -
          α0 * m * a x y z := by
      dsimp [a]; ring
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hkill_xy, hkill_xz, hkill_yz, hkill_x, hkill_y, hkill_z, hkill_1]
    ring
  -- Evaluate the surviving cross terms against `deg3`
  have h3_xy : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z * deg2 S x y =
      ((t : ℚ) - 2) * ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - 1) := by
    have hxy (x : I) (y : I) (hy : y ∈ univ.erase x) :
        ∑ z ∈ (univ.erase x).erase y, deg3 S x y z * deg2 S x y = ((t : ℚ) - 2) * deg2 S x y ^ 2 := by
      rw [← Finset.sum_mul, sum_deg3_inner S ht (mem_erase.mp hy).1.symm]; ring
    have h1 (x : I) :
        ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z * deg2 S x y =
        ((t : ℚ) - 2) * ∑ y ∈ univ.erase x, deg2 S x y ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y hy => hxy x y hy
    simp_rw [h1, ← Finset.mul_sum, sum_deg2_sq]
  have h3_xz : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z * deg2 S x z =
      ((t : ℚ) - 2) * ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - 1) := by
    rw [sum_swap23]; simp_rw [← hd3_swap23]; exact h3_xy
  have h3_yz : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z * deg2 S y z =
      ((t : ℚ) - 2) * ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - 1) := by
    rw [sum_swap12]; simp_rw [← hd3_swap12]; exact h3_xz
  have h3_x : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z * deg1 S x =
      ((t : ℚ) - 1) * ((t : ℚ) - 2) * ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) := by
    have hxy (x : I) (y : I) (hy : y ∈ univ.erase x) :
        ∑ z ∈ (univ.erase x).erase y, deg3 S x y z * deg1 S x = ((t : ℚ) - 2) * (deg2 S x y * deg1 S x) := by
      rw [← Finset.sum_mul, sum_deg3_inner S ht (mem_erase.mp hy).1.symm]; ring
    have h1 (x : I) :
        ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z * deg1 S x =
        ((t : ℚ) - 1) * ((t : ℚ) - 2) * deg1 S x ^ 2 := by
      have h2 : ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z * deg1 S x =
          ((t : ℚ) - 2) * ((∑ y ∈ univ.erase x, deg2 S x y) * deg1 S x) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y hy => hxy x y hy
      rw [h2, sum_deg2_inner S ht x]; ring
    simp_rw [h1, ← Finset.mul_sum, sum_deg1_sq]
  have h3_y : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z * deg1 S y =
      ((t : ℚ) - 1) * ((t : ℚ) - 2) * ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) := by
    rw [sum_swap12]; simp_rw [← hd3_swap12]; exact h3_x
  have h3_z : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z * deg1 S z =
      ((t : ℚ) - 1) * ((t : ℚ) - 2) * ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) := by
    rw [sum_swap23]; simp_rw [← hd3_swap23]; exact h3_y
  have h3_1 : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z =
      (m : ℚ) * t * ((t : ℚ) - 1) * ((t : ℚ) - 2) := by
    have h1 (x : I) :
        ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z =
        ((t : ℚ) - 2) * (((t : ℚ) - 1) * deg1 S x) := by
      have h2 : ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z =
          ((t : ℚ) - 2) * ∑ y ∈ univ.erase x, deg2 S x y := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y hy => sum_deg3_inner S ht (mem_erase.mp hy).1.symm
      rw [h2, sum_deg2_inner S ht x]
    simp_rw [h1, ← Finset.mul_sum, sum_deg1 S ht]
    ring
  have hval : ∑ x : I, ∑ y ∈ univ.erase x, ∑ z ∈ (univ.erase x).erase y, deg3 S x y z * a x y z =
      6 * ∑ i : Fin m, ∑ j : Fin m, P3 n t ((S i ∩ S j).card) := by
    have hterm (x y z : I) : deg3 S x y z * a x y z =
        deg3 S x y z ^ 2 -
          α2 * (deg3 S x y z * deg2 S x y) - α2 * (deg3 S x y z * deg2 S x z) -
          α2 * (deg3 S x y z * deg2 S y z) +
          α1 * (deg3 S x y z * deg1 S x) + α1 * (deg3 S x y z * deg1 S y) +
          α1 * (deg3 S x y z * deg1 S z) -
          α0 * m * deg3 S x y z := by
      dsimp [a]; ring
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_deg3_sq, h3_xy, h3_xz, h3_yz, h3_x, h3_y, h3_z, h3_1]
    simp only [P3, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hdiv6 : ∑ i : Fin m, ∑ j : Fin m,
        ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - 1) * (((S i ∩ S j).card : ℚ) - 2) / 6 =
      (∑ i : Fin m, ∑ j : Fin m,
        ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - 1) * (((S i ∩ S j).card : ℚ) - 2)) / 6 := by
      simp_rw [← Finset.sum_div]
    have hdiv2 : ∑ i : Fin m, ∑ j : Fin m,
        ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - 1) / 2 =
      (∑ i : Fin m, ∑ j : Fin m,
        ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - 1)) / 2 := by
      simp_rw [← Finset.sum_div]
    rw [hdiv6, hdiv2]
    dsimp [α2, α1, α0]
    field_simp [hn2, hn3, hn4]
    ring
  rw [horth, hval] at hsq
  simpa only [n] using (by linarith : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, P3 n t ((S i ∩ S j).card))

end ElementaryHahn

section MasterBounds

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Exact Hahn coefficient `c₁` of `s * (s - d) = c₀ + c₁ P₁ + 2 P₂`. -/
def quadC1 (n t d : ℚ) : ℚ :=
  2 * (t - 1) ^ 2 / (n - 2) + 1 - d

/-- Exact Hahn constant `c₀` of `s * (s - d) = c₀ + c₁ P₁ + 2 P₂`. -/
def quadC0 (n t d : ℚ) : ℚ :=
  quadC1 n t d * (t ^ 2 / n) - t ^ 2 * (t - 1) ^ 2 / ((n - 1) * (n - 2))

theorem quad_poly_eq (n t d s : ℚ) (hn : n ≠ 0) (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0) :
    s * (s - d) = quadC0 n t d + quadC1 n t d * P1 n t s + 2 * P2 n t s := by
  unfold quadC0 quadC1 P1 P2
  field_simp [hn, hn1, hn2]
  ring

/-- Quadratic Hahn constant-weight block bound (using `P₁, P₂` and `s * (s - d) ≤ 0` for `0 ≤ s ≤ d`). -/
theorem quadratic_hahn_block_bound {m t d : ℕ} (S : Fin m → Finset I)
    (hn : 3 ≤ Fintype.card I) (hdt : d ≤ t) (ht : ∀ i, (S i).card = t)
    (hpair : Pairwise fun i j => (S i ∩ S j).card ≤ d)
    (hc1 : 0 ≤ quadC1 (Fintype.card I) t d) :
    (m : ℚ) * quadC0 (Fintype.card I) t d ≤ (t : ℚ) * ((t : ℚ) - d) := by
  by_cases hm : m = 0
  · subst hm
    have hdt' : (d : ℚ) ≤ t := by exact_mod_cast hdt
    simpa using mul_nonneg (Nat.cast_nonneg t) (by linarith : 0 ≤ (t : ℚ) - d)
  · let n : ℚ := Fintype.card I
    have hn_ge : (3 : ℚ) ≤ n := by dsimp [n]; exact_mod_cast hn
    have hn0 : n ≠ 0 := by linarith
    have hn1 : n - 1 ≠ 0 := by linarith
    have hn2 : n - 2 ≠ 0 := by linarith
    have hP1 := sum_P1_nonneg S (by omega) ht
    have hP2 := sum_P2_nonneg S hn ht
    have hlow : (m : ℚ) ^ 2 * quadC0 n t d ≤
        ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - d) := by
      have hid : ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - d) =
          (m : ℚ) ^ 2 * quadC0 n t d +
          quadC1 n t d * (∑ i : Fin m, ∑ j : Fin m, P1 n t ((S i ∩ S j).card)) +
          2 * (∑ i : Fin m, ∑ j : Fin m, P2 n t ((S i ∩ S j).card)) := by
        simp_rw [quad_poly_eq n t d _ hn0 hn1 hn2, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      rw [hid]
      nlinarith
    have hhi : ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - d) ≤
        (m : ℚ) * ((t : ℚ) * ((t : ℚ) - d)) := by
      have hrow (i : Fin m) :
          ∑ j : Fin m, ((S i ∩ S j).card : ℚ) * (((S i ∩ S j).card : ℚ) - d) ≤
            (t : ℚ) * ((t : ℚ) - d) := by
        rw [← Finset.add_sum_erase univ _ (mem_univ i), inter_self, ht i]
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
    have hmpos : (0 : ℚ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    nlinarith

/-- Exact Hahn coefficient `c₂` of `(s - d) * (s - r₀)² = c₀ + c₁ P₁ + c₂ P₂ + 6 P₃`. -/
def cubicC2 (n t d r0 : ℚ) : ℚ :=
  2 * (3 + 3 * (t - 2) ^ 2 / (n - 4) - d - 2 * r0)

/-- Exact Hahn coefficient `c₁` of `(s - d) * (s - r₀)² = c₀ + c₁ P₁ + c₂ P₂ + 6 P₃`. -/
def cubicC1 (n t d r0 : ℚ) : ℚ :=
  2 * d * r0 + r0 ^ 2 - cubicC2 n t d r0 * (-(1 / 2 : ℚ) - (t - 1) ^ 2 / (n - 2)) -
    (2 + 3 * (t - 2) ^ 2 / (n - 4) + 3 * (t - 1) ^ 2 * (t - 2) ^ 2 / ((n - 3) * (n - 4)))

/-- Exact Hahn constant `c₀` of `(s - d) * (s - r₀)² = c₀ + c₁ P₁ + c₂ P₂ + 6 P₃`. -/
def cubicC0 (n t d r0 : ℚ) : ℚ :=
  -d * r0 ^ 2 + cubicC1 n t d r0 * (t ^ 2 / n) -
    cubicC2 n t d r0 * (t ^ 2 * (t - 1) ^ 2 / (2 * (n - 1) * (n - 2))) +
    t ^ 2 * (t - 1) ^ 2 * (t - 2) ^ 2 / ((n - 2) * (n - 3) * (n - 4))

theorem cubic_poly_eq (n t d r0 s : ℚ) (hn : n ≠ 0) (hn1 : n - 1 ≠ 0) (hn2 : n - 2 ≠ 0)
    (hn3 : n - 3 ≠ 0) (hn4 : n - 4 ≠ 0) :
    (s - d) * (s - r0) ^ 2 =
      cubicC0 n t d r0 + cubicC1 n t d r0 * P1 n t s +
        cubicC2 n t d r0 * P2 n t s + 6 * P3 n t s := by
  unfold cubicC0 cubicC1 cubicC2 P1 P2 P3
  field_simp [hn, hn1, hn2, hn3, hn4]
  ring

/-- Cubic Hahn constant-weight block bound: for any `r₀ : ℚ` with nonnegative Hahn
coefficients `c₁, c₂ ≥ 0` and `c₀ > 0`, `m * c₀ ≤ (t - d) * (t - r₀)²`. -/
theorem cubic_hahn_block_bound {m t d : ℕ} (S : Fin m → Finset I)
    (hn : 5 ≤ Fintype.card I) (hdt : d ≤ t) (ht : ∀ i, (S i).card = t)
    (hpair : Pairwise fun i j => (S i ∩ S j).card ≤ d) (r0 : ℚ)
    (hc1 : 0 ≤ cubicC1 (Fintype.card I) t d r0)
    (hc2 : 0 ≤ cubicC2 (Fintype.card I) t d r0) :
    (m : ℚ) * cubicC0 (Fintype.card I) t d r0 ≤ ((t : ℚ) - d) * ((t : ℚ) - r0) ^ 2 := by
  by_cases hm : m = 0
  · subst hm
    have hdt' : (d : ℚ) ≤ t := by exact_mod_cast hdt
    simpa using mul_nonneg (by linarith : 0 ≤ (t : ℚ) - d) (sq_nonneg ((t : ℚ) - r0))
  · let n : ℚ := Fintype.card I
    have hn_ge : (5 : ℚ) ≤ n := by dsimp [n]; exact_mod_cast hn
    have hn0 : n ≠ 0 := by linarith
    have hn1 : n - 1 ≠ 0 := by linarith
    have hn2 : n - 2 ≠ 0 := by linarith
    have hn3 : n - 3 ≠ 0 := by linarith
    have hn4 : n - 4 ≠ 0 := by linarith
    have hP1 := sum_P1_nonneg S (by omega) ht
    have hP2 := sum_P2_nonneg S (by omega) ht
    have hP3 := sum_P3_nonneg S hn ht
    have hlow : (m : ℚ) ^ 2 * cubicC0 n t d r0 ≤
        ∑ i : Fin m, ∑ j : Fin m,
          (((S i ∩ S j).card : ℚ) - d) * (((S i ∩ S j).card : ℚ) - r0) ^ 2 := by
      have hid : ∑ i : Fin m, ∑ j : Fin m,
          (((S i ∩ S j).card : ℚ) - d) * (((S i ∩ S j).card : ℚ) - r0) ^ 2 =
          (m : ℚ) ^ 2 * cubicC0 n t d r0 +
          cubicC1 n t d r0 * (∑ i : Fin m, ∑ j : Fin m, P1 n t ((S i ∩ S j).card)) +
          cubicC2 n t d r0 * (∑ i : Fin m, ∑ j : Fin m, P2 n t ((S i ∩ S j).card)) +
          6 * (∑ i : Fin m, ∑ j : Fin m, P3 n t ((S i ∩ S j).card)) := by
        simp_rw [cubic_poly_eq n t d r0 _ hn0 hn1 hn2 hn3 hn4, Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      rw [hid]
      nlinarith
    have hhi : ∑ i : Fin m, ∑ j : Fin m,
        (((S i ∩ S j).card : ℚ) - d) * (((S i ∩ S j).card : ℚ) - r0) ^ 2 ≤
        (m : ℚ) * (((t : ℚ) - d) * ((t : ℚ) - r0) ^ 2) := by
      have hrow (i : Fin m) :
          ∑ j : Fin m, (((S i ∩ S j).card : ℚ) - d) * (((S i ∩ S j).card : ℚ) - r0) ^ 2 ≤
            ((t : ℚ) - d) * ((t : ℚ) - r0) ^ 2 := by
        rw [← Finset.add_sum_erase univ _ (mem_univ i), inter_self, ht i]
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
    have hmpos : (0 : ℚ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    nlinarith

omit [DecidableEq I] in
/-- Transfer the Quadratic Hahn bound directly to interleaved Reed–Solomon lists
over any field, any injective domain, and any interleaving width. -/
theorem list_le_of_quadratic_hahn {F : Type*} [Field F] [Nonempty I] (D : I ↪ F)
    (k t width B : ℕ) (δ : ℝ) (hn : 3 ≤ Fintype.card I) (hdt : k - 1 ≤ t)
    (hδ : δ * (Fintype.card I : ℝ) < (Fintype.card I : ℝ) - t + 1)
    (hc0 : 0 < quadC0 (Fintype.card I) t ((k - 1 : ℕ) : ℚ))
    (hc1 : 0 ≤ quadC1 (Fintype.card I) t ((k - 1 : ℕ) : ℚ))
    (hbudget : (t : ℚ) * ((t : ℚ) - ((k - 1 : ℕ) : ℚ)) <
      ((B + 1 : ℕ) : ℚ) * quadC0 (Fintype.card I) t ((k - 1 : ℕ) : ℚ)) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code D k : Set (I → F))) δ ≤ B := by
  classical
  apply interleaved_lambda_le_of_block_bound D k t width B δ hδ
  intro m S hw hp
  by_contra! hm
  have hq := quadratic_hahn_block_bound S hn hdt hw hp hc1
  have hB : ((B + 1 : ℕ) : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hmul : ((B + 1 : ℕ) : ℚ) * quadC0 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) ≤
      (m : ℚ) * quadC0 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) :=
    mul_le_mul_of_nonneg_right hB hc0.le
  linarith

omit [DecidableEq I] in
/-- Transfer the Cubic Hahn bound directly to interleaved Reed–Solomon lists
over any field, any injective domain, and any interleaving width. -/
theorem list_le_of_cubic_hahn {F : Type*} [Field F] [Nonempty I] (D : I ↪ F)
    (k t width B : ℕ) (δ : ℝ) (r0 : ℚ) (hn : 5 ≤ Fintype.card I) (hdt : k - 1 ≤ t)
    (hδ : δ * (Fintype.card I : ℝ) < (Fintype.card I : ℝ) - t + 1)
    (hc0 : 0 < cubicC0 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) r0)
    (hc1 : 0 ≤ cubicC1 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) r0)
    (hc2 : 0 ≤ cubicC2 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) r0)
    (hbudget : ((t : ℚ) - ((k - 1 : ℕ) : ℚ)) * ((t : ℚ) - r0) ^ 2 <
      ((B + 1 : ℕ) : ℚ) * cubicC0 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) r0) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code D k : Set (I → F))) δ ≤ B := by
  classical
  apply interleaved_lambda_le_of_block_bound D k t width B δ hδ
  intro m S hw hp
  have hq := cubic_hahn_block_bound S hn hdt hw hp r0 hc1 hc2
  by_contra! hm
  have hB : ((B + 1 : ℕ) : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hmul : ((B + 1 : ℕ) : ℚ) * cubicC0 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) r0 ≤
      (m : ℚ) * cubicC0 (Fintype.card I) t ((k - 1 : ℕ) : ℚ) r0 :=
    mul_le_mul_of_nonneg_right hB hc0.le
  linarith

end MasterBounds

section ProductionCertificates

private theorem atErrors_of_cubic {F : Type*} [Field F] (D : Fin 1073741824 ↪ F)
    (width k e t B : ℕ) (r0 : ℚ) (he : e + t = 1073741824) (hdt : k - 1 ≤ t)
    (hc0 : 0 < cubicC0 1073741824 t ((k - 1 : ℕ) : ℚ) r0)
    (hc1 : 0 ≤ cubicC1 1073741824 t ((k - 1 : ℕ) : ℚ) r0)
    (hc2 : 0 ≤ cubicC2 1073741824 t ((k - 1 : ℕ) : ℚ) r0)
    (hbudget : ((t : ℚ) - ((k - 1 : ℕ) : ℚ)) * ((t : ℚ) - r0) ^ 2 <
      ((B + 1 : ℕ) : ℚ) * cubicC0 1073741824 t ((k - 1 : ℕ) : ℚ) r0) :
    AtErrors D width k e B := by
  apply list_le_of_cubic_hahn D k t width B ((e : ℝ) / 1073741824) r0
    (by simp) hdt _ (by simpa using hc0) (by simpa using hc1) (by simpa using hc2)
    (by simpa using hbudget)
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  have hsum : (e : ℝ) + t = 1073741824 := by exact_mod_cast he
  linarith

private theorem atErrors_of_quadratic {F : Type*} [Field F] (D : Fin 1073741824 ↪ F)
    (width k e t B : ℕ) (he : e + t = 1073741824) (hdt : k - 1 ≤ t)
    (hc0 : 0 < quadC0 1073741824 t ((k - 1 : ℕ) : ℚ))
    (hc1 : 0 ≤ quadC1 1073741824 t ((k - 1 : ℕ) : ℚ))
    (hbudget : (t : ℚ) * ((t : ℚ) - ((k - 1 : ℕ) : ℚ)) <
      ((B + 1 : ℕ) : ℚ) * quadC0 1073741824 t ((k - 1 : ℕ) : ℚ)) :
    AtErrors D width k e B := by
  apply list_le_of_quadratic_hahn D k t width B ((e : ℝ) / 1073741824)
    (by simp) hdt _ (by simpa using hc0) (by simpa using hc1) (by simpa using hbudget)
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  have hsum : (e : ℝ) + t = 1073741824 := by exact_mod_cast he
  linarith

/-- Rate 1/2, first step beyond Johnson (`314,491,700` errors): list size `≤ 4,251,066,562`
(`3.96n`, 10× tighter than `MultipleOmissionJohnson`'s `40n`). -/
theorem rate_half_johnson_plus_one {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 536870912 314491700 4251066562 :=
  atErrors_of_cubic D width 536870912 314491700 759250124 4251066562 461720310
    (by decide) (by decide)
    (by norm_num [cubicC0, cubicC1, cubicC2])
    (by norm_num [cubicC1, cubicC2])
    (by norm_num [cubicC2])
    (by norm_num [cubicC0, cubicC1, cubicC2])

/-- Rate 1/2, second step beyond Johnson (`314,491,701` errors): list size `≤ 11,583,034,964`
(`10.79n`, 147× tighter than multiple omissions). -/
theorem rate_half_johnson_plus_two {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 536870912 314491701 11583034964 :=
  atErrors_of_cubic D width 536870912 314491701 759250123 11583034964 514150268
    (by decide) (by decide)
    (by norm_num [cubicC0, cubicC1, cubicC2])
    (by norm_num [cubicC1, cubicC2])
    (by norm_num [cubicC2])
    (by norm_num [cubicC0, cubicC1, cubicC2])

/-- Rate 1/4, first step beyond Johnson (`536,870,914` errors): list size `≤ 6,442,450,994`
(`6.00n`, 5.33× tighter than `MultipleOmissionJohnson`'s `34,359,737,888`). -/
theorem rate_quarter_johnson_plus_one {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 268435456 536870914 6442450994 :=
  atErrors_of_cubic D width 268435456 536870914 536870910 6442450994 214748362
    (by decide) (by decide)
    (by norm_num [cubicC0, cubicC1, cubicC2])
    (by norm_num [cubicC1, cubicC2])
    (by norm_num [cubicC2])
    (by norm_num [cubicC0, cubicC1, cubicC2])

/-- Rate 1/4, second step beyond Johnson (`536,870,915` errors): list size `≤ 10,737,418,754`
(`10.00n`, 51× tighter than multiple omissions). -/
theorem rate_quarter_johnson_plus_two {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 268435456 536870915 10737418754 :=
  atErrors_of_cubic D width 268435456 536870915 536870909 10737418754 238609291
    (by decide) (by decide)
    (by norm_num [cubicC0, cubicC1, cubicC2])
    (by norm_num [cubicC1, cubicC2])
    (by norm_num [cubicC2])
    (by norm_num [cubicC0, cubicC1, cubicC2])

/-- Rate 1/8, first step beyond Johnson (`694,116,763` errors): pure Quadratic Hahn
(`P₁, P₂` alone, with zero puncturing) yields list size `≤ 1,931,589,822 < 2³¹`. -/
theorem rate_eighth_johnson_plus_one_quadratic {F : Type*} [Field F]
    (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 134217728 694116763 1931589822 :=
  atErrors_of_quadratic D width 134217728 694116763 379625061 1931589822
    (by decide) (by decide)
    (by norm_num [quadC0, quadC1])
    (by norm_num [quadC1])
    (by norm_num [quadC0, quadC1])

/-- Rate 1/8, second step beyond Johnson (`694,116,764` errors): list size `≤ 5,744,500,761`
(`5.35n`, 3.96× tighter than `MultipleOmissionJohnson`'s `22,759,945,996`). -/
theorem rate_eighth_johnson_plus_two {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 134217728 694116764 5744500761 :=
  atErrors_of_cubic D width 134217728 694116764 379625060 5744500761 77802029
    (by decide) (by decide)
    (by norm_num [cubicC0, cubicC1, cubicC2])
    (by norm_num [cubicC1, cubicC2])
    (by norm_num [cubicC2])
    (by norm_num [cubicC0, cubicC1, cubicC2])

/-- Rate 1/16, first step beyond Johnson (`805,306,371` errors): list size `≤ 5,010,795,150`
(`4.67n`, 2.14× tighter than `MultipleOmissionJohnson`'s `10,725,307,448`). -/
theorem rate_sixteenth_johnson_plus_one {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 67108864 805306371 5010795150 :=
  atErrors_of_cubic D width 67108864 805306371 268435453 5010795150 12201610
    (by decide) (by decide)
    (by norm_num [cubicC0, cubicC1, cubicC2])
    (by norm_num [cubicC1, cubicC2])
    (by norm_num [cubicC2])
    (by norm_num [cubicC0, cubicC1, cubicC2])

/-- Rate 1/16, second step beyond Johnson (`805,306,372` errors): list size `≤ 7,874,106,789`
(`7.33n`). -/
theorem rate_sixteenth_johnson_plus_two {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 67108864 805306372 7874106789 :=
  atErrors_of_cubic D width 67108864 805306372 268435452 7874106789 35320453
    (by decide) (by decide)
    (by norm_num [cubicC0, cubicC1, cubicC2])
    (by norm_num [cubicC1, cubicC2])
    (by norm_num [cubicC2])
    (by norm_num [cubicC0, cubicC1, cubicC2])

/-- Rate 1/2, 4,799 full integer errors strictly beyond Johnson (`314,496,498` errors):
every closed interleaved RS ball over any field and injective domain has at most
`142,046,270,429,484,896` codewords (far below 128-bit budgets such as BLS12-381). -/
theorem rate_half_super_johnson_4799 {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 536870912 314496498 142046270429484896 :=
  atErrors_of_cubic D width 536870912 314496498 759245326 142046270429484896 536857338
    (by decide) (by decide)
    (by norm_num [cubicC0, cubicC1, cubicC2])
    (by norm_num [cubicC1, cubicC2])
    (by norm_num [cubicC2])
    (by norm_num [cubicC0, cubicC1, cubicC2])

/-- Rate 1/4, 8,192 full integer errors strictly beyond Johnson (`536,879,105` errors):
every closed interleaved RS ball has at most `2,305,271,392,757,763,350` codewords. -/
theorem rate_quarter_super_johnson_8192 {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 268435456 536879105 2305271392757763350 :=
  atErrors_of_cubic D width 268435456 536879105 536862719 2305271392757763350 268419071
    (by decide) (by decide)
    (by norm_num [cubicC0, cubicC1, cubicC2])
    (by norm_num [cubicC1, cubicC2])
    (by norm_num [cubicC2])
    (by norm_num [cubicC0, cubicC1, cubicC2])

/-- Rate 1/8, 10,592 full integer errors strictly beyond Johnson (`694,127,354` errors):
every closed interleaved RS ball has at most `499,537,678,460,700,742` codewords. -/
theorem rate_eighth_super_johnson_10592 {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 134217728 694127354 499537678460700742 :=
  atErrors_of_cubic D width 134217728 694127354 379614470 499537678460700742 134202749
    (by decide) (by decide)
    (by norm_num [cubicC0, cubicC1, cubicC2])
    (by norm_num [cubicC1, cubicC2])
    (by norm_num [cubicC2])
    (by norm_num [cubicC0, cubicC1, cubicC2])

/-- Rate 1/16, 12,288 full integer errors strictly beyond Johnson (`805,318,658` errors):
every closed interleaved RS ball has at most `1,383,257,789,440,870,609` codewords. -/
theorem rate_sixteenth_super_johnson_12288 {F : Type*} [Field F]
    (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 67108864 805318658 1383257789440870609 :=
  atErrors_of_cubic D width 67108864 805318658 268423166 1383257789440870609 67096575
    (by decide) (by decide)
    (by norm_num [cubicC0, cubicC1, cubicC2])
    (by norm_num [cubicC1, cubicC2])
    (by norm_num [cubicC2])
    (by norm_num [cubicC0, cubicC1, cubicC2])

end ProductionCertificates

end ProximityGap.CubicHahnJohnson

#print axioms ProximityGap.CubicHahnJohnson.sum_P1_nonneg
#print axioms ProximityGap.CubicHahnJohnson.sum_P2_nonneg
#print axioms ProximityGap.CubicHahnJohnson.sum_P3_nonneg
#print axioms ProximityGap.CubicHahnJohnson.quadratic_hahn_block_bound
#print axioms ProximityGap.CubicHahnJohnson.cubic_hahn_block_bound
#print axioms ProximityGap.CubicHahnJohnson.list_le_of_cubic_hahn
#print axioms ProximityGap.CubicHahnJohnson.rate_half_johnson_plus_one
#print axioms ProximityGap.CubicHahnJohnson.rate_quarter_johnson_plus_one
#print axioms ProximityGap.CubicHahnJohnson.rate_eighth_johnson_plus_one_quadratic
#print axioms ProximityGap.CubicHahnJohnson.rate_eighth_johnson_plus_two
#print axioms ProximityGap.CubicHahnJohnson.rate_sixteenth_johnson_plus_one
#print axioms ProximityGap.CubicHahnJohnson.rate_half_super_johnson_4799
#print axioms ProximityGap.CubicHahnJohnson.rate_quarter_super_johnson_8192
#print axioms ProximityGap.CubicHahnJohnson.rate_eighth_super_johnson_10592
#print axioms ProximityGap.CubicHahnJohnson.rate_sixteenth_super_johnson_12288
