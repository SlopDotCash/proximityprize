/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Short interval tests for Paley discrepancy

Averaging consecutive translates of a complete interval sum gives a Paley
rectangle with an explicit boundary error. Conversely, an interval estimate at
every translate controls the rectangle on one arithmetic progression and any
partner set. -/

namespace ProximityGap.PaleyIntervalCriterion

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- Sum of the quadratic character along a unit-step interval. -/
def intervalSum (s : ZMod p) (H : ℕ) : ℤ :=
  ∑ i ∈ range H, quadraticChar (ZMod p) (s + i)

/-- The rectangle on the interval starting at `s` and the reflected interval
`0,-1,…,-(K-1)`, written with indices. -/
def rectangle (s : ZMod p) (H K : ℕ) : ℤ :=
  ∑ j ∈ range K, intervalSum (s + (j : ZMod p)) H

/-- A finite arithmetic progression, with nonzero steps injective up to length `p`. -/
def progression (s d : ZMod p) (H : ℕ) : Finset (ZMod p) :=
  (range H).image fun i : ℕ => s + d * i

private theorem prog_inj (s : ZMod p) {d : ZMod p} (hd : d ≠ 0) {H : ℕ}
    (hH : H ≤ p) : Set.InjOn (fun i : ℕ => s + d * i) ↑(range H) := by
  intro i hi j hj h
  have he : (i : ZMod p) = (j : ZMod p) := mul_left_cancel₀ hd (add_left_cancel h)
  have hi' := lt_of_lt_of_le (mem_range.mp hi) hH
  have hj' := lt_of_lt_of_le (mem_range.mp hj) hH
  simpa [ZMod.val_natCast_of_lt hi', ZMod.val_natCast_of_lt hj'] using congrArg ZMod.val he

theorem card_progression (s : ZMod p) {d : ZMod p} (hd : d ≠ 0) {H : ℕ} (hH : H ≤ p) :
    (progression s d H).card = H := by
  rw [progression, card_image_of_injOn (prog_inj s hd hH), card_range]

/-- The indexed smoothing rectangle equals the ordinary difference sum on two
finite sets, including intervals crossing zero modulo the prime. -/
theorem rectangle_eq (s : ZMod p) {H K : ℕ} (hH : H ≤ p) (hK : K ≤ p) :
    rectangle s H K =
      ∑ b ∈ progression 0 (-1) K, ∑ a ∈ progression s 1 H, quadraticChar (ZMod p) (a-b) := by
  unfold rectangle progression intervalSum
  rw [sum_image (prog_inj 0 (neg_ne_zero.mpr one_ne_zero) hK)]
  apply sum_congr rfl
  intro j _
  rw [sum_image (prog_inj s one_ne_zero hH)]
  apply sum_congr rfl
  intro i _
  congr 1
  ring

private theorem abs_char_le (x : ZMod p) : |quadraticChar (ZMod p) x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rcases quadraticChar_dichotomy hx with he | he <;> simp [he]

private theorem shift_one (s : ZMod p) (H : ℕ) :
    intervalSum (s+1) H - intervalSum s H =
      quadraticChar (ZMod p) (s+H) - quadraticChar (ZMod p) s := by
  let f (j : ℕ) := quadraticChar (ZMod p) (s+(j : ZMod p))
  have h : (∑ i ∈ range H, f (i+1)) + f 0 = (∑ i ∈ range H, f i) + f H := by
    rw [← sum_range_succ', sum_range_succ]
  simpa [intervalSum, f, Nat.cast_add, add_assoc, add_left_comm, add_comm] using
    (show (∑ i ∈ range H, f (i+1)) - (∑ i ∈ range H, f i) = f H - f 0 by omega)

private theorem shift_bound (s : ZMod p) (H j : ℕ) :
    |intervalSum (s+(j : ZMod p)) H - intervalSum s H| ≤ 2 * (j : ℤ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.cast_succ, Nat.cast_succ, ← add_assoc]
    have he := shift_one (s+(j : ZMod p)) H
    have hb := abs_sub (quadraticChar (ZMod p) (s+(j : ZMod p)+(H : ZMod p))) (quadraticChar (ZMod p) (s+(j : ZMod p)))
    have h1 := abs_char_le (s+(j : ZMod p)+(H : ZMod p))
    have h2 := abs_char_le (s+(j : ZMod p))
    have ht := abs_sub_le (intervalSum (s+(j : ZMod p)+1) H) (intervalSum (s+(j : ZMod p)) H) (intervalSum s H)
    rw [he] at ht
    omega

/-- Exact boundary error for averaging the `K` shifts in the rectangle. -/
theorem smoothing (s : ZMod p) (H K : ℕ) :
    |rectangle s H K - K * intervalSum s H| ≤ (K : ℤ) * (K - 1) := by
  have he : rectangle s H K - K * intervalSum s H =
      ∑ j ∈ range K, (intervalSum (s+(j : ZMod p)) H - intervalSum s H) := by
    simp [rectangle, sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ j ∈ range K, |intervalSum (s+(j : ZMod p)) H - intervalSum s H| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range K, 2 * (j : ℤ) := sum_le_sum fun j _ => shift_bound s H j
    _ = _ := by
      clear he
      induction K with
      | zero => simp
      | succ k ih => rw [sum_range_succ, ih, Nat.cast_succ]; ring

/-- A rectangle density bound controls the original interval, with loss `K-1`. -/
theorem interval_of_rectangle (s : ZMod p) (H : ℕ) {K : ℕ} (hK : 0 < K) {ρ : ℝ}
    (hr : |(rectangle s H K : ℝ)| ≤ ρ * H * K) :
    |(intervalSum s H : ℝ)| ≤ ρ * H + K - 1 := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have h : |(rectangle s H K : ℝ) - K * intervalSum s H| ≤ (K : ℝ) * (K - 1) := by
    exact_mod_cast smoothing s H K
  have htri := abs_sub_le ((K : ℝ) * intervalSum s H) (rectangle s H K : ℝ) 0
  rw [sub_zero, sub_zero, abs_sub_comm _ (rectangle s H K : ℝ), abs_mul, abs_of_pos hk] at htri
  apply (mul_le_mul_iff_right₀ hk).mp
  nlinarith

/-- An arbitrary partner against one progression obeys the uniform translated
interval bound, with its original constant. -/
theorem progression_partner (s : ZMod p) {d : ZMod p} (hd : d ≠ 0) {H : ℕ}
    (hH : H ≤ p) (B : Finset (ZMod p)) {M : ℝ} (hI : ∀ x : ZMod p, |(intervalSum x H : ℝ)| ≤ M) :
    |((∑ b ∈ B, ∑ a ∈ progression s d H, quadraticChar (ZMod p) (a-b) : ℤ) : ℝ)| ≤ B.card * M := by
  have he (b : ZMod p) : ∑ a ∈ progression s d H, quadraticChar (ZMod p) (a-b) =
      quadraticChar (ZMod p) d * intervalSum ((s-b)/d) H := by
    rw [progression, sum_image (prog_inj s hd hH), intervalSum, mul_sum]
    apply sum_congr rfl
    intro i _
    rw [← map_mul]
    congr 1
    field_simp
    ring
  have hs : |(quadraticChar (ZMod p) d : ℝ)| = 1 := by
    rcases quadraticChar_dichotomy hd with ha | ha <;> simp [ha]
  push_cast
  calc
    _ ≤ ∑ b ∈ B, |((∑ a ∈ progression s d H, quadraticChar (ZMod p) (a-b) : ℤ) : ℝ)| := by
      push_cast
      exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ B, M := by
      refine sum_le_sum fun b _ => ?_
      rw [he, Int.cast_mul, abs_mul, hs, one_mul]
      exact hI _
    _ = _ := by simp

/-- If the initial interval has a genuine saving and stays below the prime,
it contains a positive quadratic nonresidue. -/
theorem exists_nonresidue_of_interval {H : ℕ} (hH : H < p)
    (hs : |intervalSum (1 : ZMod p) H| < (H : ℤ)) :
    ∃ n : ℕ, 0 < n ∧ n ≤ H ∧ quadraticChar (ZMod p) (n : ZMod p) = -1 := by
  by_contra! h
  have he : intervalSum (1 : ZMod p) H = H := by
    unfold intervalSum
    calc
      _ = ∑ _ ∈ range H, (1 : ℤ) := by
        refine sum_congr rfl fun i hi => ?_
        have hi' := mem_range.mp hi
        have hj : i+1 < p := by omega
        have hn : ((i+1 : ℕ) : ZMod p) ≠ 0 := by
          intro hh
          have := congrArg ZMod.val hh
          rw [ZMod.val_natCast_of_lt hj, ZMod.val_zero] at this
          omega
        have hh := (quadraticChar_dichotomy hn).resolve_right (h (i+1) (by omega) (by omega))
        simpa [add_comm] using hh
      _ = _ := by simp
  rw [he, abs_of_nonneg (Nat.cast_nonneg _)] at hs
  exact (lt_irrefl _ hs)

/-- A single all-residue positive interval would give a perfect rectangle. -/
theorem exists_nonresidue_of_rectangle {H K : ℕ} (hsize : H+K-1 < p)
    (hs : rectangle (1 : ZMod p) H K < (H : ℤ) * K) :
    ∃ n : ℕ, 0 < n ∧ n ≤ H+K-1 ∧ quadraticChar (ZMod p) (n : ZMod p) = -1 := by
  by_contra! h
  have hp (i j : ℕ) (hi : i < H) (hj : j < K) :
      quadraticChar (ZMod p) ((1 : ZMod p) + j + i) = 1 := by
    let n := 1+j+i
    have hn₁ : 0 < n := by dsimp [n]; omega
    have hn₂ : n ≤ H+K-1 := by dsimp [n]; omega
    have hn : (n : ZMod p) ≠ 0 := by
      intro hz
      have hval := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt (lt_of_le_of_lt hn₂ hsize), ZMod.val_zero] at hval
      omega
    have he := (quadraticChar_dichotomy hn).resolve_right (h n hn₁ hn₂)
    simpa [n] using he
  have hr : rectangle (1 : ZMod p) H K = (K : ℤ) * H := by
    unfold rectangle intervalSum
    calc
      _ = ∑ j ∈ range K, ∑ _ ∈ range H, (1 : ℤ) := by
        refine sum_congr rfl fun j hj => sum_congr rfl fun i hi => ?_
        exact hp i j (mem_range.mp hi) (mem_range.mp hj)
      _ = _ := by simp
  rw [hr, mul_comm] at hs
  exact (lt_irrefl _ hs)

/-- Uniform translated interval cancellation along a specified family of primes. -/
def IntervalSaving (P : ℕ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ (q : ℕ) [Fact q.Prime], P q → N ≤ q → ∀ (s : ZMod q) (H : ℕ), H ≤ q →
      (q : ℝ) ^ ε ≤ H → |(intervalSum s H : ℝ)| ≤ C * (q : ℝ) ^ (-δ) * H

/-- Uniform cancellation on unit-step interval rectangles at every polynomial scale. -/
def RectangleSaving (P : ℕ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ (q : ℕ) [Fact q.Prime], P q → N ≤ q → ∀ (s : ZMod q) (H K : ℕ),
      H ≤ q → K ≤ q → (q : ℝ) ^ ε ≤ H → (q : ℝ) ^ ε ≤ K →
      |(rectangle s H K : ℝ)| ≤ C * (q : ℝ) ^ (-δ) * H * K

/-- At all polynomial scales, short interval rectangles and individual
translated intervals have equivalent power savings on the same prime family. -/
theorem rectangleSaving_iff_intervalSaving (P : ℕ → Prop) :
    RectangleSaving P ↔ IntervalSaving P := by
  constructor
  · intro h ε hε
    have he : 0 < ε/2 := by positivity
    obtain ⟨δ, hδ, C, hC, N, hh⟩ := h (ε/2) he
    refine ⟨min δ (ε/2), lt_min hδ he, C+1, by positivity, N, ?_⟩
    intro q hq hP hN s H hH hsize
    have hq' : 1 ≤ (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_le
    have hqp : 0 < (q : ℝ) := by linarith
    let K := ⌈(q : ℝ) ^ (ε/2)⌉₊
    have hk₁ : (q : ℝ) ^ (ε/2) ≤ K := Nat.le_ceil _
    have hk₂ : (K : ℝ) < (q : ℝ) ^ (ε/2) + 1 := Nat.ceil_lt_add_one (by positivity)
    have hhalf : (q : ℝ) ^ (ε/2) ≤ H :=
      (Real.rpow_le_rpow_of_exponent_le hq' (by linarith)).trans hsize
    have hKn : K ≤ H := Nat.ceil_le.mpr hhalf
    have hK : 0 < K := by
      have := lt_of_lt_of_le (Real.rpow_pos_of_pos hqp _) hk₁
      exact_mod_cast this
    have hr := hh q hP hN s H K hH (hKn.trans hH) hhalf hk₁
    have hi := interval_of_rectangle s H hK hr
    let d := min δ (ε/2)
    have hd₁ : (q : ℝ)^(-δ) ≤ (q : ℝ)^(-d) :=
      Real.rpow_le_rpow_of_exponent_le hq' (neg_le_neg (min_le_left ..))
    have hd₂ : (q : ℝ)^(-(ε/2)) ≤ (q : ℝ)^(-d) :=
      Real.rpow_le_rpow_of_exponent_le hq' (neg_le_neg (min_le_right ..))
    have hb : (q : ℝ)^(ε/2) ≤ (q : ℝ)^(-d)*H := calc
      _ = (q : ℝ)^(-(ε/2)) * (q : ℝ)^ε := by
        rw [← Real.rpow_add hqp]; congr 1; ring
      _ ≤ _ := mul_le_mul hd₂ hsize (by positivity) (by positivity)
    have hterm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd₁ hC)
      (Nat.cast_nonneg H)
    change _ ≤ (C+1) * (q : ℝ)^(-d) * H
    linarith [show (C+1) * (q : ℝ)^(-d) * H =
      C * (q : ℝ)^(-d) * H + (q : ℝ)^(-d) * H by ring]
  · intro h ε hε
    obtain ⟨δ, hδ, C, hC, N, hh⟩ := h ε hε
    refine ⟨δ, hδ, C, hC, N, ?_⟩
    intro q hq hP hN s H K hH hK hsize _
    have hr := progression_partner s (d := 1) one_ne_zero hH (progression 0 (-1) K)
      (fun x => hh q hP hN x H hH hsize)
    rw [← rectangle_eq s hH hK, card_progression 0 (neg_ne_zero.mpr one_ne_zero) hK] at hr
    linarith [mul_comm (K : ℝ) (C * (q : ℝ)^(-δ) * H)]

/-- One nonzero-step progression at a polynomial scale and an unrestricted partner. -/
def ProgressionSaving (P : ℕ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ (q : ℕ) [Fact q.Prime], P q → N ≤ q → ∀ (s d : ZMod q) (H : ℕ),
      d ≠ 0 → H ≤ q → (q : ℝ) ^ ε ≤ H → ∀ B : Finset (ZMod q),
      |((∑ b ∈ B, ∑ a ∈ progression s d H, quadraticChar (ZMod q) (a-b) : ℤ) : ℝ)| ≤
        C * (q : ℝ)^(-δ) * H * B.card

/-- Testing two unit-step intervals at every polynomial scale is equivalent
to obtaining a power saving with one progression against any partner. -/
theorem rectangleSaving_iff_progressionSaving (P : ℕ → Prop) :
    RectangleSaving P ↔ ProgressionSaving P := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, C, hC, N, hh⟩ := (rectangleSaving_iff_intervalSaving P).mp h ε hε
    refine ⟨δ, hδ, C, hC, N, ?_⟩
    intro q hq hP hN s d H hd hH hsize B
    exact (progression_partner s hd hH B (fun x => hh q hP hN x H hH hsize)).trans_eq
      (mul_comm _ _)
  · intro h ε hε
    obtain ⟨δ, hδ, C, hC, N, hh⟩ := h ε hε
    refine ⟨δ, hδ, C, hC, N, ?_⟩
    intro q hq hP hN s H K hH hK hsize _
    have he := hh q hP hN s 1 H one_ne_zero hH hsize (progression 0 (-1) K)
    rwa [← rectangle_eq s hH hK, card_progression 0 (neg_ne_zero.mpr one_ne_zero) hK] at he

open Filter Topology in
/-- Power saving on all interval rectangles implies Vinogradov's least
quadratic nonresidue conclusion along exactly the hypothesized prime family. -/
theorem small_nonresidue_of_rectangleSaving {P : ℕ → Prop} (h : RectangleSaving P)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (q : ℕ) [Fact q.Prime], P q → N ≤ q →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ (q : ℝ)^ε ∧ quadraticChar (ZMod q) (n : ZMod q) = -1 := by
  let α := min (ε/2) (1/2)
  have hα : 0 < α := lt_min (by positivity) (by norm_num)
  obtain ⟨δ, hδ, C, _, N, hh⟩ := (rectangleSaving_iff_intervalSaving P).mp h α hα
  have hdecay : Tendsto (fun q : ℕ => C * (q : ℝ)^(-δ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul C
  have hgrowth : Tendsto (fun q : ℕ => (q : ℝ)^α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hdecay.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num)))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hgrowth.eventually_ge_atTop 2)
  refine ⟨max N (max N₁ N₂), ?_⟩
  intro q hq hP hN
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).one_le
  have hqp : 0 < (q : ℝ) := by linarith
  have hy : 2 ≤ (q : ℝ)^α := hN₂ q (by omega)
  let H := ⌈(q : ℝ)^α⌉₊
  have hlow : (q : ℝ)^α ≤ H := Nat.le_ceil _
  have hceil : (H : ℝ) < (q : ℝ)^α + 1 := Nat.ceil_lt_add_one (by positivity)
  have hsq : (H : ℝ) < (q : ℝ)^(α+α) := by
    rw [Real.rpow_add hqp]
    nlinarith [mul_self_nonneg ((q : ℝ)^α-2)]
  have hαq : α+α ≤ 1 := by linarith [show α ≤ 1/2 from min_le_right ..]
  have hαε : α+α ≤ ε := by linarith [show α ≤ ε/2 from min_le_left ..]
  have hH : H < q := by
    have ht := hsq.trans_le (Real.rpow_le_rpow_of_exponent_le hq' hαq)
    rw [Real.rpow_one] at ht
    exact_mod_cast ht
  have hpH : (0 : ℝ) < H := by linarith
  have hb := hh q hP (by omega) (1 : ZMod q) H hH.le hlow
  have hc : C * (q : ℝ)^(-δ) < 1 := hN₁ q (by omega)
  have hstrong : |(intervalSum (1 : ZMod q) H : ℝ)| < H :=
    hb.trans_lt (by simpa using mul_lt_mul_of_pos_right hc hpH)
  obtain ⟨n, hn, hnH, hχ⟩ := exists_nonresidue_of_interval hH (by exact_mod_cast hstrong)
  exact ⟨n, hn, (by exact_mod_cast hnH : (n : ℝ) ≤ H).trans
    (hsq.le.trans (Real.rpow_le_rpow_of_exponent_le hq' hαε)), hχ⟩

end ProximityGap.PaleyIntervalCriterion

#print axioms ProximityGap.PaleyIntervalCriterion.interval_of_rectangle
#print axioms ProximityGap.PaleyIntervalCriterion.progression_partner
#print axioms ProximityGap.PaleyIntervalCriterion.exists_nonresidue_of_interval

#print axioms ProximityGap.PaleyIntervalCriterion.rectangleSaving_iff_intervalSaving
#print axioms ProximityGap.PaleyIntervalCriterion.exists_nonresidue_of_rectangle

#print axioms ProximityGap.PaleyIntervalCriterion.small_nonresidue_of_rectangleSaving

#print axioms ProximityGap.PaleyIntervalCriterion.rectangleSaving_iff_progressionSaving
