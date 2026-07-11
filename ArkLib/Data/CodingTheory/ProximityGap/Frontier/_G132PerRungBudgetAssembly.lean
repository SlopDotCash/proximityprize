/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G131PerRungDescentSeries

/-!
# G132: per-rung budget assembly — shallow and deep descent at every rung

Assembles G130's uniform gates and G131's series into the two budget theorems the per-rung
tower steps consume, for every rung `11 ≤ t ≤ 110` and every `q ≤ 2^160`:

1. `perRung_shallow_budget`: with only the trivial energy bounds, the shallow descent
   (depths `0..t−9`) fits a quarter of the rung-`t` DC mass:
   `4·q·Σ_{s<t−8} (t)_{t−s}²·n^{t−s}·E_s ≤ n^{2t}`.
2. `perRung_deep_budget`: with DC-shape bounds at the eight predecessor rungs
   (`t−8 ≤ s ≤ t−1`), the deep descent fits a quarter as well:
   `4·q·Σ_{s ∈ [t−8,t)} (t)_{t−s}²·n^{t−s}·E_s ≤ n^{2t}`.
3. `perRung_full_budget`: together, `2·q·(full rung-t overhead) ≤ n^{2t}` — half the DC mass,
   leaving half for the disjoint census in the per-rung gate.

**Honest scope.**  Arithmetic assembly; the per-rung tower step and the strong induction over
rungs is the sequel, and the census bounds are the wall.  CORE remains OPEN.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G132PerRungBudgetAssembly

open Finset
open ArkLib.ProximityGap.Frontier.G130UniformRungBudgets
open ArkLib.ProximityGap.Frontier.G131PerRungDescentSeries

/-- Descending factorials with more factors are larger (while factors stay positive). -/
theorem descFactorial_mono_len {a j k : ℕ} (hjk : j ≤ k) (hk : k ≤ a) :
    Nat.descFactorial a j ≤ Nat.descFactorial a k := by
  induction k with
  | zero =>
      have : j = 0 := by omega
      subst this
      exact le_refl _
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
      · exact le_refl _
      · have h1 := ih (by omega) (by omega)
        rw [Nat.descFactorial_succ]
        have hfac : 1 ≤ a - k := by omega
        calc
          Nat.descFactorial a j ≤ Nat.descFactorial a k := h1
          _ = 1 * Nat.descFactorial a k := (Nat.one_mul _).symm
          _ ≤ (a - k) * Nat.descFactorial a k :=
            Nat.mul_le_mul_right _ hfac

/-- Odd double factorials are monotone in the rung. -/
theorem doubleFactorial_odd_mono {s t : ℕ} (hst : s ≤ t) :
    Nat.doubleFactorial (2 * s - 1) ≤ Nat.doubleFactorial (2 * t - 1) := by
  induction t with
  | zero =>
      have : s = 0 := by omega
      subst this
      exact le_refl _
  | succ t ih =>
      rcases Nat.eq_or_lt_of_le hst with rfl | hlt
      · exact le_refl _
      · have h1 := ih (by omega)
        rcases Nat.eq_zero_or_pos t with rfl | htpos
        · -- t = 0, s = 0: compare (2·0−1)!! = 0!! = 1 with (2·1−1)!! = 1!! = 1
          have hs0 : s = 0 := by omega
          subst hs0
          simp [Nat.doubleFactorial]
        · have harg : 2 * (t + 1) - 1 = (2 * t - 1) + 2 := by omega
          calc
            Nat.doubleFactorial (2 * s - 1)
                ≤ Nat.doubleFactorial (2 * t - 1) := h1
            _ = 1 * Nat.doubleFactorial (2 * t - 1) := (Nat.one_mul _).symm
            _ ≤ (2 * t - 1 + 2) * Nat.doubleFactorial (2 * t - 1) :=
              Nat.mul_le_mul_right _ (by omega)
            _ = Nat.doubleFactorial (2 * (t + 1) - 1) := by
              rw [harg, Nat.doubleFactorial_add_two]

/-- **Per-rung shallow budget.**  For `11 ≤ t ≤ 110` and `q ≤ 2^160`, the trivial-energy
shallow descent fits a quarter of the rung-`t` DC mass. -/
theorem perRung_shallow_budget {t : ℕ} (ht11 : 11 ≤ t) (ht : t ≤ 110)
    (q : ℕ) (hq : q ≤ 2 ^ 160) (E : ℕ → ℕ) (hE0 : E 0 ≤ 1)
    (hEs : ∀ s, 1 ≤ s → E s ≤ (2 ^ 30 : ℕ) ^ (2 * s - 1)) :
    4 * (q * ∑ s ∈ Finset.range (t - 8),
        (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s))
      ≤ (2 ^ 30 : ℕ) ^ (2 * t) := by
  -- s = 0 term and the k ∈ [9, t] series
  have hpeel : t - 8 = (t - 9) + 1 := by omega
  rw [Finset.mul_sum, hpeel, Finset.sum_range_succ']
  -- eight-fold bounds on the two pieces, then halve
  have hT0 : 8 * (q * ((Nat.descFactorial t (t - 0)) ^ 2 *
      ((2 ^ 30) ^ (t - 0) * E 0)))
      ≤ (2 ^ 30 : ℕ) ^ (2 * t) := by
    have hds : Nat.descFactorial t t = Nat.factorial t := Nat.descFactorial_self t
    have hfac := factorial_sq_le t (by omega) ht
    calc
      8 * (q * ((Nat.descFactorial t (t - 0)) ^ 2 * ((2 ^ 30) ^ (t - 0) * E 0)))
          ≤ 8 * (2 ^ 160 * ((Nat.factorial t) ^ 2 * ((2 ^ 30) ^ t * 1))) := by
        simp only [Nat.sub_zero, hds]
        gcongr
      _ = (2 ^ 163 * (Nat.factorial t) ^ 2) * (2 ^ 30) ^ t := by ring
      _ ≤ 2 ^ (30 * t) * (2 ^ 30) ^ t := Nat.mul_le_mul_right _ hfac
      _ = (2 ^ 30 : ℕ) ^ t * (2 ^ 30) ^ t := by rw [pow_mul]
      _ = (2 ^ 30 : ℕ) ^ (2 * t) := by
        rw [← pow_add]
        congr 1
        omega
  have htails : 8 * ∑ i ∈ Finset.range (t - 9),
      q * ((Nat.descFactorial t (t - (i + 1))) ^ 2 *
        ((2 ^ 30) ^ (t - (i + 1)) * E (i + 1)))
      ≤ (2 ^ 30 : ℕ) ^ (2 * t) := by
    have hterm : ∀ i, i < t - 9 →
        q * ((Nat.descFactorial t (t - (i + 1))) ^ 2 *
          ((2 ^ 30) ^ (t - (i + 1)) * E (i + 1)))
          ≤ descBT t q (t - (i + 1)) := by
      intro i hi
      have hE := hEs (i + 1) (Nat.succ_le_succ (Nat.zero_le i))
      have hpow : (2 ^ 30 : ℕ) ^ (t - (i + 1)) * (2 ^ 30) ^ (2 * (i + 1) - 1)
          = (2 ^ 30) ^ (2 * t - 1 - (t - (i + 1))) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        q * ((Nat.descFactorial t (t - (i + 1))) ^ 2 *
            ((2 ^ 30) ^ (t - (i + 1)) * E (i + 1)))
            ≤ q * ((Nat.descFactorial t (t - (i + 1))) ^ 2 *
              ((2 ^ 30) ^ (t - (i + 1)) * (2 ^ 30) ^ (2 * (i + 1) - 1))) := by
          gcongr
        _ = q * (Nat.descFactorial t (t - (i + 1))) ^ 2 *
              ((2 ^ 30) ^ (t - (i + 1)) * (2 ^ 30) ^ (2 * (i + 1) - 1)) := by ring
        _ = descBT t q (t - (i + 1)) := by
          rw [hpow]
          rfl
    have hsum : ∑ i ∈ Finset.range (t - 9),
        q * ((Nat.descFactorial t (t - (i + 1))) ^ 2 *
          ((2 ^ 30) ^ (t - (i + 1)) * E (i + 1)))
        ≤ 2 * descBT t q 9 := by
      calc
        ∑ i ∈ Finset.range (t - 9),
            q * ((Nat.descFactorial t (t - (i + 1))) ^ 2 *
              ((2 ^ 30) ^ (t - (i + 1)) * E (i + 1)))
            ≤ ∑ i ∈ Finset.range (t - 9), descBT t q (t - (i + 1)) :=
          Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
        _ ≤ ∑ j ∈ Finset.range (t - 9 + 1), descBT t q (t - j) := by
          rw [Finset.sum_range_succ' (fun j => descBT t q (t - j)) (t - 9)]
          exact Nat.le_add_right _ _
        _ ≤ 2 * descBT t q (t - (t - 9)) := descBT_tail ht q (t - 9) (by omega)
        _ = 2 * descBT t q 9 := by
          congr 2
          omega
    have hB9 : 16 * descBT t q 9 ≤ (2 ^ 30 : ℕ) ^ (2 * t) := by
      have hmono : Nat.descFactorial t 9 ≤ Nat.descFactorial 110 9 :=
        descFactorial_mono_base ht
      have hexp : 2 * t - 1 - 9 = 2 * t - 10 := by omega
      calc
        16 * descBT t q 9
            = 16 * (q * (Nat.descFactorial t 9) ^ 2) * (2 ^ 30) ^ (2 * t - 1 - 9) := by
          unfold descBT
          ring
        _ ≤ 16 * (2 ^ 160 * (Nat.descFactorial 110 9) ^ 2) *
              (2 ^ 30) ^ (2 * t - 10) := by
          rw [hexp]
          gcongr
        _ ≤ 2 ^ 300 * (2 ^ 30) ^ (2 * t - 10) :=
          Nat.mul_le_mul_right _ shallow_head_gate
        _ = (2 ^ 30 : ℕ) ^ 10 * (2 ^ 30) ^ (2 * t - 10) := by
          congr 1
        _ = (2 ^ 30 : ℕ) ^ (2 * t) := by
          rw [← pow_add]
          congr 1
          omega
    calc
      8 * ∑ i ∈ Finset.range (t - 9),
          q * ((Nat.descFactorial t (t - (i + 1))) ^ 2 *
            ((2 ^ 30) ^ (t - (i + 1)) * E (i + 1)))
          ≤ 8 * (2 * descBT t q 9) := Nat.mul_le_mul_left _ hsum
      _ = 16 * descBT t q 9 := by ring
      _ ≤ (2 ^ 30 : ℕ) ^ (2 * t) := hB9
  -- combine: 8a ≤ M and 8b ≤ M give 4(a + b) ≤ M
  have hcomb : 8 * ((∑ i ∈ Finset.range (t - 9),
      q * ((Nat.descFactorial t (t - (i + 1))) ^ 2 *
        ((2 ^ 30) ^ (t - (i + 1)) * E (i + 1))))
      + q * ((Nat.descFactorial t (t - 0)) ^ 2 * ((2 ^ 30) ^ (t - 0) * E 0)))
      ≤ 2 * (2 ^ 30 : ℕ) ^ (2 * t) := by
    calc
      8 * ((∑ i ∈ Finset.range (t - 9),
          q * ((Nat.descFactorial t (t - (i + 1))) ^ 2 *
            ((2 ^ 30) ^ (t - (i + 1)) * E (i + 1))))
          + q * ((Nat.descFactorial t (t - 0)) ^ 2 * ((2 ^ 30) ^ (t - 0) * E 0)))
          = 8 * (∑ i ∈ Finset.range (t - 9),
              q * ((Nat.descFactorial t (t - (i + 1))) ^ 2 *
                ((2 ^ 30) ^ (t - (i + 1)) * E (i + 1))))
            + 8 * (q * ((Nat.descFactorial t (t - 0)) ^ 2 *
                ((2 ^ 30) ^ (t - 0) * E 0))) := by ring
      _ ≤ (2 ^ 30 : ℕ) ^ (2 * t) + (2 ^ 30 : ℕ) ^ (2 * t) :=
        Nat.add_le_add htails hT0
      _ = 2 * (2 ^ 30 : ℕ) ^ (2 * t) := (Nat.two_mul _).symm
  have : 2 * (4 * ((∑ i ∈ Finset.range (t - 9),
      q * ((Nat.descFactorial t (t - (i + 1))) ^ 2 *
        ((2 ^ 30) ^ (t - (i + 1)) * E (i + 1))))
      + q * ((Nat.descFactorial t (t - 0)) ^ 2 * ((2 ^ 30) ^ (t - 0) * E 0))))
      ≤ 2 * (2 ^ 30 : ℕ) ^ (2 * t) := by
    calc
      2 * (4 * ((∑ i ∈ Finset.range (t - 9),
          q * ((Nat.descFactorial t (t - (i + 1))) ^ 2 *
            ((2 ^ 30) ^ (t - (i + 1)) * E (i + 1))))
          + q * ((Nat.descFactorial t (t - 0)) ^ 2 * ((2 ^ 30) ^ (t - 0) * E 0))))
          = 8 * ((∑ i ∈ Finset.range (t - 9),
              q * ((Nat.descFactorial t (t - (i + 1))) ^ 2 *
                ((2 ^ 30) ^ (t - (i + 1)) * E (i + 1))))
            + q * ((Nat.descFactorial t (t - 0)) ^ 2 *
                ((2 ^ 30) ^ (t - 0) * E 0))) := by ring
      _ ≤ 2 * (2 ^ 30 : ℕ) ^ (2 * t) := hcomb
  exact Nat.le_of_mul_le_mul_left this (by norm_num)

/-- **Per-rung deep budget.**  For `11 ≤ t ≤ 110`, `q ≤ 2^160`, with DC-shape bounds at the
eight predecessor rungs, the deep descent fits a quarter of the rung-`t` DC mass. -/
theorem perRung_deep_budget {t : ℕ} (ht11 : 11 ≤ t) (ht : t ≤ 110)
    (q : ℕ) (hq : q ≤ 2 ^ 160) (E : ℕ → ℕ)
    (hDC : ∀ s, t - 8 ≤ s → s < t →
      q * E s ≤ q * (Nat.doubleFactorial (2 * s - 1) * (2 ^ 30) ^ s)
        + (2 ^ 30) ^ (2 * s)) :
    4 * (q * ∑ s ∈ Finset.Ico (t - 8) t,
        (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s))
      ≤ (2 ^ 30 : ℕ) ^ (2 * t) := by
  -- per-term: 32·q·term_s ≤ n^{2t}, via a 64× split (both G130 gates are exact at 64)
  have hterm : ∀ s ∈ Finset.Ico (t - 8) t,
      32 * (q * ((Nat.descFactorial t (t - s)) ^ 2 *
        ((2 ^ 30) ^ (t - s) * E s)))
        ≤ (2 ^ 30 : ℕ) ^ (2 * t) := by
    intro s hs
    have hs' := Finset.mem_Ico.mp hs
    have hk1 : 1 ≤ t - s := by omega
    have hk8 : t - s ≤ 8 := by omega
    have hdc := hDC s hs'.1 hs'.2
    have hdescK : Nat.descFactorial t (t - s) ≤ Nat.descFactorial 110 (t - s) :=
      descFactorial_mono_base ht
    have hdesc8 : Nat.descFactorial t (t - s) ≤ Nat.descFactorial 110 8 :=
      le_trans hdescK (descFactorial_mono_len hk8 (by norm_num))
    -- 64× split
    have hsplit : 64 * (q * ((Nat.descFactorial t (t - s)) ^ 2 *
        ((2 ^ 30) ^ (t - s) * E s)))
        ≤ 64 * ((Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) *
            (q * (Nat.doubleFactorial (2 * s - 1) * (2 ^ 30) ^ s))))
          + 64 * ((Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) *
            (2 ^ 30) ^ (2 * s))) := by
      calc
        64 * (q * ((Nat.descFactorial t (t - s)) ^ 2 *
            ((2 ^ 30) ^ (t - s) * E s)))
            = 64 * ((Nat.descFactorial t (t - s)) ^ 2 *
                ((2 ^ 30) ^ (t - s) * (q * E s))) := by ring
        _ ≤ 64 * ((Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) *
              (q * (Nat.doubleFactorial (2 * s - 1) * (2 ^ 30) ^ s)
                + (2 ^ 30) ^ (2 * s)))) := by
          gcongr
        _ = 64 * ((Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) *
              (q * (Nat.doubleFactorial (2 * s - 1) * (2 ^ 30) ^ s))))
            + 64 * ((Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) *
              (2 ^ 30) ^ (2 * s))) := by ring
    -- Wick half at 64×: exact fit of deep_wick_le (64 · 2^160 = 2^166)
    have hwick : 64 * ((Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) *
        (q * (Nat.doubleFactorial (2 * s - 1) * (2 ^ 30) ^ s))))
        ≤ (2 ^ 30 : ℕ) ^ (2 * t) := by
      have hdf : Nat.doubleFactorial (2 * s - 1)
          ≤ Nat.doubleFactorial (2 * t - 1) :=
        doubleFactorial_odd_mono (le_of_lt hs'.2)
      have hwl := deep_wick_le t ht11 ht
      have hpow : (2 ^ 30 : ℕ) ^ (t - s) * (2 ^ 30) ^ s = (2 ^ 30) ^ t := by
        rw [← pow_add]
        congr 1
        omega
      have hpowt : (2 ^ 30 : ℕ) ^ t * (2 ^ 30) ^ t = (2 ^ 30 : ℕ) ^ (2 * t) := by
        rw [← pow_add]
        congr 1
        ring
      calc
        64 * ((Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) *
            (q * (Nat.doubleFactorial (2 * s - 1) * (2 ^ 30) ^ s))))
            = (64 * q * (Nat.descFactorial t (t - s)) ^ 2 *
                Nat.doubleFactorial (2 * s - 1)) *
              ((2 ^ 30) ^ (t - s) * (2 ^ 30) ^ s) := by ring
        _ ≤ (2 ^ 166 * (Nat.descFactorial 110 8) ^ 2 *
              Nat.doubleFactorial (2 * t - 1)) * (2 ^ 30) ^ t := by
          rw [hpow]
          have h64q : 64 * q ≤ 2 ^ 166 := by
            calc
              64 * q ≤ 64 * 2 ^ 160 := Nat.mul_le_mul_left _ hq
              _ = 2 ^ 166 := by norm_num
          exact Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.mul_le_mul h64q (Nat.pow_le_pow_left hdesc8 2)) hdf)
            (le_refl _)
        _ ≤ 2 ^ (30 * t) * (2 ^ 30) ^ t := Nat.mul_le_mul_right _ hwl
        _ = (2 ^ 30 : ℕ) ^ t * (2 ^ 30) ^ t := by rw [pow_mul]
        _ = (2 ^ 30 : ℕ) ^ (2 * t) := hpowt
    -- DC half at 64×: exact fit of deep_dc_gate
    have hdcpart : 64 * ((Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) *
        (2 ^ 30) ^ (2 * s)))
        ≤ (2 ^ 30 : ℕ) ^ (2 * t) := by
      have hgate := deep_dc_gate (t - s) hk1 hk8
      have hlead : 64 * (Nat.descFactorial t (t - s)) ^ 2
          ≤ (2 ^ 30 : ℕ) ^ (t - s) := by
        calc
          64 * (Nat.descFactorial t (t - s)) ^ 2
              ≤ 64 * (Nat.descFactorial 110 (t - s)) ^ 2 := by gcongr
          _ ≤ 2 ^ (30 * (t - s)) := hgate
          _ = (2 ^ 30 : ℕ) ^ (t - s) := by rw [← pow_mul]
      calc
        64 * ((Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) *
            (2 ^ 30) ^ (2 * s)))
            = (64 * (Nat.descFactorial t (t - s)) ^ 2) *
              ((2 ^ 30) ^ (t - s) * (2 ^ 30) ^ (2 * s)) := by ring
        _ ≤ (2 ^ 30 : ℕ) ^ (t - s) *
              ((2 ^ 30) ^ (t - s) * (2 ^ 30) ^ (2 * s)) :=
          Nat.mul_le_mul_right _ hlead
        _ = (2 ^ 30 : ℕ) ^ ((t - s) + ((t - s) + 2 * s)) := by
          rw [pow_add, pow_add]
        _ ≤ (2 ^ 30 : ℕ) ^ (2 * t) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
    -- combine and halve
    have h64 : 64 * (q * ((Nat.descFactorial t (t - s)) ^ 2 *
        ((2 ^ 30) ^ (t - s) * E s)))
        ≤ 2 * (2 ^ 30 : ℕ) ^ (2 * t) := by
      calc
        64 * (q * ((Nat.descFactorial t (t - s)) ^ 2 *
            ((2 ^ 30) ^ (t - s) * E s)))
            ≤ 64 * ((Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) *
                (q * (Nat.doubleFactorial (2 * s - 1) * (2 ^ 30) ^ s))))
              + 64 * ((Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) *
                (2 ^ 30) ^ (2 * s))) := hsplit
        _ ≤ (2 ^ 30 : ℕ) ^ (2 * t) + (2 ^ 30 : ℕ) ^ (2 * t) :=
          Nat.add_le_add hwick hdcpart
        _ = 2 * (2 ^ 30 : ℕ) ^ (2 * t) := (Nat.two_mul _).symm
    have h32 : 2 * (32 * (q * ((Nat.descFactorial t (t - s)) ^ 2 *
        ((2 ^ 30) ^ (t - s) * E s))))
        ≤ 2 * (2 ^ 30 : ℕ) ^ (2 * t) := by
      calc
        2 * (32 * (q * ((Nat.descFactorial t (t - s)) ^ 2 *
            ((2 ^ 30) ^ (t - s) * E s))))
            = 64 * (q * ((Nat.descFactorial t (t - s)) ^ 2 *
              ((2 ^ 30) ^ (t - s) * E s))) := by ring
        _ ≤ 2 * (2 ^ 30 : ℕ) ^ (2 * t) := h64
    exact Nat.le_of_mul_le_mul_left h32 (by norm_num)
  -- sum the eight terms: 32·Σ ≤ 8·n^{2t}, then cancel 8
  have hcard : (Finset.Ico (t - 8) t).card = 8 := by
    rw [Nat.card_Ico]
    omega
  have hsum32 : 32 * (q * ∑ s ∈ Finset.Ico (t - 8) t,
      (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s))
      ≤ 8 * (2 ^ 30 : ℕ) ^ (2 * t) := by
    calc
      32 * (q * ∑ s ∈ Finset.Ico (t - 8) t,
          (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s))
          = ∑ s ∈ Finset.Ico (t - 8) t,
              32 * (q * ((Nat.descFactorial t (t - s)) ^ 2 *
                ((2 ^ 30) ^ (t - s) * E s))) := by
        rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ ∑ _s ∈ Finset.Ico (t - 8) t, (2 ^ 30 : ℕ) ^ (2 * t) :=
        Finset.sum_le_sum hterm
      _ = 8 * (2 ^ 30 : ℕ) ^ (2 * t) := by
        rw [Finset.sum_const, hcard, smul_eq_mul]
  have hfinal : 8 * (4 * (q * ∑ s ∈ Finset.Ico (t - 8) t,
      (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s)))
      ≤ 8 * (2 ^ 30 : ℕ) ^ (2 * t) := by
    calc
      8 * (4 * (q * ∑ s ∈ Finset.Ico (t - 8) t,
          (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s)))
          = 32 * (q * ∑ s ∈ Finset.Ico (t - 8) t,
            (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s)) := by
        ring
      _ ≤ 8 * (2 ^ 30 : ℕ) ^ (2 * t) := hsum32
  exact Nat.le_of_mul_le_mul_left hfinal (by norm_num)

/-- **Per-rung full budget.**  Shallow plus deep: with DC-shape bounds at the eight
predecessor rungs, the FULL rung-`t` descent overhead fits half the DC mass. -/
theorem perRung_full_budget {t : ℕ} (ht11 : 11 ≤ t) (ht : t ≤ 110)
    (q : ℕ) (hq : q ≤ 2 ^ 160) (E : ℕ → ℕ) (hE0 : E 0 ≤ 1)
    (hEs : ∀ s, 1 ≤ s → E s ≤ (2 ^ 30 : ℕ) ^ (2 * s - 1))
    (hDC : ∀ s, t - 8 ≤ s → s < t →
      q * E s ≤ q * (Nat.doubleFactorial (2 * s - 1) * (2 ^ 30) ^ s)
        + (2 ^ 30) ^ (2 * s)) :
    2 * (q * ∑ s ∈ Finset.range t,
        (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s))
      ≤ (2 ^ 30 : ℕ) ^ (2 * t) := by
  have hsplit : ∑ s ∈ Finset.range t,
      (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s)
      = (∑ s ∈ Finset.range (t - 8),
          (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s))
        + ∑ s ∈ Finset.Ico (t - 8) t,
            (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le (t - 8)) (by omega)).symm
  have hshallow := perRung_shallow_budget ht11 ht q hq E hE0 hEs
  have hdeep := perRung_deep_budget ht11 ht q hq E hDC
  have h4 : 4 * (q * ∑ s ∈ Finset.range t,
      (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s))
      ≤ 2 * (2 ^ 30 : ℕ) ^ (2 * t) := by
    calc
      4 * (q * ∑ s ∈ Finset.range t,
          (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s))
          = 4 * (q * ∑ s ∈ Finset.range (t - 8),
              (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s))
            + 4 * (q * ∑ s ∈ Finset.Ico (t - 8) t,
              (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s)) := by
        rw [hsplit]
        ring
      _ ≤ (2 ^ 30 : ℕ) ^ (2 * t) + (2 ^ 30 : ℕ) ^ (2 * t) :=
        Nat.add_le_add hshallow hdeep
      _ = 2 * (2 ^ 30 : ℕ) ^ (2 * t) := (Nat.two_mul _).symm
  have h2 : 2 * (2 * (q * ∑ s ∈ Finset.range t,
      (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s)))
      ≤ 2 * (2 ^ 30 : ℕ) ^ (2 * t) := by
    calc
      2 * (2 * (q * ∑ s ∈ Finset.range t,
          (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s)))
          = 4 * (q * ∑ s ∈ Finset.range t,
            (Nat.descFactorial t (t - s)) ^ 2 * ((2 ^ 30) ^ (t - s) * E s)) := by
        ring
      _ ≤ 2 * (2 ^ 30 : ℕ) ^ (2 * t) := h4
  exact Nat.le_of_mul_le_mul_left h2 (by norm_num)

end ArkLib.ProximityGap.Frontier.G132PerRungBudgetAssembly

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G132PerRungBudgetAssembly.descFactorial_mono_len
#print axioms
  ArkLib.ProximityGap.Frontier.G132PerRungBudgetAssembly.doubleFactorial_odd_mono
#print axioms
  ArkLib.ProximityGap.Frontier.G132PerRungBudgetAssembly.perRung_shallow_budget
#print axioms
  ArkLib.ProximityGap.Frontier.G132PerRungBudgetAssembly.perRung_deep_budget
#print axioms
  ArkLib.ProximityGap.Frontier.G132PerRungBudgetAssembly.perRung_full_budget