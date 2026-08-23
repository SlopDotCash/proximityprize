/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-!
# Round 14 (Issue #232) — δ* is bounded away from capacity by an ABSOLUTE CONSTANT at prize scale

The in-tree refutations (`rs_uptoCapacity_false_*`, `RSListThresholdStrictRate12`) exclude the
capacity point itself: `δ* < 1 − ρ` (strict, at `n = 256`). This file proves the quantitatively
stronger statement at *prize scale* (large `n`, the regime `k ≤ 2^40` the prize allows):

  **`δ* ≤ 1 − ρ − Θ(ρ)` with an explicit absolute constant** — the averaging list lower bound
  `maxList(1−(k+t)/n) ≥ C(n,k+t)/q^t` stays above the prize threshold `ε*·|F| ≤ 2^128` for `t` up
  to `≈ 2k/254` (rate < 1/2) resp. `t ≈ n/258` (rate 1/2), i.e. for all relative radii in
  `[1−ρ−c_ρ, 1−ρ]` with `c_ρ ≈ ρ/127`.

The two arithmetic engines (everything in ℕ, no real analysis):

* **Rates < 1/2** (`crossover_general_rate`): `C(n, k+t) ≥ C(2(k+t), k+t) = centralBinom (k+t)`
  (monotonicity in `n`), and `4^{k+t} ≤ 2(k+t)·centralBinom(k+t)` (Mathlib), so
  `C(n,k+t) ≳ 2^{2(k+t)}` — which beats `2^{128}·q^t ≤ 2^{128+256t}` as soon as
  `2k ≥ 254·t + 193` (and `k+t ≤ 2^62`).
* **Rate 1/2** (`crossover_rate_half`): there `n = 2k` and `2(k+t) > n`, so instead use the
  Pascal **shift** `C(2m, m+t) ≥ C(2(m−t), m−t) = centralBinom (m−t) ≳ 2^{2(m−t)}` — which beats
  `2^{128+256t}` as soon as `2m ≥ 258·t + 193` (and `m ≤ 2^62`).

Composed with the in-tree averaging pigeonhole (`AveragingListLowerBoundRS`, taken here as the
`hpigeon` hypothesis `C(n,a) ≤ q^t·L` to keep this file self-contained), each gives the headline
`Lstar < L`: **the list at the interior radius exceeds the prize threshold** `Lstar = ε*·|F|`.

Non-vacuity: explicit prize-scale instantiations at `n = 2^20` — rate 1/2 with `t = 4063`
(relative gap `t/n ≈ 1/258`, i.e. `δ ≈ 0.4961` vs capacity `0.5`) and rate 1/4 with `t = 2063`.

What this does NOT do: it does not touch the lower side (`δ* ≥` Johnson) — pushing past Johnson is
the open research core. It moves the *upper* side of the bracket from "capacity excluded" to
"capacity excluded by an absolute constant" at the scale the prize actually allows.
-/

open Nat

namespace Round14ConstantGap

/-! ## 1. The Pascal shift: `C(n, m) ≤ C(n + j, m + j)`. -/

/-- One-step Pascal: `C(n, m) ≤ C(n+1, m+1)` (the RHS is `C(n,m) + C(n,m+1)`). -/
theorem choose_le_succ_succ (n m : ℕ) : n.choose m ≤ (n + 1).choose (m + 1) := by
  rw [Nat.choose_succ_succ']
  exact Nat.le_add_right _ _

/-- **The Pascal shift.** `C(n, m) ≤ C(n + j, m + j)` for every `j` (iterate the one-step). -/
theorem choose_le_add_add (n m j : ℕ) : n.choose m ≤ (n + j).choose (m + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc n.choose m ≤ (n + j).choose (m + j) := ih
      _ ≤ (n + j + 1).choose (m + j + 1) := choose_le_succ_succ _ _

/-! ## 2. The two central-binomial lower bounds on the interior binomial. -/

/-- **Rate-1/2 engine.** For `t < m`: `4^{m−t} ≤ 2(m−t) · C(2m, m+t)`. Chain:
`C(2m, m+t) ≥ C(2(m−t), m−t) = centralBinom (m−t)` (Pascal shift by `j = 2t`), and Mathlib's
`4^s ≤ 2s·centralBinom s`. -/
theorem four_pow_le_shift_choose {m t : ℕ} (ht : t < m) :
    4 ^ (m - t) ≤ 2 * (m - t) * (2 * m).choose (m + t) := by
  have hpos : 0 < m - t := Nat.sub_pos_of_lt ht
  have hcb : 4 ^ (m - t) ≤ 2 * (m - t) * centralBinom (m - t) :=
    Nat.four_pow_le_two_mul_self_mul_centralBinom (m - t) hpos
  have hshift : centralBinom (m - t) ≤ (2 * m).choose (m + t) := by
    have h := choose_le_add_add (2 * (m - t)) (m - t) (2 * t)
    have e1 : 2 * (m - t) + 2 * t = 2 * m := by omega
    have e2 : m - t + 2 * t = m + t := by omega
    rw [e1, e2] at h
    exact h
  calc 4 ^ (m - t) ≤ 2 * (m - t) * centralBinom (m - t) := hcb
    _ ≤ 2 * (m - t) * (2 * m).choose (m + t) := Nat.mul_le_mul_left _ hshift

/-- **General-rate engine.** For `0 < k + t` and `2(k+t) ≤ n`:
`4^{k+t} ≤ 2(k+t) · C(n, k+t)`. Chain: `centralBinom (k+t) = C(2(k+t), k+t) ≤ C(n, k+t)`
(monotone in `n`), and Mathlib's central-binomial bound. -/
theorem four_pow_le_choose_of_double_le {n k t : ℕ} (hpos : 0 < k + t)
    (hn : 2 * (k + t) ≤ n) :
    4 ^ (k + t) ≤ 2 * (k + t) * n.choose (k + t) := by
  have hcb : 4 ^ (k + t) ≤ 2 * (k + t) * centralBinom (k + t) :=
    Nat.four_pow_le_two_mul_self_mul_centralBinom (k + t) hpos
  have hmono : centralBinom (k + t) ≤ n.choose (k + t) :=
    Nat.choose_le_choose (k + t) hn
  calc 4 ^ (k + t) ≤ 2 * (k + t) * centralBinom (k + t) := hcb
    _ ≤ 2 * (k + t) * n.choose (k + t) := Nat.mul_le_mul_left _ hmono

/-! ## 3. The prize-scale crossovers: the binomial beats `2^{128}·q^t` for `q ≤ 2^{256}`. -/

/-- **Rate-1/2 crossover.** With `t < m`, `m ≤ 2^62`, and the scale condition `258t + 193 ≤ 2m`:
for every prize field (`q ≤ 2^{256}`) and prize threshold (`Lstar ≤ 2^{128}`),
`Lstar · q^t < C(2m, m+t)`. -/
theorem crossover_rate_half {m t q Lstar : ℕ}
    (ht : t < m) (hm : m ≤ 2 ^ 62) (hscale : 258 * t + 193 ≤ 2 * m)
    (hq : q ≤ 2 ^ 256) (hL : Lstar ≤ 2 ^ 128) :
    Lstar * q ^ t < (2 * m).choose (m + t) := by
  have hpos : 0 < 2 * (m - t) := by omega
  -- Step 1: Lstar·q^t ≤ 2^{128+256t}.
  have h1 : Lstar * q ^ t ≤ 2 ^ (128 + 256 * t) := by
    calc Lstar * q ^ t ≤ 2 ^ 128 * (2 ^ 256) ^ t :=
          Nat.mul_le_mul hL (Nat.pow_le_pow_left hq t)
      _ = 2 ^ (128 + 256 * t) := by rw [← Nat.pow_mul, ← Nat.pow_add]
  -- Step 2: 2(m−t)·2^{128+256t} < 4^{m−t} = 2^{2(m−t)}.
  have h2 : 2 * (m - t) * 2 ^ (128 + 256 * t) < 4 ^ (m - t) := by
    have hmt : 2 * (m - t) ≤ 2 ^ 63 := by
      calc 2 * (m - t) ≤ 2 * m := by omega
        _ ≤ 2 * 2 ^ 62 := by omega
        _ = 2 ^ 63 := by norm_num
    have hfour : (4 : ℕ) ^ (m - t) = 2 ^ (2 * (m - t)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← Nat.pow_mul]
    rw [hfour]
    calc 2 * (m - t) * 2 ^ (128 + 256 * t)
        ≤ 2 ^ 63 * 2 ^ (128 + 256 * t) := Nat.mul_le_mul_right _ hmt
      _ = 2 ^ (191 + 256 * t) := by rw [← Nat.pow_add]; congr 1; omega
      _ < 2 ^ (2 * (m - t)) := by
          apply Nat.pow_lt_pow_right (by norm_num)
          omega
  -- Step 3: chain through the central-binomial bound and cancel 2(m−t) > 0.
  have h3 : 4 ^ (m - t) ≤ 2 * (m - t) * (2 * m).choose (m + t) :=
    four_pow_le_shift_choose ht
  have h4 : 2 * (m - t) * (Lstar * q ^ t) < 2 * (m - t) * (2 * m).choose (m + t) := by
    calc 2 * (m - t) * (Lstar * q ^ t)
        ≤ 2 * (m - t) * 2 ^ (128 + 256 * t) := Nat.mul_le_mul_left _ h1
      _ < 4 ^ (m - t) := h2
      _ ≤ 2 * (m - t) * (2 * m).choose (m + t) := h3
  exact Nat.lt_of_mul_lt_mul_left h4

/-- **General-rate crossover.** With `0 < k`, `2(k+t) ≤ n` (rate ≤ 1/2 with room), `k + t ≤ 2^62`,
and the scale condition `254t + 193 ≤ 2k`: for every prize field (`q ≤ 2^{256}`) and prize
threshold (`Lstar ≤ 2^{128}`), `Lstar · q^t < C(n, k+t)`. -/
theorem crossover_general_rate {n k t q Lstar : ℕ}
    (hk : 0 < k) (hn : 2 * (k + t) ≤ n) (hkt : k + t ≤ 2 ^ 62)
    (hscale : 254 * t + 193 ≤ 2 * k)
    (hq : q ≤ 2 ^ 256) (hL : Lstar ≤ 2 ^ 128) :
    Lstar * q ^ t < n.choose (k + t) := by
  have hpos : 0 < k + t := by omega
  have h1 : Lstar * q ^ t ≤ 2 ^ (128 + 256 * t) := by
    calc Lstar * q ^ t ≤ 2 ^ 128 * (2 ^ 256) ^ t :=
          Nat.mul_le_mul hL (Nat.pow_le_pow_left hq t)
      _ = 2 ^ (128 + 256 * t) := by rw [← Nat.pow_mul, ← Nat.pow_add]
  have h2 : 2 * (k + t) * 2 ^ (128 + 256 * t) < 4 ^ (k + t) := by
    have hkt63 : 2 * (k + t) ≤ 2 ^ 63 := by
      calc 2 * (k + t) ≤ 2 * 2 ^ 62 := by omega
        _ = 2 ^ 63 := by norm_num
    have hfour : (4 : ℕ) ^ (k + t) = 2 ^ (2 * (k + t)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← Nat.pow_mul]
    rw [hfour]
    calc 2 * (k + t) * 2 ^ (128 + 256 * t)
        ≤ 2 ^ 63 * 2 ^ (128 + 256 * t) := Nat.mul_le_mul_right _ hkt63
      _ = 2 ^ (191 + 256 * t) := by rw [← Nat.pow_add]; congr 1; omega
      _ < 2 ^ (2 * (k + t)) := by
          apply Nat.pow_lt_pow_right (by norm_num)
          omega
  have h3 : 4 ^ (k + t) ≤ 2 * (k + t) * n.choose (k + t) :=
    four_pow_le_choose_of_double_le hpos hn
  have h4 : 2 * (k + t) * (Lstar * q ^ t) < 2 * (k + t) * n.choose (k + t) := by
    calc 2 * (k + t) * (Lstar * q ^ t)
        ≤ 2 * (k + t) * 2 ^ (128 + 256 * t) := Nat.mul_le_mul_left _ h1
      _ < 4 ^ (k + t) := h2
      _ ≤ 2 * (k + t) * n.choose (k + t) := h3
  exact Nat.lt_of_mul_lt_mul_left h4

/-! ## 4. The composed refutations: the list exceeds the prize threshold a constant below capacity. -/

/-- **HEADLINE (rate 1/2).** Under the prize-scale conditions and the averaging pigeonhole
`C(2m, m+t) ≤ q^t · L` (the in-tree `averaging_list_lower_bound` instantiated at agreement
`a = m + t`, i.e. relative radius `δ = 1/2 − t/(2m)`), the list `L` strictly exceeds the prize
threshold `Lstar = ε*·|F| ≤ 2^{128}`:

  `Lstar < L`.

Since this holds for every `t` with `258t + 193 ≤ 2m`, the threshold `δ*` of `RS[F, 2m, m]`
satisfies `δ* < 1/2 − t/(2m)` for the largest such `t ≈ m/129` — i.e. **δ* is bounded away from
capacity by the absolute constant ≈ 1/258**. -/
theorem constant_gap_rate_half {m t q L Lstar : ℕ}
    (ht : t < m) (hm : m ≤ 2 ^ 62) (hscale : 258 * t + 193 ≤ 2 * m)
    (hq : q ≤ 2 ^ 256) (hL : Lstar ≤ 2 ^ 128)
    (hpigeon : (2 * m).choose (m + t) ≤ q ^ t * L) :
    Lstar < L := by
  have h := crossover_rate_half ht hm hscale hq hL
  have hcomb : Lstar * q ^ t < q ^ t * L := lt_of_lt_of_le h hpigeon
  rw [Nat.mul_comm (q ^ t) L] at hcomb
  exact Nat.lt_of_mul_lt_mul_right hcomb

/-- **HEADLINE (rates < 1/2).** Same composition with the general-rate crossover: under
`254t + 193 ≤ 2k` and `2(k+t) ≤ n`, the list at agreement `k + t` exceeds the prize threshold.
For the largest valid `t ≈ k/127` this bounds `δ*` away from capacity by `≈ ρ/127` — at the prize
rates `ρ ∈ {1/4, 1/8, 1/16}` an absolute constant gap. -/
theorem constant_gap_general_rate {n k t q L Lstar : ℕ}
    (hk : 0 < k) (hn : 2 * (k + t) ≤ n) (hkt : k + t ≤ 2 ^ 62)
    (hscale : 254 * t + 193 ≤ 2 * k)
    (hq : q ≤ 2 ^ 256) (hL : Lstar ≤ 2 ^ 128)
    (hpigeon : n.choose (k + t) ≤ q ^ t * L) :
    Lstar < L := by
  have h := crossover_general_rate hk hn hkt hscale hq hL
  have hcomb : Lstar * q ^ t < q ^ t * L := lt_of_lt_of_le h hpigeon
  rw [Nat.mul_comm (q ^ t) L] at hcomb
  exact Nat.lt_of_mul_lt_mul_right hcomb

/-! ## 5. Non-vacuity at prize scale: explicit `n = 2^20` instantiations. -/

/-- **Prize-scale witness, rate 1/2.** At `n = 2^20` (`m = 2^19`), `t = 4063` satisfies every
hypothesis of the rate-1/2 crossover: the refutation fires at relative radius
`δ = 1/2 − 4063/2^20 ≈ 0.49613`, an absolute `≈ 1/258` below capacity. -/
theorem witness_rate_half_n_2_20 :
    4063 < 2 ^ 19 ∧ (2 ^ 19 : ℕ) ≤ 2 ^ 62 ∧ 258 * 4063 + 193 ≤ 2 * 2 ^ 19 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **Prize-scale witness, rate 1/4.** At `n = 2^20`, `k = 2^18`, `t = 2063` satisfies every
hypothesis of the general-rate crossover (`2(k+t) = 528 510 ≤ 2^20`, `254·2063 + 193 = 524 195 ≤
2^19 = 2k`): the refutation fires at `δ = 3/4 − 2063/2^20 ≈ 0.74803`, an absolute `≈ 1/508` below
the rate-1/4 capacity. -/
theorem witness_rate_quarter_n_2_20 :
    (0 : ℕ) < 2 ^ 18 ∧ 2 * (2 ^ 18 + 2063) ≤ 2 ^ 20 ∧ (2 ^ 18 + 2063 : ℕ) ≤ 2 ^ 62 ∧
      254 * 2063 + 193 ≤ 2 * 2 ^ 18 := by
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The two crossover engines fire non-vacuously at the witnesses: the rate-1/2 instantiation
delivers the strict inequality with all numerals concrete (`q = 2^256`, `Lstar = 2^128` — the
extreme prize parameters). -/
theorem nonvacuous_crossover_extreme :
    (2 ^ 128 : ℕ) * (2 ^ 256) ^ (4063 : ℕ) < (2 * 2 ^ 19).choose (2 ^ 19 + 4063) :=
  crossover_rate_half (by norm_num) (by norm_num) (by norm_num) (le_refl _) (le_refl _)

end Round14ConstantGap

#print axioms Round14ConstantGap.choose_le_add_add
#print axioms Round14ConstantGap.four_pow_le_shift_choose
#print axioms Round14ConstantGap.four_pow_le_choose_of_double_le
#print axioms Round14ConstantGap.crossover_rate_half
#print axioms Round14ConstantGap.crossover_general_rate
#print axioms Round14ConstantGap.constant_gap_rate_half
#print axioms Round14ConstantGap.constant_gap_general_rate
#print axioms Round14ConstantGap.nonvacuous_crossover_extreme
