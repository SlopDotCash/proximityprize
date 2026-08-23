/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Sum

/-!
# The [KKH26] entropy/Stirling step as explicit finite inequalities

The in-tree ceiling `kkh26_mcaDeltaStar_le` (`KKH26WitnessSpread.lean`) produces the
bad-scalar count `2^r · C(2^{μ−1}, r)`.  The paper [KKH26] converts this into the headline
"count `≥ 2^{s(c−o(1))} = n^{τ−o(1)}` at `η = Θ(1/log n)`" via the Stirling estimate
`log₂ C(s/2, r) = (s/2)·H₂(2r/s)·(1−o(1))` and the dyadic sandwich
`(1/2)·2^{(c/τ)s} < n ≤ 2^{(c/τ)s}`.  This file proves the **explicit-constant, finite**
versions of every analytic step — no asymptotics, no filters, every loss term written out.

## Main results

* `pow_self_le_succ_mul_choose` — the **method-of-types bound in pure `ℕ`**:
  `n^n ≤ (n+1) · C(n,k) · k^k · (n−k)^{n−k}` for `k ≤ n`, by the binomial-mode ratio
  argument (the `j = k` term is the largest of the `n+1` terms of `(k + (n−k))^n`).
* `exp_entropy_le_succ_mul_choose` / `two_rpow_entropy_le_succ_mul_choose` /
  `choose_ge_two_rpow_entropy_div` — the real form: for `0 < k < n`,
  `C(n,k) ≥ 2^{n·H₂(k/n)} / (n+1)`, with `H₂` in bits obtained from Mathlib's nat-log
  `Real.binEntropy` by dividing by `log 2`.  The loss is **exactly** the factor `n+1`.
* `count_ge_two_rpow` / `kkh26_count_corollary` / `kkh26_witness_count_ge` — the [KKH26]
  count corollary: `2^r · C(s/2, r) ≥ 2^{r + (s/2)·H₂(2r/s)/log 2} / (s/2 + 1)`, also
  instantiated at the exact `2^r · C(2^{μ−1}, r)` surface of `kkh26_mcaDeltaStar_le`.
* `exists_pow_two_window` — existence of the dyadic `n`: for `x ≥ 0` there is `k : ℕ` with
  `(1/2)·2^x < 2^k ≤ 2^x`.
* `logb_window_sandwich` — `(c/τ)·s − 1 < log₂ n ≤ (c/τ)·s` for such an `n`.
* `inv_s_window_sandwich` — the `η = Θ(1/log n)` sandwich with explicit constants:
  `(c/τ)/(1 + log₂ n) < 1/s ≤ (c/τ)/log₂ n`.
* `kkh26_count_poly_in_n` — the composed statement: when `c·s` is the exact base-2 rate
  `r + (s/2)·H₂(2r/s)/log 2` of the count and `n ≤ 2^{(c/τ)s}`, the count is at least
  `n^{τ·(1 − ε)}` with the **explicit** loss `ε = log₂(s/2 + 1)/(c·s)` — the finite,
  constant-explicit form of `n^{τ−o(1)}`.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782.
* [Jo26] ePrint 2026/891.  Issue #334.
-/

open Finset

namespace ArkLib.ProximityGap.KKH26

/-! ## The method-of-types bound in pure `ℕ`

Among the `n+1` terms `t_j = C(n,j)·k^j·(n−k)^{n−j}` of the binomial expansion of
`n^n = (k + (n−k))^n`, the term at `j = k` is maximal: the consecutive ratio identity
`t_{j+1}·(j+1)·(n−k) = t_j·(n−j)·k` shows `t` increases up to `j = k` and decreases after.
Hence `n^n ≤ (n+1)·t_k`. -/

/-- The `j`-th term of the binomial expansion of `(k + (n − k))^n` over `ℕ`. -/
private def binTerm (n k j : ℕ) : ℕ :=
  n.choose j * (k ^ j * (n - k) ^ (n - j))

/-- The consecutive-terms ratio identity, in product (division-free) form. -/
private lemma binTerm_step (n k j : ℕ) (hj : j < n) :
    binTerm n k (j + 1) * ((j + 1) * (n - k)) = binTerm n k j * ((n - j) * k) := by
  obtain ⟨d, hd⟩ : ∃ d, n - j = d + 1 := ⟨n - j - 1, by omega⟩
  have hd' : n - (j + 1) = d := by omega
  have key : n.choose (j + 1) * (j + 1) = n.choose j * (d + 1) := by
    rw [Nat.choose_succ_right_eq, hd]
  unfold binTerm
  rw [hd, hd']
  calc n.choose (j + 1) * (k ^ (j + 1) * (n - k) ^ d) * ((j + 1) * (n - k))
      = n.choose (j + 1) * (j + 1) * (k ^ (j + 1) * ((n - k) ^ d * (n - k))) := by ring
    _ = n.choose j * (d + 1) * (k ^ (j + 1) * (n - k) ^ (d + 1)) := by
        rw [key, pow_succ (n - k) d]
    _ = n.choose j * (k ^ j * (n - k) ^ (d + 1)) * ((d + 1) * k) := by
        rw [pow_succ]; ring

/-- Below the mode the terms increase: `t_j ≤ t_{j+1}` for `j < k ≤ n`. -/
private lemma binTerm_le_succ (n k j : ℕ) (hjk : j < k) (hkn : k ≤ n) :
    binTerm n k j ≤ binTerm n k (j + 1) := by
  have hjn : j < n := lt_of_lt_of_le hjk hkn
  have hstep := binTerm_step n k j hjn
  rcases eq_or_lt_of_le hkn with hkn' | hkn'
  · -- `k = n`: the `j`-th term vanishes (it contains the factor `0^{n-j}` with `n − j > 0`)
    have hzero : binTerm n k j = 0 := by
      unfold binTerm
      have h1 : n - k = 0 := by omega
      have h2 : n - j ≠ 0 := by omega
      rw [h1, zero_pow h2, mul_zero, mul_zero]
    rw [hzero]
    exact Nat.zero_le _
  · -- `k < n`: cancel the positive factor `(j+1)·(n−k)`
    have hpos : 0 < (j + 1) * (n - k) := by
      have : 0 < n - k := by omega
      positivity
    have hineq : (j + 1) * (n - k) ≤ (n - j) * k := by
      calc (j + 1) * (n - k) ≤ k * (n - k) := Nat.mul_le_mul_right _ hjk
        _ ≤ k * (n - j) := Nat.mul_le_mul_left _ (by omega)
        _ = (n - j) * k := Nat.mul_comm _ _
    have hchain : binTerm n k j * ((j + 1) * (n - k))
        ≤ binTerm n k (j + 1) * ((j + 1) * (n - k)) := by
      calc binTerm n k j * ((j + 1) * (n - k))
          ≤ binTerm n k j * ((n - j) * k) := Nat.mul_le_mul_left _ hineq
        _ = binTerm n k (j + 1) * ((j + 1) * (n - k)) := hstep.symm
    exact Nat.le_of_mul_le_mul_right hchain hpos

/-- Above the mode the terms decrease: `t_{j+1} ≤ t_j` for `k ≤ j < n`. -/
private lemma binTerm_succ_le (n k j : ℕ) (hkj : k ≤ j) (hjn : j < n) :
    binTerm n k (j + 1) ≤ binTerm n k j := by
  have hkn : k < n := lt_of_le_of_lt hkj hjn
  have hstep := binTerm_step n k j hjn
  have hpos : 0 < (j + 1) * (n - k) := by
    have : 0 < n - k := by omega
    positivity
  have hineq : (n - j) * k ≤ (j + 1) * (n - k) := by
    calc (n - j) * k ≤ (n - k) * k := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (n - k) * (j + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (j + 1) * (n - k) := Nat.mul_comm _ _
  have hchain : binTerm n k (j + 1) * ((j + 1) * (n - k))
      ≤ binTerm n k j * ((j + 1) * (n - k)) := by
    rw [hstep]
    exact Nat.mul_le_mul_left _ hineq
  exact Nat.le_of_mul_le_mul_right hchain hpos

/-- The mode of the binomial terms: every term is at most the `j = k` term. -/
private lemma binTerm_le_mode (n k : ℕ) (hkn : k ≤ n) :
    ∀ j, j ≤ n → binTerm n k j ≤ binTerm n k k := by
  have up : ∀ i, binTerm n k (k - i) ≤ binTerm n k k := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rcases le_or_gt k i with h | h
      · have heq : k - (i + 1) = k - i := by omega
        rw [heq]; exact ih
      · have h1 : k - (i + 1) < k := by omega
        have h2 : k - (i + 1) + 1 = k - i := by omega
        have hmono := binTerm_le_succ n k (k - (i + 1)) h1 hkn
        rw [h2] at hmono
        exact hmono.trans ih
  have down : ∀ j, k ≤ j → j ≤ n → binTerm n k j ≤ binTerm n k k := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hkj ih =>
      intro hjn
      exact (binTerm_succ_le n k j hkj (by omega)).trans (ih (by omega))
  intro j hjn
  rcases le_or_gt j k with h | h
  · have heq : j = k - (k - j) := by omega
    rw [heq]; exact up (k - j)
  · exact down j h.le hjn

/-- **The method-of-types bound over `ℕ`** ([KKH26] Stirling step, division-free form):
`n^n ≤ (n+1) · C(n,k) · k^k · (n−k)^{n−k}` for every `k ≤ n`.  This is the exact
finite content of `C(n,k) ≥ 2^{n·H₂(k/n)}/(n+1)`. -/
theorem pow_self_le_succ_mul_choose (n k : ℕ) (hkn : k ≤ n) :
    n ^ n ≤ (n + 1) * (n.choose k * (k ^ k * (n - k) ^ (n - k))) := by
  have hbin : n ^ n = ∑ j ∈ Finset.range (n + 1), binTerm n k j := by
    have h1 := add_pow k (n - k) n
    rw [Nat.add_sub_cancel' hkn] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold binTerm
    simp only [Nat.cast_id]
    ring
  calc n ^ n = ∑ j ∈ Finset.range (n + 1), binTerm n k j := hbin
    _ ≤ ∑ _j ∈ Finset.range (n + 1), binTerm n k k :=
        Finset.sum_le_sum fun j hj =>
          binTerm_le_mode n k hkn j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = (n + 1) * binTerm n k k := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ = (n + 1) * (n.choose k * (k ^ k * (n - k) ^ (n - k))) := rfl

/-! ## The real bridge: `2^{n·H₂(k/n)} = n^n / (k^k (n−k)^{n−k})`

Mathlib's `Real.binEntropy` is in nats (`binEntropy p = p·log p⁻¹ + (1−p)·log (1−p)⁻¹`,
natural log); bits are recovered by dividing by `log 2`, i.e.
`2^{n·H₂(k/n)} = exp (n · binEntropy (k/n))`. -/

/-- The exact value of the nat-log entropy exponential at a rational point `k/n`:
`exp (n · binEntropy (k/n)) = n^n / (k^k · (n−k)^{n−k})` for `0 < k < n`. -/
lemma exp_mul_binEntropy_eq {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    Real.exp ((n : ℝ) * Real.binEntropy ((k : ℝ) / (n : ℝ)))
      = (n : ℝ) ^ n / ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hk0.trans hkn
  have hk0' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hnk0 : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by
    have : 0 < n - k := by omega
    exact_mod_cast this
  have hd : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    exact_mod_cast Nat.cast_sub hkn.le
  have h1p : 1 - (k : ℝ) / (n : ℝ) = ((n - k : ℕ) : ℝ) / (n : ℝ) := by
    rw [hd]; field_simp
  -- the two log atoms
  set L1 : ℝ := Real.log ((n : ℝ) / (k : ℝ)) with hL1
  set L2 : ℝ := Real.log ((n : ℝ) / ((n - k : ℕ) : ℝ)) with hL2
  have harg : (n : ℝ) * Real.binEntropy ((k : ℝ) / (n : ℝ))
      = (k : ℝ) * L1 + ((n - k : ℕ) : ℝ) * L2 := by
    unfold Real.binEntropy
    rw [h1p, inv_div, inv_div, ← hL1, ← hL2]
    field_simp
  have e1 : Real.exp ((k : ℝ) * L1) = ((n : ℝ) / (k : ℝ)) ^ k := by
    rw [hL1, ← Real.log_pow, Real.exp_log (by positivity)]
  have e2 : Real.exp (((n - k : ℕ) : ℝ) * L2) = ((n : ℝ) / ((n - k : ℕ) : ℝ)) ^ (n - k) := by
    rw [hL2, ← Real.log_pow, Real.exp_log (by positivity)]
  rw [harg, Real.exp_add, e1, e2, div_pow, div_pow, div_mul_div_comm, ← pow_add,
    Nat.add_sub_cancel' hkn.le]

/-- **The entropy lower bound on binomial coefficients (nat-log form).**  For `0 < k < n`:
`exp (n · binEntropy (k/n)) ≤ (n+1) · C(n,k)`, i.e. `C(n,k) ≥ 2^{n·H₂(k/n)}/(n+1)` with
the loss being exactly the factor `n+1`. -/
theorem exp_entropy_le_succ_mul_choose {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    Real.exp ((n : ℝ) * Real.binEntropy ((k : ℝ) / (n : ℝ)))
      ≤ ((n : ℝ) + 1) * (n.choose k : ℝ) := by
  have hnk0 : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by
    have : 0 < n - k := by omega
    exact_mod_cast this
  have hk0' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hpos : (0 : ℝ) < (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) := by positivity
  have hnat := pow_self_le_succ_mul_choose n k hkn.le
  have hcast : ((n : ℝ)) ^ n
      ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))) := by
    exact_mod_cast hnat
  rw [exp_mul_binEntropy_eq hk0 hkn, div_le_iff₀ hpos]
  calc (n : ℝ) ^ n
      ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))) :=
        hcast
    _ = ((n : ℝ) + 1) * (n.choose k : ℝ) * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
        ring

/-- Base-2 conversion: `2^{y/log 2} = exp y` (real powers). -/
lemma two_rpow_div_log_two (y : ℝ) : (2 : ℝ) ^ (y / Real.log 2) = Real.exp y := by
  rw [Real.rpow_def_of_pos two_pos, mul_comm,
    div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']

/-- **The entropy lower bound in bits**: `2^{n·H₂(k/n)} ≤ (n+1)·C(n,k)` where the bit
entropy is `binEntropy(k/n)/log 2` and `^` is the real power. -/
theorem two_rpow_entropy_le_succ_mul_choose {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    (2 : ℝ) ^ ((n : ℝ) * Real.binEntropy ((k : ℝ) / (n : ℝ)) / Real.log 2)
      ≤ ((n : ℝ) + 1) * (n.choose k : ℝ) := by
  rw [two_rpow_div_log_two]
  exact exp_entropy_le_succ_mul_choose hk0 hkn

/-- Division form of the method-of-types bound: `C(n,k) ≥ 2^{n·H₂(k/n)}/(n+1)`. -/
theorem choose_ge_two_rpow_entropy_div {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    (2 : ℝ) ^ ((n : ℝ) * Real.binEntropy ((k : ℝ) / (n : ℝ)) / Real.log 2) / ((n : ℝ) + 1)
      ≤ (n.choose k : ℝ) := by
  rw [div_le_iff₀ (by positivity)]
  calc (2 : ℝ) ^ ((n : ℝ) * Real.binEntropy ((k : ℝ) / (n : ℝ)) / Real.log 2)
      ≤ ((n : ℝ) + 1) * (n.choose k : ℝ) := two_rpow_entropy_le_succ_mul_choose hk0 hkn
    _ = (n.choose k : ℝ) * ((n : ℝ) + 1) := by ring

/-! ## The [KKH26] count corollary

The bad-scalar count of `kkh26_mcaDeltaStar_le` is `2^r · C(s/2, r)` with `s = 2^μ`; the
entropy bound gives `count ≥ 2^{r + (s/2)·H₂(2r/s)/log 2}/(s/2 + 1)`, an explicit
`2^{s·(c − O(log s)/s)}`. -/

/-- The count corollary in half-domain form: for `0 < r < m`,
`2^r · C(m,r) ≥ 2^{r + m·H₂(r/m)/log 2} / (m+1)`. -/
theorem count_ge_two_rpow {m r : ℕ} (hr0 : 0 < r) (hrm : r < m) :
    (2 : ℝ) ^ ((r : ℝ) + (m : ℝ) * Real.binEntropy ((r : ℝ) / (m : ℝ)) / Real.log 2)
        / ((m : ℝ) + 1)
      ≤ (2 : ℝ) ^ r * (m.choose r : ℝ) := by
  rw [Real.rpow_add two_pos, Real.rpow_natCast, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (choose_ge_two_rpow_entropy_div hr0 hrm) (by positivity)

/-- **The [KKH26] count corollary** in the paper's `s`-variables: for even `s` and
`0 < 2r < s`, `2^r · C(s/2, r) ≥ 2^{r + (s/2)·H₂(2r/s)/log 2} / (s/2 + 1)`.  The exponent
is `s·c_r` with `c_r := r/s + H₂(2r/s)/(2 log 2)` and the loss is the single polynomial
factor `s/2 + 1`. -/
theorem kkh26_count_corollary {s r : ℕ} (hs : 2 ∣ s) (hr0 : 0 < r) (hrs : 2 * r < s) :
    (2 : ℝ) ^ ((r : ℝ) + (s : ℝ) / 2 * Real.binEntropy (2 * (r : ℝ) / (s : ℝ)) / Real.log 2)
        / ((s : ℝ) / 2 + 1)
      ≤ (2 : ℝ) ^ r * ((s / 2).choose r : ℝ) := by
    obtain ⟨m, rfl⟩ := hs
    have hm0 : 0 < m := by omega
    have hnat : 2 * m / 2 = m := by omega
    have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    have h1 : ((2 * m : ℕ) : ℝ) / 2 = (m : ℝ) := by rw [hcast]; ring
    have h2 : 2 * (r : ℝ) / ((2 * m : ℕ) : ℝ) = (r : ℝ) / (m : ℝ) := by
      rw [hcast]
      exact mul_div_mul_left (r : ℝ) (m : ℝ) two_ne_zero
    rw [hnat, h1, h2]
    exact count_ge_two_rpow hr0 (by omega)

/-- The count corollary at the exact surface of `kkh26_mcaDeltaStar_le`: the bad-scalar
count `2^r · C(2^{μ−1}, r)` is at least `2^{r + 2^{μ−1}·H₂(r/2^{μ−1})/log 2}/(2^{μ−1}+1)`. -/
theorem kkh26_witness_count_ge {μ r : ℕ} (hr0 : 0 < r) (hr : r < 2 ^ (μ - 1)) :
    (2 : ℝ) ^ ((r : ℝ) + ((2 ^ (μ - 1) : ℕ) : ℝ) *
          Real.binEntropy ((r : ℝ) / ((2 ^ (μ - 1) : ℕ) : ℝ)) / Real.log 2)
        / (((2 ^ (μ - 1) : ℕ) : ℝ) + 1)
      ≤ ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ) := by
  have h := count_ge_two_rpow (m := 2 ^ (μ - 1)) hr0 hr
  have hcast : ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ)
      = (2 : ℝ) ^ r * ((2 ^ (μ - 1)).choose r : ℝ) := by push_cast; ring
  rw [hcast]
  exact h

/-! ## The dyadic sandwich: `n` a power of two in `((1/2)·2^{(c/τ)s}, 2^{(c/τ)s}]`

These are the `η = Θ(1/log n)` bookkeeping inequalities of [KKH26], with every constant
explicit.  We first record that such an `n` always exists. -/

/-- Existence of the dyadic point: for any `x ≥ 0` there is `k : ℕ` with
`(1/2)·2^x < 2^k ≤ 2^x` (`2^k` a genuine natural number, `2^x` a real power). -/
theorem exists_pow_two_window (x : ℝ) (hx : 0 ≤ x) :
    ∃ k : ℕ, (1 / 2 : ℝ) * (2 : ℝ) ^ x < ((2 ^ k : ℕ) : ℝ) ∧
      ((2 ^ k : ℕ) : ℝ) ≤ (2 : ℝ) ^ x := by
  refine ⟨⌊x⌋.toNat, ?_, ?_⟩
  · have hcast : (((2 : ℕ) ^ ⌊x⌋.toNat : ℕ) : ℝ) = (2 : ℝ) ^ ((⌊x⌋.toNat : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; push_cast; ring
    have hfl : ((⌊x⌋.toNat : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx)
    have hlt : x - 1 < ((⌊x⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor x
    have hhalf : (1 / 2 : ℝ) * (2 : ℝ) ^ x = (2 : ℝ) ^ (x - 1) := by
      rw [Real.rpow_sub two_pos, Real.rpow_one]; ring
    rw [hcast, hfl, hhalf]
    exact Real.rpow_lt_rpow_of_exponent_lt one_lt_two hlt
  · have hcast : (((2 : ℕ) ^ ⌊x⌋.toNat : ℕ) : ℝ) = (2 : ℝ) ^ ((⌊x⌋.toNat : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; push_cast; ring
    have hfl : ((⌊x⌋.toNat : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx)
    rw [hcast, hfl]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (Int.floor_le x)

/-- **The log sandwich**: if `(1/2)·2^{(c/τ)s} < n ≤ 2^{(c/τ)s}` then
`(c/τ)·s − 1 < log₂ n ≤ (c/τ)·s`. -/
theorem logb_window_sandwich {s : ℕ} {c τ : ℝ} {n : ℕ}
    (hlow : (1 / 2 : ℝ) * (2 : ℝ) ^ (c / τ * (s : ℝ)) < (n : ℝ))
    (hhigh : (n : ℝ) ≤ (2 : ℝ) ^ (c / τ * (s : ℝ))) :
    c / τ * (s : ℝ) - 1 < Real.logb 2 (n : ℝ) ∧
      Real.logb 2 (n : ℝ) ≤ c / τ * (s : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) :=
    lt_trans (by positivity) hlow
  constructor
  · have hhalf : (1 / 2 : ℝ) * (2 : ℝ) ^ (c / τ * (s : ℝ))
        = (2 : ℝ) ^ (c / τ * (s : ℝ) - 1) := by
      rw [Real.rpow_sub two_pos, Real.rpow_one]; ring
    rw [hhalf] at hlow
    have := Real.logb_lt_logb one_lt_two (by positivity) hlow
    rwa [Real.logb_rpow two_pos (by norm_num)] at this
  · have := Real.logb_le_logb_of_le one_lt_two hn0 hhigh
    rwa [Real.logb_rpow two_pos (by norm_num)] at this

/-- **The `η = Θ(1/log n)` sandwich with explicit constants**: under the dyadic window
hypotheses and `1 ≤ (c/τ)·s` (so that `n ≥ 2`),
`(c/τ)/(1 + log₂ n) < 1/s ≤ (c/τ)/log₂ n`. -/
theorem inv_s_window_sandwich {s : ℕ} {c τ : ℝ} {n : ℕ}
    (hs : 0 < s) (hcs : 1 ≤ c / τ * (s : ℝ))
    (hlow : (1 / 2 : ℝ) * (2 : ℝ) ^ (c / τ * (s : ℝ)) < (n : ℝ))
    (hhigh : (n : ℝ) ≤ (2 : ℝ) ^ (c / τ * (s : ℝ))) :
    c / τ / (1 + Real.logb 2 (n : ℝ)) < 1 / (s : ℝ) ∧
      1 / (s : ℝ) ≤ c / τ / Real.logb 2 (n : ℝ) := by
  obtain ⟨hL_lo, hL_hi⟩ := logb_window_sandwich hlow hhigh
  have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hL_pos : 0 < Real.logb 2 (n : ℝ) := by
    have h1 : (0 : ℝ) ≤ c / τ * (s : ℝ) - 1 := by linarith
    linarith
  have h1L : (0 : ℝ) < 1 + Real.logb 2 (n : ℝ) := by linarith
  constructor
  · rw [div_lt_div_iff₀ h1L hs0]
    -- `(c/τ)·s < (1 + log₂ n) · 1` from `(c/τ)·s − 1 < log₂ n`
    nlinarith [hL_lo]
  · rw [div_le_div_iff₀ hs0 hL_pos]
    -- `log₂ n ≤ (c/τ)·s` is exactly the upper sandwich
    nlinarith [hL_hi]

/-! ## The composed statement: count ≥ `n^{τ·(1 − ε)}` with explicit `ε`

Take `c` to be the exact base-2 exponential rate of the count, `c·s = r + m·H₂(r/m)/log 2`
with `m = s/2`.  Then for any `n ≤ 2^{(c/τ)s}` the count beats `n^{τ(1−ε)}` with the fully
explicit loss `ε = log₂(m+1)/(c·s)` — the finite form of `n^{τ − o(1)}`, the loss being
`O(log s / s)` relative to the rate. -/

/-- The exact base-2 exponential rate of the [KKH26] bad-scalar count `2^r · C(m, r)`
(up to the `m+1` polynomial loss): `r + m·H₂(r/m)/log 2`. -/
noncomputable def countRate (m r : ℕ) : ℝ :=
  (r : ℝ) + (m : ℝ) * Real.binEntropy ((r : ℝ) / (m : ℝ)) / Real.log 2

/-- The rate is at least `r` (entropy is nonnegative on `[0,1]`). -/
lemma le_countRate {m r : ℕ} (hrm : r ≤ m) : (r : ℝ) ≤ countRate m r := by
  unfold countRate
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hp0 : (0 : ℝ) ≤ (r : ℝ) / (m : ℝ) := by positivity
  have hp1 : (r : ℝ) / (m : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · rw [div_le_one (by exact_mod_cast hm)]
      exact_mod_cast hrm
  have hE := Real.binEntropy_nonneg hp0 hp1
  have hlog := Real.log_pos one_lt_two
  have : (0 : ℝ) ≤ (m : ℝ) * Real.binEntropy ((r : ℝ) / (m : ℝ)) / Real.log 2 := by
    positivity
  linarith

/-- **The composed [KKH26] polynomial-in-`n` count bound.**  Let `c·s` be the exact rate
`countRate m r` (with `m = s/2`, `s = 2m`), let `τ > 0`, and let `n ≤ 2^{(c/τ)s}` (e.g. the
dyadic point of `exists_pow_two_window`).  If the polynomial loss is affordable
(`log₂(m+1) ≤ c·s`), then

  `2^r · C(m,r) ≥ n^{τ·(1 − ε)}`  with the explicit loss  `ε = log₂(m+1)/(c·s)`.

Every quantity is finite and explicit; the `o(1)` of the paper is the concrete
`ε = O(log s / s)` once `c` is bounded below. -/
theorem kkh26_count_poly_in_n {m r s n : ℕ} {c τ : ℝ}
    (hr0 : 0 < r) (hrm : r < m) (hτ : 0 < τ)
    (hsm : (s : ℝ) ≠ 0)
    (hc : c * (s : ℝ) = countRate m r)
    (hhigh : (n : ℝ) ≤ (2 : ℝ) ^ (c / τ * (s : ℝ)))
    (hbig : Real.logb 2 ((m : ℝ) + 1) ≤ c * (s : ℝ)) :
    (n : ℝ) ^ (τ * (1 - Real.logb 2 ((m : ℝ) + 1) / (c * (s : ℝ))))
      ≤ (2 : ℝ) ^ r * (m.choose r : ℝ) := by
  have hcs_pos : (0 : ℝ) < c * (s : ℝ) := by
    rw [hc]
    have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
    have h2 := le_countRate (m := m) (r := r) hrm.le
    linarith
  set ε : ℝ := Real.logb 2 ((m : ℝ) + 1) / (c * (s : ℝ)) with hε
  have hε_le_one : ε ≤ 1 := by
    rw [hε, div_le_one hcs_pos]
    exact hbig
  have hexp_nonneg : (0 : ℝ) ≤ τ * (1 - ε) := by
    have : (0 : ℝ) ≤ 1 - ε := by linarith
    positivity
  -- step 1: replace `n` by its upper bound `2^{(c/τ)s}`
  have hstep1 : (n : ℝ) ^ (τ * (1 - ε))
      ≤ ((2 : ℝ) ^ (c / τ * (s : ℝ))) ^ (τ * (1 - ε)) :=
    Real.rpow_le_rpow (by positivity) hhigh hexp_nonneg
  -- step 2: collapse the iterated power and simplify the exponent
  have hstep2 : ((2 : ℝ) ^ (c / τ * (s : ℝ))) ^ (τ * (1 - ε))
      = (2 : ℝ) ^ (c * (s : ℝ) - Real.logb 2 ((m : ℝ) + 1)) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    have hτ' : τ ≠ 0 := hτ.ne'
    have : c / τ * (s : ℝ) * (τ * (1 - ε)) = c * (s : ℝ) * (1 - ε) := by
      field_simp
    rw [this, hε, mul_sub, mul_one, mul_div_cancel₀ _ hcs_pos.ne']
  -- step 3: the right-hand side is `2^{countRate}/(m+1)`, which the count beats
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hstep3 : (2 : ℝ) ^ (c * (s : ℝ) - Real.logb 2 ((m : ℝ) + 1))
      = (2 : ℝ) ^ countRate m r / ((m : ℝ) + 1) := by
    rw [Real.rpow_sub two_pos, hc, Real.rpow_logb two_pos (by norm_num) hm1]
  calc (n : ℝ) ^ (τ * (1 - ε))
      ≤ ((2 : ℝ) ^ (c / τ * (s : ℝ))) ^ (τ * (1 - ε)) := hstep1
    _ = (2 : ℝ) ^ (c * (s : ℝ) - Real.logb 2 ((m : ℝ) + 1)) := hstep2
    _ = (2 : ℝ) ^ countRate m r / ((m : ℝ) + 1) := hstep3
    _ ≤ (2 : ℝ) ^ r * (m.choose r : ℝ) := count_ge_two_rpow hr0 hrm

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.pow_self_le_succ_mul_choose
#print axioms ArkLib.ProximityGap.KKH26.exp_entropy_le_succ_mul_choose
#print axioms ArkLib.ProximityGap.KKH26.two_rpow_entropy_le_succ_mul_choose
#print axioms ArkLib.ProximityGap.KKH26.choose_ge_two_rpow_entropy_div
#print axioms ArkLib.ProximityGap.KKH26.count_ge_two_rpow
#print axioms ArkLib.ProximityGap.KKH26.kkh26_count_corollary
#print axioms ArkLib.ProximityGap.KKH26.kkh26_witness_count_ge
#print axioms ArkLib.ProximityGap.KKH26.exists_pow_two_window
#print axioms ArkLib.ProximityGap.KKH26.logb_window_sandwich
#print axioms ArkLib.ProximityGap.KKH26.inv_s_window_sandwich
#print axioms ArkLib.ProximityGap.KKH26.kkh26_count_poly_in_n
