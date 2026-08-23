/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.Nat.Choose.Sum

/-!
# Binomial mode-term bound (pure ℕ core of the q-ary entropy ball bound)

The q-ary Hamming-ball volume lower bound `Vol_q(δ, n) ≥ q^{n·H_q(δ)}/(n+1)` (the easy
`/(n+1)` form sufficient for the CS25 / ABF26 T4.17 `epsCA` breakdown band, see
`rs_epsCA_breakdown_cs25_of_lower_bound`) rests on a single combinatorial inequality. After
clearing the entropy algebra
`q^{n·H_q(k/n)} = (q-1)^k · (k/n)^{-k} · ((n-k)/n)^{-(n-k)}`, the per-term bound
`C(n,k)·(q-1)^k ≥ q^{n·H_q(k/n)}/(n+1)` is equivalent to the entropy-free statement

  `n^n ≤ (n+1) · C(n,k) · k^k · (n-k)^{n-k}`   (for `k ≤ n`).

This says the term of `Binomial(n, k/n)` at its mode `i = k` dominates the average of all
`n + 1` layers. The symmetric `k = n` (in `2n`) instance is mathlib's
`Nat.four_pow_le_mul_add_one_mul_central_binom`; this general-`k` form is not in mathlib.

The proof is fully elementary (no Stirling): the layers
`C(n,i)·k^i·(n-k)^{n-i}` sum to `(k + (n-k))^n = n^n` by the binomial theorem (`add_pow`),
and each layer is `≤` the `i = k` layer, established by walking the `choose_succ_right_eq`
ratio up to and down from `k` (the binomial is unimodal with mode `k`).

This is the entropy-free ingredient for the q-ary entropy ball bound; the real-valued
entropy form and the `hammingBallVolume` bridge build on top of it.
-/

namespace CodingTheory

open Finset

/-- The weighted binomial layer `C(n,i)·k^i·(n-k)^{n-i}`. As `i` ranges over `0..n` these
are the layers of `(k + (n-k))^n = n^n`, and the family is maximised at `i = k` (the mode
of `Binomial(n, k/n)`). -/
private def binTerm (n k i : ℕ) : ℕ := n.choose i * k ^ i * (n - k) ^ (n - i)

/-- The weighted binomial layer is maximised at the mode `i = k`. -/
private theorem binTerm_le_peak (n k : ℕ) (hk : k ≤ n) :
    ∀ i, i ≤ n → binTerm n k i ≤ binTerm n k k := by
  -- One upward step, valid for `i < k`: `binTerm n k i ≤ binTerm n k (i+1)`.
  have step_up : ∀ i, i < k → binTerm n k i ≤ binTerm n k (i + 1) := by
    intro i hik
    have hin : i < n := lt_of_lt_of_le hik hk
    -- The ratio inequality `(n-k)(i+1) ≤ (n-i)k` ⟺ mode is to the right of `i`.
    have harith : (n - k) * (i + 1) ≤ (n - i) * k := by
      have hin' : i ≤ n := le_of_lt hin
      zify [hk, hin']
      have hc : (i : ℤ) + 1 ≤ k := by exact_mod_cast hik
      nlinarith [hc, mul_nonneg (by positivity : (0 : ℤ) ≤ (n : ℤ))
        (by linarith : (0 : ℤ) ≤ (k : ℤ) - i - 1)]
    -- Cross-multiplied form of the layer ratio via `choose_succ_right_eq`.
    have dagger : n.choose i * (n - k) ≤ n.choose (i + 1) * k := by
      refine le_of_mul_le_mul_right ?_ (show 0 < i + 1 by omega)
      have e1 : n.choose (i + 1) * k * (i + 1) = n.choose i * (n - i) * k := by
        rw [mul_right_comm, Nat.choose_succ_right_eq]
      rw [e1]
      calc n.choose i * (n - k) * (i + 1)
            = n.choose i * ((n - k) * (i + 1)) := by ring
        _ ≤ n.choose i * ((n - i) * k) := by gcongr
        _ = n.choose i * (n - i) * k := by ring
    have hni : n - i = (n - (i + 1)) + 1 := by omega
    show n.choose i * k ^ i * (n - k) ^ (n - i)
        ≤ n.choose (i + 1) * k ^ (i + 1) * (n - k) ^ (n - (i + 1))
    rw [hni, pow_succ (n - k) (n - (i + 1)), pow_succ k i]
    calc n.choose i * k ^ i * ((n - k) ^ (n - (i + 1)) * (n - k))
          = (k ^ i * (n - k) ^ (n - (i + 1))) * (n.choose i * (n - k)) := by ring
      _ ≤ (k ^ i * (n - k) ^ (n - (i + 1))) * (n.choose (i + 1) * k) := by gcongr
      _ = n.choose (i + 1) * (k ^ i * k) * (n - k) ^ (n - (i + 1)) := by ring
  -- One downward step, valid for `k ≤ i` and `i + 1 ≤ n`.
  have step_down : ∀ i, k ≤ i → i + 1 ≤ n → binTerm n k (i + 1) ≤ binTerm n k i := by
    intro i hki hin
    have harith : (n - i) * k ≤ (n - k) * (i + 1) := by
      have hin' : i ≤ n := by omega
      zify [hk, hin']
      have hc : (k : ℤ) ≤ i := by exact_mod_cast hki
      nlinarith [hc, mul_nonneg (by positivity : (0 : ℤ) ≤ (n : ℤ))
        (by linarith : (0 : ℤ) ≤ (i : ℤ) - k)]
    have dagger : n.choose (i + 1) * k ≤ n.choose i * (n - k) := by
      refine le_of_mul_le_mul_right ?_ (show 0 < i + 1 by omega)
      have e1 : n.choose (i + 1) * k * (i + 1) = n.choose i * (n - i) * k := by
        rw [mul_right_comm, Nat.choose_succ_right_eq]
      rw [e1]
      calc n.choose i * (n - i) * k
            = n.choose i * ((n - i) * k) := by ring
        _ ≤ n.choose i * ((n - k) * (i + 1)) := by gcongr
        _ = n.choose i * (n - k) * (i + 1) := by ring
    have hni : n - i = (n - (i + 1)) + 1 := by omega
    show n.choose (i + 1) * k ^ (i + 1) * (n - k) ^ (n - (i + 1))
        ≤ n.choose i * k ^ i * (n - k) ^ (n - i)
    rw [hni, pow_succ (n - k) (n - (i + 1)), pow_succ k i]
    calc n.choose (i + 1) * (k ^ i * k) * (n - k) ^ (n - (i + 1))
          = (k ^ i * (n - k) ^ (n - (i + 1))) * (n.choose (i + 1) * k) := by ring
      _ ≤ (k ^ i * (n - k) ^ (n - (i + 1))) * (n.choose i * (n - k)) := by gcongr
      _ = n.choose i * k ^ i * ((n - k) ^ (n - (i + 1)) * (n - k)) := by ring
  -- Chain the upward steps from any `i ≤ k` up to `k`.
  have key_up : ∀ d i, i + d ≤ k → binTerm n k i ≤ binTerm n k (i + d) := by
    intro d
    induction d with
    | zero => intro i _; simp
    | succ d ih =>
      intro i hi
      have h1 : binTerm n k i ≤ binTerm n k (i + 1) := step_up i (by omega)
      have h2 : binTerm n k (i + 1) ≤ binTerm n k ((i + 1) + d) := ih (i + 1) (by omega)
      have he : (i + 1) + d = i + (d + 1) := by omega
      rw [he] at h2
      exact le_trans h1 h2
  -- Chain the downward steps from `k` down... up to any `k ≤ i ≤ n`.
  have key_down : ∀ d i, k ≤ i → i + d ≤ n → binTerm n k (i + d) ≤ binTerm n k i := by
    intro d
    induction d with
    | zero => intro i _ _; simp
    | succ d ih =>
      intro i hki hin
      have h1 : binTerm n k ((i + d) + 1) ≤ binTerm n k (i + d) :=
        step_down (i + d) (by omega) (by omega)
      have h2 : binTerm n k (i + d) ≤ binTerm n k i := ih i hki (by omega)
      have he : i + (d + 1) = (i + d) + 1 := by omega
      rw [he]
      exact le_trans h1 h2
  intro i hi
  rcases Nat.lt_or_ge i k with hik | hik
  · have hsum : i + (k - i) = k := by omega
    have h := key_up (k - i) i (by omega)
    rw [hsum] at h
    exact h
  · have hsum : k + (i - k) = i := by omega
    have h := key_down (i - k) k (le_refl k) (by omega)
    rw [hsum] at h
    exact h

/-- **Binomial mode-term bound (pure ℕ core).** The single weighted binomial layer at the
mode `i = k` dominates the average of all `n + 1` layers:

  `n^n ≤ (n + 1) · C(n,k) · k^k · (n-k)^{n-k}`   (for `k ≤ n`).

This is the entropy-free heart of the q-ary Hamming-ball volume lower bound
`Vol_q(δ, n) ≥ q^{n·H_q(δ)}/(n+1)`.

Proof: the layers `C(n,i)·k^i·(n-k)^{n-i}` sum to `(k + (n-k))^n = n^n` by the binomial
theorem, and each is `≤` the `i = k` layer (`binTerm_le_peak`), which is the mode of
`Binomial(n, k/n)`; bounding `n + 1` summands by their maximum gives the factor `n + 1`. -/
theorem npow_le_succ_mul_choose_mul_pow (n k : ℕ) (hk : k ≤ n) :
    n ^ n ≤ (n + 1) * (n.choose k * k ^ k * (n - k) ^ (n - k)) := by
  have hkn' : k + (n - k) = n := Nat.add_sub_cancel' hk
  -- The layers sum to `n^n` by the binomial theorem.
  have hsum : ∑ i ∈ Finset.range (n + 1), binTerm n k i = n ^ n := by
    have h := add_pow k (n - k) n
    simp only [Nat.cast_id] at h
    rw [hkn'] at h
    rw [h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [binTerm]; ring
  have hconst : ∑ _i ∈ Finset.range (n + 1), binTerm n k k = (n + 1) * binTerm n k k := by
    rw [Finset.sum_const, Finset.card_range]; ring
  -- Each layer is at most the mode layer.
  have hbound : ∑ i ∈ Finset.range (n + 1), binTerm n k i
      ≤ ∑ _i ∈ Finset.range (n + 1), binTerm n k k := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    exact binTerm_le_peak n k hk i (by simpa [Nat.lt_succ_iff] using hi)
  rw [hsum, hconst] at hbound
  simpa only [binTerm] using hbound

end CodingTheory

-- Audit: the mode-term bound is kernel-clean (no `sorryAx`).
#print axioms CodingTheory.npow_le_succ_mul_choose_mul_pow
