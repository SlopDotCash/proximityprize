/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.EntropyVolumeBound
import Mathlib.Data.Nat.Choose.Sum

/-!
# Per-term `q`-ary entropy UPPER bound on a binomial mode

Complements the landed per-term *lower* bound `CodingTheory.choose_pow_ge_qEntropy`
(`q^{n·H_q(k/n)} ≤ (n+1)·C(n,k)(q-1)^k`) with the matching *upper* bound

  `C(n,k) · (q-1)^k ≤ q^{n · H_q(k/n)}`,

the standard entropy estimate feeding capacity / list-size **upper** bounds (the direction the
landed lower bound does not give). The combinatorial core is the single-term binomial inequality
`C(n,k) · k^k · (n-k)^{n-k} ≤ n^n` (one summand of `(k + (n-k))^n = n^n`), combined with the
landed entropy-clearing identity `entropy_rpow_eq`.

## Main results (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `choose_mul_pow_self_le_pow` — `C(n,k) · (k^k · (n-k)^{n-k}) ≤ n^n`.
* `choose_pow_le_qEntropy` — `C(n,k) · (q-1)^k ≤ q^{n·H_q(k/n)}`.
-/

namespace CodingTheory

open Real

variable {q : ℕ}

/-- **Single-term binomial bound.** `C(n,k) · k^k · (n-k)^{n-k} ≤ n^n`: the `i = k` summand of
the binomial expansion `(k + (n-k))^n = n^n` (all summands nonnegative). -/
theorem choose_mul_pow_self_le_pow (n k : ℕ) (hk : k ≤ n) :
    n.choose k * (k ^ k * (n - k) ^ (n - k)) ≤ n ^ n := by
  have hadd : (k + (n - k)) ^ n
      = ∑ i ∈ Finset.range (n + 1), k ^ i * (n - k) ^ (n - i) * n.choose i := add_pow k (n - k) n
  have hn : k + (n - k) = n := Nat.add_sub_cancel' hk
  rw [hn] at hadd
  calc n.choose k * (k ^ k * (n - k) ^ (n - k))
      = k ^ k * (n - k) ^ (n - k) * n.choose k := by ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), k ^ i * (n - k) ^ (n - i) * n.choose i := by
        refine Finset.single_le_sum
          (f := fun i => k ^ i * (n - k) ^ (n - i) * n.choose i)
          (fun i _ => Nat.zero_le _) ?_
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    _ = n ^ n := hadd.symm

/-- **Per-term `q`-ary entropy upper bound.** For `2 ≤ q`, `0 < k`, `k < n`,
`C(n,k) · (q-1)^k ≤ q^{n · H_q(k/n)}`. -/
theorem choose_pow_le_qEntropy (hq : 2 ≤ q) (n k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    ((n.choose k : ℝ) * ((q : ℝ) - 1) ^ k)
      ≤ (q : ℝ) ^ ((n : ℝ) * qEntropy q ((k : ℝ) / (n : ℝ))) := by
  have hkle : k ≤ n := le_of_lt hkn
  -- the entropy-clearing identity (landed)
  have hid := entropy_rpow_eq (q := q) hq n k hk0 hkn
  -- positivity of `D := k^k · (n-k)^{n-k}`
  have hnk0 : 0 < n - k := Nat.sub_pos_of_lt hkn
  have hDpos : (0 : ℝ) < (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) := by
    have h1 : (0 : ℝ) < (k : ℝ) ^ k := pow_pos (by exact_mod_cast hk0) k
    have h2 : (0 : ℝ) < ((n - k : ℕ) : ℝ) ^ (n - k) := pow_pos (by exact_mod_cast hnk0) (n - k)
    positivity
  -- the combinatorial bound, cast to ℝ
  have hcomb : ((n.choose k : ℝ) * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))) ≤ (n : ℝ) ^ n := by
    have := choose_mul_pow_self_le_pow n k hkle
    exact_mod_cast this
  have hq1 : (0 : ℝ) ≤ ((q : ℝ) - 1) ^ k := by
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
    exact pow_nonneg (by linarith) k
  -- multiply the combinatorial bound by (q-1)^k ≥ 0 and rewrite n^n via the identity
  have hmul : ((q : ℝ) - 1) ^ k * ((n.choose k : ℝ) * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)))
      ≤ ((q : ℝ) - 1) ^ k * (n : ℝ) ^ n :=
    mul_le_mul_of_nonneg_left hcomb hq1
  -- (q-1)^k · n^n = q^{nH} · D  (from the identity)
  rw [← hid] at hmul
  -- hmul : (q-1)^k · (C(n,k) · D) ≤ q^{nH} · D ; cancel D > 0
  have hgoal : ((q : ℝ) - 1) ^ k * (n.choose k : ℝ) ≤ (q : ℝ) ^ ((n : ℝ) * qEntropy q ((k:ℝ)/(n:ℝ))) := by
    refine le_of_mul_le_mul_right ?_ hDpos
    calc (((q : ℝ) - 1) ^ k * (n.choose k : ℝ)) * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))
        = ((q : ℝ) - 1) ^ k * ((n.choose k : ℝ) * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))) := by
          ring
      _ ≤ (q : ℝ) ^ ((n : ℝ) * qEntropy q ((k:ℝ)/(n:ℝ)))
            * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := hmul
  calc ((n.choose k : ℝ) * ((q : ℝ) - 1) ^ k)
      = ((q : ℝ) - 1) ^ k * (n.choose k : ℝ) := by ring
    _ ≤ (q : ℝ) ^ ((n : ℝ) * qEntropy q ((k:ℝ)/(n:ℝ))) := hgoal

end CodingTheory

-- Axiom audit.
#print axioms CodingTheory.choose_mul_pow_self_le_pow
#print axioms CodingTheory.choose_pow_le_qEntropy
