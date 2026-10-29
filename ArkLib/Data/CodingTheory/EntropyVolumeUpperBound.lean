/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.EntropyVolumeBound
import ArkLib.Data.CodingTheory.EntropyVolumeUpper
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

end CodingTheory

-- Axiom audit.
#print axioms CodingTheory.choose_mul_pow_self_le_pow
#print axioms CodingTheory.choose_pow_le_qEntropy
