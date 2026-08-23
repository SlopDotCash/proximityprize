/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.EntropyVolumeBound

/-!
# Matching single-term q-ary entropy UPPER bound

The complement to `choose_pow_ge_qEntropy` (`EntropyVolumeBound.lean`): the binomial mode term is
also **at most** `q^{n·H_q(k/n)}`,

  `C(n,k) · (q-1)^k ≤ q^{n·H_q(k/n)}`   (for `2 ≤ q`, `0 < k < n`),

so together the two give the standard two-sided single-term estimate
`q^{n·H_q(k/n)} / (n+1) ≤ C(n,k)·(q-1)^k ≤ q^{n·H_q(k/n)}`.

The proof reuses the entropy-clearing identity `entropy_rpow_eq`
(`q^{n·H_q(k/n)}·(k^k·(n-k)^{n-k}) = (q-1)^k·n^n`); the entropy-free upper half is the trivial fact
that the binomial mode term is one summand of `n^n = (k + (n-k))^n` (`choose_mul_pow_le_npow`),
no Stirling needed. This upper bound feeds the Johnson / Elias list-size *upper* bounds.
`sorry`/`axiom`-free, axiom-clean.
-/

namespace CodingTheory

open Real Finset

variable {q : ℕ}

/-- The binomial mode term `C(n,k)·k^k·(n-k)^{n-k}` is at most `n^n`: it is a single summand of
`n^n = (k + (n-k))^n = ∑ᵢ C(n,i)·k^i·(n-k)^{n-i}` (all summands nonnegative). -/
theorem choose_mul_pow_le_npow (n k : ℕ) (hk : k ≤ n) :
    n.choose k * k ^ k * (n - k) ^ (n - k) ≤ n ^ n := by
  have hkmn : k + (n - k) = n := Nat.add_sub_cancel' hk
  have hsum : ∑ i ∈ Finset.range (n + 1), k ^ i * (n - k) ^ (n - i) * n.choose i = n ^ n := by
    have h := add_pow k (n - k) n
    rw [hkmn] at h
    exact h.symm
  calc n.choose k * k ^ k * (n - k) ^ (n - k)
      = k ^ k * (n - k) ^ (n - k) * n.choose k := by ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), k ^ i * (n - k) ^ (n - i) * n.choose i :=
        Finset.single_le_sum (f := fun i => k ^ i * (n - k) ^ (n - i) * n.choose i)
          (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    _ = n ^ n := hsum

/-- **Single-term q-ary entropy UPPER bound.**  For `2 ≤ q`, `0 < k`, `k < n`:

  `C(n,k) · (q-1)^k ≤ q^{n·H_q(k/n)}`.

The matching upper half of `choose_pow_ge_qEntropy`. From the entropy-clearing identity
`entropy_rpow_eq` and the entropy-free mode bound `choose_mul_pow_le_npow`. -/
theorem choose_pow_le_qEntropy (hq : 2 ≤ q) (n k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    ((n.choose k : ℝ) * ((q : ℝ) - 1) ^ k)
      ≤ (q : ℝ) ^ ((n : ℝ) * qEntropy q ((k : ℝ) / (n : ℝ))) := by
  have hkle : k ≤ n := le_of_lt hkn
  have hqsub_nonneg : (0 : ℝ) ≤ ((q : ℝ) - 1) ^ k := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
    exact pow_nonneg (by linarith) k
  -- Positivity of the denominator `k^k · (n-k)^{n-k}`.
  have hk0' : (0 : ℝ) < (k : ℝ) ^ k := pow_pos (by exact_mod_cast hk0) k
  have hmnR : (0 : ℝ) < ((n - k : ℕ) : ℝ) ^ (n - k) :=
    pow_pos (by exact_mod_cast (show 0 < n - k by omega)) (n - k)
  have hden0 : (0 : ℝ) < (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) := mul_pos hk0' hmnR
  -- The ℕ upper bound, cast to ℝ:  `C(n,k) · (k^k · (n-k)^{n-k}) ≤ n^n`.
  have hcore : (n.choose k : ℝ) * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) ≤ (n : ℝ) ^ n := by
    have h := choose_mul_pow_le_npow n k hkle
    calc (n.choose k : ℝ) * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))
        = ((n.choose k * k ^ k * (n - k) ^ (n - k) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((n ^ n : ℕ) : ℝ) := by exact_mod_cast h
      _ = (n : ℝ) ^ n := by push_cast; ring
  -- Reduce to the ℕ bound by multiplying through by the positive denominator.
  refine le_of_mul_le_mul_right ?_ hden0
  rw [entropy_rpow_eq hq n k hk0 hkn]
  calc (n.choose k : ℝ) * ((q : ℝ) - 1) ^ k * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))
      = ((q : ℝ) - 1) ^ k
          * ((n.choose k : ℝ) * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))) := by ring
    _ ≤ ((q : ℝ) - 1) ^ k * (n : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hcore hqsub_nonneg

end CodingTheory

-- Axiom audit: depends on exactly `[propext, Classical.choice, Quot.sound]`.
#print axioms CodingTheory.choose_mul_pow_le_npow
#print axioms CodingTheory.choose_pow_le_qEntropy
