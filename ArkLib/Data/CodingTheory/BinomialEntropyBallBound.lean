/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import ArkLib.Data.CodingTheory.ProximityLeaves2
import ArkLib.Data.CodingTheory.BinomialEntropyBound

/-!
# Per-term binomial-entropy bound (real-valued)

The real-valued per-term form of the q-ary entropy ball bound named in the CS25 / ABF26 T4.17
roadmap (`rs_epsCA_breakdown_cs25_entropyBallLowerWitness`):

  `q^{n·H_q(k/n)} / (n+1) ≤ C(n,k) · (q-1)^k`   (for `2 ≤ q`, `0 < k < n`).

It is obtained from the pure-ℕ mode-term core `npow_le_succ_mul_choose_mul_pow`
(`ArkLib/Data/CodingTheory/BinomialEntropyBound.lean`) once the qEntropy ↔ qaryEntropy bridge
(`qEntropy_rpow_eq_exp_qaryEntropy`) collapses
`q^{n·H_q(k/n)}` to `(q-1)^k · n^n / (k^k·(n-k)^{n-k})`:

  `exp(n·H_q(k/n)) = (q-1)^k · (n/k)^k · (n/(n-k))^{n-k}`,
  `(n/k)^k · (n/(n-k))^{n-k} = n^n / (k^k·(n-k)^{n-k})`,

after which the inequality is exactly the ℕ core divided through by `(n+1)·k^k·(n-k)^{n-k}`.

This is the Stirling-free elementary `/(n+1)` companion to the in-tree MS77 √-estimate
`ms77_lattice` (`ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean`); it bounds the single
binomial layer that feeds the q-ary Hamming-ball volume lower bound.
-/

namespace CodingTheory

open Real

/-- `exp (m · log x) = x^m` for `x > 0` and `m : ℕ`. -/
private theorem exp_natCast_mul_log {x : ℝ} (hx : 0 < x) (m : ℕ) :
    Real.exp ((m : ℝ) * Real.log x) = x ^ m := by
  rw [mul_comm, ← Real.rpow_def_of_pos hx, Real.rpow_natCast]

/-- **Per-term binomial-entropy bound (real-valued).** For `2 ≤ q` and `0 < k < n`,

  `q^{n·H_q(k/n)} / (n+1) ≤ C(n,k) · (q-1)^k`.

Per-term form of the q-ary entropy ball bound named in the CS25 T4.17 roadmap; it follows
from the pure-ℕ mode-term core `npow_le_succ_mul_choose_mul_pow` after the
qEntropy ↔ qaryEntropy algebra collapses `q^{n·H_q(k/n)}` to
`(q-1)^k · n^n / (k^k·(n-k)^{n-k})`. -/
theorem qEntropyPow_div_succ_le_choose_mul_qsub_pow
    {q : ℕ} (hq : 2 ≤ q) {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    (q : ℝ) ^ ((n : ℝ) * qEntropy q ((k : ℝ) / (n : ℝ))) / ((n : ℝ) + 1)
      ≤ (n.choose k : ℝ) * ((q : ℝ) - 1) ^ k := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hk0' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hnk : 0 < n - k := by omega
  have hnk0 : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast hnk
  have hqsub : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  set δ : ℝ := (k : ℝ) / (n : ℝ) with hδ
  -- basic δ identities
  have h_nδ : (n : ℝ) * δ = (k : ℝ) := by rw [hδ]; field_simp
  have h_nk_real : (n : ℝ) - (k : ℝ) = ((n - k : ℕ) : ℝ) := by rw [Nat.cast_sub hkn.le]
  have h_1δ : (1 : ℝ) - δ = ((n - k : ℕ) : ℝ) / (n : ℝ) := by
    rw [hδ, ← h_nk_real]; field_simp
  have h_n1δ : (n : ℝ) * (1 - δ) = ((n - k : ℕ) : ℝ) := by rw [h_1δ]; field_simp
  have hδinv : δ⁻¹ = (n : ℝ) / (k : ℝ) := by rw [hδ, inv_div]
  have h1δinv : (1 - δ)⁻¹ = (n : ℝ) / ((n - k : ℕ) : ℝ) := by rw [h_1δ, inv_div]
  have hqcast : ((q - 1 : ℤ) : ℝ) = (q : ℝ) - 1 := by push_cast; ring
  -- exponent rearrangement (keep log args symbolic, match the def, then ring)
  have hexp_arg : (n : ℝ) * Real.qaryEntropy q δ
      = (k : ℝ) * Real.log ((q : ℝ) - 1)
        + ((k : ℝ) * Real.log ((n : ℝ) / (k : ℝ))
          + ((n - k : ℕ) : ℝ) * Real.log ((n : ℝ) / ((n - k : ℕ) : ℝ))) := by
    have e1 : Real.log ((q : ℝ) - 1) = Real.log ((q - 1 : ℤ) : ℝ) := by rw [hqcast]
    have e2 : Real.log ((n : ℝ) / (k : ℝ)) = Real.log δ⁻¹ := by rw [hδinv]
    have e3 : Real.log ((n : ℝ) / ((n - k : ℕ) : ℝ)) = Real.log (1 - δ)⁻¹ := by rw [h1δinv]
    rw [e1, e2, e3]
    unfold Real.qaryEntropy Real.binEntropy
    rw [← h_nδ, ← h_n1δ]
    ring
  -- collapse q^{...} to a product of powers
  have hpow : (q : ℝ) ^ ((n : ℝ) * qEntropy q δ)
      = ((q : ℝ) - 1) ^ k * (((n : ℝ) / (k : ℝ)) ^ k
          * ((n : ℝ) / ((n - k : ℕ) : ℝ)) ^ (n - k)) := by
    rw [qEntropy_rpow_eq_exp_qaryEntropy hq n δ, hexp_arg, Real.exp_add, Real.exp_add,
      exp_natCast_mul_log hqsub,
      exp_natCast_mul_log (x := (n : ℝ) / (k : ℝ)) (by positivity),
      exp_natCast_mul_log (x := (n : ℝ) / ((n - k : ℕ) : ℝ)) (by positivity)]
  -- collapse the two power-quotients into n^n / (k^k·(n-k)^{n-k})
  have hsplit : ((n : ℝ) / (k : ℝ)) ^ k * ((n : ℝ) / ((n - k : ℕ) : ℝ)) ^ (n - k)
      = (n : ℝ) ^ n / ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
    rw [div_pow, div_pow, div_mul_div_comm, ← pow_add, show k + (n - k) = n from by omega]
  -- the ℕ core, cast to ℝ
  have hcore : (n : ℝ) ^ n
      ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
    have h := npow_le_succ_mul_choose_mul_pow n k hkn.le
    exact_mod_cast h
  -- assemble
  rw [hpow, hsplit]
  have hQ : (0 : ℝ) ≤ ((q : ℝ) - 1) ^ k := by positivity
  rw [← mul_div_assoc, div_div,
    div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) * ((n : ℝ) + 1))]
  nlinarith [mul_le_mul_of_nonneg_left hcore hQ]

end CodingTheory

-- Audit: the per-term entropy bound is kernel-clean (no `sorryAx`).
#print axioms CodingTheory.qEntropyPow_div_succ_le_choose_mul_qsub_pow
