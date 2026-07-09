/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

set_option linter.style.longLine false

/-!
# The Kowalski–Untrau barrier: the SOTA growing-subgroup bound is vacuous at prize scale (#407)

The prize floor reduces (machine-checked across faces, see `RESEARCH_SYNTHESIS_407.md`) to controlling
the **growing-`n` Gauss-period house** `B(μ_n) = max_{a≠0}‖∑_{x∈μ_n} e_p(ax)‖`. The only result in the
literature attacking exactly the growing-`|H|` distribution of these subgroup sums is:

> **Kowalski–Untrau 2025** (arXiv:2505.22059), *Wasserstein metrics and quantitative equidistribution*.
> **Lemma 3.9:** `W₁(μ_{q,d}, ν_d) ≤ 2^{12}·d(d+1)·q^{−1/(d−1)}`, `d = |H|` the subgroup size,
> `μ_{q,d}` the law of `|H|^{−1/2}∑_{x∈H} e(ax/q)`, `ν_d` the limiting hypocycloid measure.
> **Theorem 3.8:** equidistribution to a complex Gaussian holds iff `d = o(log q / log log q)`.

If this reached the prize regime it would supply the Gaussian tail that controls `B`. It does not. The
Wasserstein bound is **non-vacuous** (`< 1`, so it actually certifies closeness to the limit — the
support diameter being `O(√d)`) only when

  `2^{12}·d² < q^{1/(d−1)}`  ⟺  `(2^{12}·d²)^{d−1} < q`  ⟺  `(d−1)·(12 + 2·log₂ d) < log₂ q`.

We formalize the left side as `kuThreshold d := (d − 1)·(12 + 2·log₂ d)` and prove that at **every**
prize parameter (`d ≥ 2^32`, `q ≤ 2^256`) the threshold is violated — indeed `kuThreshold d ≥
(2^32 − 1)·76 ≈ 2^38 ≫ 256 ≥ log₂ q`. So the frontier tool is short by a factor `~2^30` in the log
(equivalently `~2^27` in the subgroup size `d`): **the best existing method provably cannot certify the
prize regime.** This is a machine-checked statement of the literature barrier — not a closure of the
prize (the wall stands), but a formal certificate locating exactly how far the SOTA falls short.

The mechanism is structural and visible in the statement: the subgroup size `d` sits in the *exponent's
denominator* of the decay `q^{−1/(d−1)}`, so for `d ≫ log q` the decay vanishes (`q^{−1/(d−1)} ≈ 1`)
while the prefactor `d²` blows up.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- [KU25]  Kowalski, Untrau. *Wasserstein metrics and quantitative equidistribution of exponential sums
  over finite fields*. arXiv:2505.22059, 2025. (Lemma 3.9, Theorem 3.8.)
-/

namespace ArkLib.ProximityGap.KowalskiUntrauBarrier

/-- `log₂` of the Kowalski–Untrau non-vacuity threshold: the SOTA Wasserstein bound (KU Lemma 3.9)
certifies equidistribution only when `log₂ q > (d−1)·(12 + 2·log₂ d)`, where `d = |H|` is the subgroup
size and the `12` is `log₂` of the `2^{12}` constant. -/
def kuThreshold (d : ℕ) : ℕ := (d - 1) * (12 + 2 * Nat.log 2 d)

/-- **The Kowalski–Untrau barrier at prize scale (machine-checked).** For every prize parameter
(`d = |H| ≥ 2^32`, field size `q ≤ 2^256`), the SOTA non-vacuity threshold is violated:
`log₂ q < kuThreshold d`. So KU Lemma 3.9 gives only a vacuous bound — the frontier growing-subgroup
equidistribution tool provably cannot certify the prize regime. The gap is enormous:
`kuThreshold d ≥ (2^32 − 1)·76 ≈ 2^38`, while `log₂ q ≤ 256`. -/
theorem ku_bound_vacuous_at_prize {d q : ℕ} (hd : 2 ^ 32 ≤ d) (_hq : 1 ≤ q) (hq2 : q ≤ 2 ^ 256) :
    Nat.log 2 q < kuThreshold d := by
  -- log₂ q ≤ 256
  have hlogq : Nat.log 2 q ≤ 256 := by
    calc Nat.log 2 q ≤ Nat.log 2 (2 ^ 256) := Nat.log_mono_right hq2
      _ = 256 := Nat.log_pow (by norm_num : (1:ℕ) < 2) 256
  -- log₂ d ≥ 32
  have hlogd : 32 ≤ Nat.log 2 d := by
    calc (32 : ℕ) = Nat.log 2 (2 ^ 32) := (Nat.log_pow (by norm_num : (1:ℕ) < 2) 32).symm
      _ ≤ Nat.log 2 d := Nat.log_mono_right hd
  -- kuThreshold d ≥ (2^32 - 1) * 76
  have hthr : (2 ^ 32 - 1) * 76 ≤ kuThreshold d := by
    unfold kuThreshold
    exact Nat.mul_le_mul (Nat.sub_le_sub_right hd 1) (by omega)
  calc Nat.log 2 q ≤ 256 := hlogq
    _ < (2 ^ 32 - 1) * 76 := by norm_num
    _ ≤ kuThreshold d := hthr

/-- The concrete prize instance: `d = 2^32`, `q = 2^256`. The threshold exceeds `log₂ q = 256` by
the factor `(2^32 − 1)·76 / 256 ≈ 2^30`. -/
theorem ku_threshold_prize_gap :
    256 < kuThreshold (2 ^ 32) ∧ (2 ^ 32 - 1) * 76 ≤ kuThreshold (2 ^ 32) := by
  refine ⟨?_, ?_⟩
  · have := ku_bound_vacuous_at_prize (d := 2 ^ 32) (q := 2 ^ 256) (le_refl _) (by norm_num) (le_refl _)
    have h256 : Nat.log 2 (2 ^ 256) = 256 := Nat.log_pow (by norm_num : (1:ℕ) < 2) 256
    omega
  · have hlogd : 32 ≤ Nat.log 2 (2 ^ 32) := le_of_eq (Nat.log_pow (by norm_num : (1:ℕ) < 2) 32).symm
    unfold kuThreshold
    exact Nat.mul_le_mul (le_refl _) (by omega)

end ArkLib.ProximityGap.KowalskiUntrauBarrier

#print axioms ArkLib.ProximityGap.KowalskiUntrauBarrier.ku_bound_vacuous_at_prize
#print axioms ArkLib.ProximityGap.KowalskiUntrauBarrier.ku_threshold_prize_gap
