/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The Kowalski–Untrau barrier: one growing-subgroup estimate is vacuous at prize scale (#407)

The prize floor reduces (machine-checked across faces, see `RESEARCH_SYNTHESIS_407.md`) to controlling
the **growing-`n` Gauss-period house** `B(μ_n) = max_{a≠0}‖∑_{x∈μ_n} e_p(ax)‖`. A literature result
attacking the growing-`|H|` distribution of these subgroup sums is:

> **Kowalski–Untrau 2025** (arXiv:2505.22059), *Wasserstein metrics and quantitative equidistribution*.
> **Theorem 3.8** (printed p. 16): for `q` an odd prime and `d = d(q)` a **prime** divisor of
> `q − 1` with `d → ∞` and `d = o(log q / log log q)`, the normalized subgroup sums
> `|H|^{−1/2}∑_{x∈H} e(ax/q)` (`|H| = d`) become equidistributed toward a complex Gaussian.
> This is a **one-way sufficient** condition: the paper states no converse/necessity (it is
> *not* an "iff").
> **Lemma 3.9** (printed p. 17): bounds `W₁(μ_{q,d}, γ_d)`, where `μ_{q,d}` is the law of the
> normalized subgroup sum and `γ_d` is the pushforward of Haar measure on a compact torus (the
> fixed-`d` reference measure, **not** the Gaussian), with coefficient
> `2·√12·√d·(d+1) = 4√3·√d·(d+1)` times a decay factor (quoted here as `q^{−1/(d−1)}`).
> **Lemma 3.10** separately supplies the comparison term between `γ_d` and the Gaussian limit;
> Theorem 3.8 combines the two.

Earlier versions of this file quoted Lemma 3.9 with the coefficient `2^{12}·d(d+1)` and target the
Gaussian, and quoted Theorem 3.8 as an iff. Both were wrong: `2^{12}·d(d+1)` is only a looser
**envelope** of the true coefficient (`4√3·√d·(d+1) ≤ 2^{12}·d(d+1)` for `d ≥ 1`), not the
lemma's stated constant.

**Applicability.** The KU results are proved for **prime** `d ∣ q − 1`. The production dyadic
domains have composite order `d = 2^k` (`k ≥ 2`), so neither Theorem 3.8 nor Lemma 3.9 applies
to them as stated. The computation below is therefore a statement about what this *particular*
estimate would give if its shape were extrapolated to prize-size `d`; it is not an application
of a proved theorem to the production regime.

**What is formalized (and what is not).** Using the envelope coefficient, the bound would be
non-vacuous (`< 1`; the support diameter is `O(√d)`) only when

  `2^{12}·d² < q^{1/(d−1)}`  ⟺  `(2^{12}·d²)^{d−1} < q`  ⟺  `(d−1)·(12 + 2·log₂ d) < log₂ q`.

We define the surrogate `kuThreshold d := (d − 1)·(12 + 2·log₂ d)` and prove only the elementary
`Nat.log` inequality that at every prize parameter (`d ≥ 2^32`, `q ≤ 2^256`) it exceeds `log₂ q`
(`ku_bound_vacuous_at_prize`; indeed `kuThreshold d ≥ (2^32 − 1)·76 ≈ 2^38 ≫ 256`). Because
failure of a coarser envelope does not by itself show that the sharper stated bound fails, we
also prove `ku_exact_coeff_vacuous_at_prize`: `q ≤ d^{d−1}` at every prize parameter. Since the
true coefficient satisfies `4√3·√d·(d+1) ≥ d`, the stated bound can be `< 1` (or even `< 2√d`,
the trivial diameter scale) only if `d^{d−1} < q`, so — by this informal (unformalized)
real-analysis step — the stated coefficient is also vacuous at prize-size `d`.

None of the analytic statements (Theorem 3.8, Lemmas 3.9/3.10) is formalized here; the Lean
content is three integer inequalities. This is **not** a universal impossibility result for all
growing-subgroup methods, nor for other estimates in the KU paper, and it does not close or
refute the prize: it only locates how far this specific estimate's shape is from the prize
regime.

The mechanism is visible in the quoted shape: the subgroup size `d` sits in the *exponent's
denominator* of the decay `q^{−1/(d−1)}`, so for `d ≫ log q` the decay vanishes (`q^{−1/(d−1)} ≈ 1`)
while the polynomial prefactor in `d` grows.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- [KU25]  Kowalski, Untrau. *Wasserstein metrics and quantitative equidistribution of exponential sums
  over finite fields*. arXiv:2505.22059, 2025. (Theorem 3.8, Lemmas 3.9 and 3.10.)
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.KowalskiUntrauBarrier

/-- Surrogate `log₂` non-vacuity threshold for the **envelope** form
`2^{12}·d(d+1)·q^{−1/(d−1)}` of the KU Lemma 3.9 Wasserstein bound: that envelope is `< 1` only
when `log₂ q > (d−1)·(12 + 2·log₂ d)`, where `d = |H|` is the subgroup size and the `12` is `log₂`
of the envelope constant `2^{12}`. The lemma's stated coefficient is the smaller
`4√3·√d·(d+1)`; see `ku_exact_coeff_vacuous_at_prize`. -/
def kuThreshold (d : ℕ) : ℕ := (d - 1) * (12 + 2 * Nat.log 2 d)

/-- **Surrogate threshold violated at prize scale (integer inequality).** For every prize parameter
(`d = |H| ≥ 2^32`, field size `q ≤ 2^256`), `log₂ q < kuThreshold d`. Read through the (informal)
envelope reduction in the module docstring, this says the *envelope* form of the KU Lemma 3.9 bound
would be vacuous at prize-size `d`. It does not formalize KU, the lemma does not apply to composite
dyadic `d` as stated (it assumes `d` prime), and it is not an impossibility result for other
growing-subgroup methods. The numeric gap: `kuThreshold d ≥ (2^32 − 1)·76 ≈ 2^38`, while
`log₂ q ≤ 256`. -/
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

/-- **Stated-coefficient form at prize scale (integer inequality).** For every prize parameter
(`d ≥ 2^32`, `q ≤ 2^256`), `q ≤ d^{d−1}`. Since KU Lemma 3.9's stated coefficient
`4√3·√d·(d+1)` is at least `d`, a bound `4√3·√d·(d+1)·q^{−1/(d−1)} < 1` (or `< 2√d`) would force
`d^{d−1} < q`; this theorem shows that necessary condition fails, so the sharper stated coefficient
(not only the `2^{12}` envelope) is vacuous at prize-size `d`. The real-analysis reduction is
informal, and the same applicability caveats as `ku_bound_vacuous_at_prize` apply. -/
theorem ku_exact_coeff_vacuous_at_prize {d q : ℕ} (hd : 2 ^ 32 ≤ d) (hq2 : q ≤ 2 ^ 256) :
    q ≤ d ^ (d - 1) := by
  have hd8 : 8 ≤ d - 1 := by
    have : (8 : ℕ) + 1 ≤ 2 ^ 32 := by norm_num
    omega
  have hd1 : 1 ≤ d := le_trans Nat.one_le_two_pow hd
  calc q ≤ 2 ^ 256 := hq2
    _ = (2 ^ 32) ^ 8 := by norm_num
    _ ≤ d ^ 8 := Nat.pow_le_pow_left hd 8
    _ ≤ d ^ (d - 1) := Nat.pow_le_pow_right hd1 hd8

end ArkLib.ProximityGap.KowalskiUntrauBarrier

#print axioms ArkLib.ProximityGap.KowalskiUntrauBarrier.ku_bound_vacuous_at_prize
#print axioms ArkLib.ProximityGap.KowalskiUntrauBarrier.ku_threshold_prize_gap
#print axioms ArkLib.ProximityGap.KowalskiUntrauBarrier.ku_exact_coeff_vacuous_at_prize
