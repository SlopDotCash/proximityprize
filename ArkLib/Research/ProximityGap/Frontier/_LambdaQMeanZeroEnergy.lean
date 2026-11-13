/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The punctured (nonzero-frequency) `2k`-th moment of the period and the DC-subtracted energy (#444)

This file records the scalar bookkeeping between the punctured moment
`μ_{2k} := (p·E_k − n^{2k})/(p − 1)` and the worst-case sup `M`. It connects, as plumbing,
`_LambdaQRudinEndToEnd` (the Λ(q) bound ⟹ prize floor, FORWARD direction) to
`_OpenCoreMonotoneReduction` (the DC-subtracted moment `μ_{2k} ≤ Wick_k` open core).

**Correction (audit R-305).** An earlier version of this header titled the object "the mean-zero
`L^{2k}` norm" and asserted `‖η − mean‖_{L^{2k}(Z_p)}^{2k} = μ_{2k}` with `mean = n/p`. Both are
wrong. `μ_{2k}` is the **uncentered** average of `|η(b)|^{2k}` over the `p − 1` NONZERO frequencies
(the *punctured* moment); removing the `b = 0` *sample* from a power sum is not subtracting a
constant mean from the function. The declarations below are therefore named `puncturedMoment_*`;
the legacy names `meanZero_eq_dc_subtracted_energy{,'}` survive only as deprecated aliases.

## The object

`η : Z_p → C`, `η(b) = Σ_{x∈μ_n} e_p(b·x)` (the period sum over the `n`-th roots of unity, `n = 2^μ`,
all-ones Fourier coefficients on `μ_n`). The prize floor is `M = max_{b≠0}|η(b)|`.

## Means and moments (informal; not formalized here)

* **Full-space mean.** Over the uniform probability on `Z_p`, the mean of `η` is
  `(1/p) Σ_b η(b) = (1/p) Σ_{x∈μ_n} Σ_b e_p(b·x) = 0`, because `0 ∉ μ_n` and each nonzero `x`
  contributes `Σ_b e_p(b·x) = 0`. The value `η(0) = n` is a *sample* of `η`, not its mean (it is the
  zero Fourier coefficient of the *indicator* of `μ_n` up to normalization, not of `η`).
* **Nonzero-frequency mean.** Over the uniform probability on the `p − 1` nonzero `b`, the mean of
  `η` is `(0 − n)/(p − 1) = −n/(p − 1)`.
* **The punctured moment** `μ_{2k} = (1/(p−1)) Σ_{b≠0} |η(b)|^{2k} = (p·E_k − n^{2k})/(p − 1)` is the
  UNCENTERED `2k`-th moment for the nonzero-frequency probability. It is neither the full-space
  normalized `L^{2k}` norm nor a centered moment for either probability.

Exact example `μ_2 ⊂ F_5^×` (`n = 2`, `k = 1`, `E_1 = 2`): full-space mean `0` and normalized
`‖η‖₂² = 2`; punctured second moment `(5·2 − 2²)/4 = 3/2`; nonzero-frequency mean `−1/2`, so the
centered nonzero-frequency second moment is `5/4`; subtracting the old header's (incorrect) mean
`2/5` from the full function gives `54/25`. Four different objects.

## The identity (this file)

For even `q = 2k`, the **punctured** (nonzero-frequency, uncentered) `2k`-th moment is the
**DC-subtracted energy moment**:

  `μ_{2k}  :=  (1/(p−1)) Σ_{b≠0} |η(b)|^{2k}  =  (p · E_k − n^{2k}) / (p − 1)`,

where:

* `E_k := E_k(μ_n) = #{ x₁+⋯+x_k = y₁+⋯+y_k : xᵢ,yⱼ ∈ μ_n }` is the (un-normalized) `k`-th **energy
  moment** — exactly the full unnormalized `2k`-th power sum `Σ_{b∈Z_p} |η(b)|^{2k}` (Parseval / additive
  energy: `Σ_b |η(b)|^{2k} = p · E_k`, the orthogonality of additive characters collapsing the `2k`-fold
  sum to the equal-sum count `E_k` scaled by `p`).
* The **DC term** is the `b = 0` sample `|η(0)|^{2k} = n^{2k}` (`η(0) = Σ_{x∈μ_n} 1 = n`).
* Dropping that single sample from the power sum and averaging over the `p−1` nonzero `b` gives the
  punctured moment, which is the worst-case-facing object (`M` is a max over `b ≠ 0`).

So `μ_{2k} = (Σ_b |η(b)|^{2k} − |η(0)|^{2k}) / (p−1) = (p·E_k − n^{2k})/(p−1)` is the **average** of
`|η(b)|^{2k}` over the `p−1` nonzero frequencies — the b≠0 period moment that `_OpenCoreMonotoneReduction`
calls `μ` (with `μ_{2k} ≤ Wick_k = (2k−1)‼·n^k` the open core). This all-ones moment is not a Λ(q)
constant: Λ(q) quantifies over ALL coefficient vectors, and the all-coefficient obstruction is a
separate matter (rootT97).

## What this file proves (axiom-clean)

We work abstractly: `E_k`, `μ_{2k}`, `M`, `n`, `p` are given reals satisfying the defining relations, and
we prove scalar rearrangements and the `L^∞`-from-`L^{2k}` consequence. No period function, additive
character, mean, norm, Parseval identity, or energy identification is formalized: the Parseval step
`Σ_b |η(b)|^{2k} = p·E_k` is an entered hypothesis (`hsum`) for downstream callers.

* `puncturedMoment_mul_eq` / `puncturedMoment_eq_div` — the scalar rearrangement
  `μ_{2k} = (p·E_k − n^{2k})/(p−1) ↔ μ_{2k} · (p − 1) = p · E_k − n^{2k}` (for `1 < p`), i.e. the
  closed form of the punctured (uncentered nonzero-frequency) moment (legacy deprecated names
  `meanZero_eq_dc_subtracted_energy{,'}`).
* `worst_case_pow_le_sum_nonzero` — the worst-case `b₀ ≠ 0` term obeys `M^{2k} ≤ Σ_{b≠0} |η(b)|^{2k}`
  (a single nonnegative term of a finite sum; the DC sample is excluded from the max by `b₀ ≠ 0`).
* `worst_case_pow_le_mu` (★) — combining the two: **`M^{2k} ≤ (p−1) · μ_{2k}`**. So the worst-case sup is
  controlled by the punctured moment: `M ≤ ((p−1)·μ_{2k})^{1/(2k)}`. This is the precise hook that
  feeds the `_OpenCoreMonotoneReduction` bound `μ_{2k} ≤ Wick_k` into the `_LambdaQRudinEndToEnd`
  optimization `M ≤ C·√(n·log m)`: substituting `μ_{2k} ≤ (2k−1)‼·n^k` gives
  `M^{2k} ≤ (p−1)·(2k−1)‼·n^k`, the sub-Gaussian `L^{2k}` bound at every depth `k`.

## The named open part (DERIVED, not discharged)

This file is **abstract scalar plumbing** (with the Parseval/energy step entered as a hypothesis) and
is unconditionally true as stated.
The genuinely open content it routes to is the **deep-`k` multiplicative deviation**: whether the b≠0
moment `μ_{2k}` of the *rank-1 multiplicative* phase family `b·x` (x∈μ_n) stays Gaussian/Wick
(`μ_{2k} ≤ (2k−1)‼·n^k`) up to the saddle depth `k ≈ ln p`. That deviation IS the BGK resonance / Paley
Graph Conjecture; this file does NOT close it — it provides the scalar step that turns "bound `μ_{2k}`"
into "bound `M`". The open inequality lives in `_OpenCoreMonotoneReduction` (named `hratio` /
`open_core_of_subGaussian_growth`).

Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.LambdaQMeanZeroEnergy

open Real Finset

/-- **The punctured-moment closed form (forward).** Given the full energy `E_k` (so, by the entered
Parseval step, the full unnormalized `2k`-th power sum is `p·E_k`), the DC sample `n^{2k}`, and the
count `p−1` of nonzero frequencies (`hp : 1 < p`), the **punctured (uncentered nonzero-frequency)
moment** `μ₂ₖ := (p·E_k − n^{2k})/(p−1)` satisfies the linear relation `μ₂ₖ · (p−1) = p·E_k − n^{2k}`.
This is a scalar rearrangement; `μ₂ₖ` is NOT a mean-subtracted norm (see the module header). -/
theorem puncturedMoment_mul_eq (Ek n2k p μ2k : ℝ) (hp : (1 : ℝ) < p)
    (hμ : μ2k = (p * Ek - n2k) / (p - 1)) :
    μ2k * (p - 1) = p * Ek - n2k := by
  have hpne : p - 1 ≠ 0 := by linarith
  rw [hμ, div_mul_cancel₀ _ hpne]

/-- **The punctured-moment closed form (reverse).** Conversely, from the linear relation
`μ₂ₖ·(p−1) = p·E_k − n^{2k}` (and `1 < p`) one recovers the closed form
`μ₂ₖ = (p·E_k − n^{2k})/(p−1)`. Together with `puncturedMoment_mul_eq` this is the two-sided scalar
rearrangement for the punctured (uncentered nonzero-frequency) moment. -/
theorem puncturedMoment_eq_div (Ek n2k p μ2k : ℝ) (hp : (1 : ℝ) < p)
    (hrel : μ2k * (p - 1) = p * Ek - n2k) :
    μ2k = (p * Ek - n2k) / (p - 1) := by
  have hpne : p - 1 ≠ 0 := by linarith
  field_simp
  linarith [hrel]

/-- Legacy name of `puncturedMoment_mul_eq`. The object is the punctured (uncentered
nonzero-frequency) moment, not a mean-zero norm (audit R-305). -/
@[deprecated puncturedMoment_mul_eq (since := "2026-10-28")]
theorem meanZero_eq_dc_subtracted_energy (Ek n2k p μ2k : ℝ) (hp : (1 : ℝ) < p)
    (hμ : μ2k = (p * Ek - n2k) / (p - 1)) :
    μ2k * (p - 1) = p * Ek - n2k :=
  puncturedMoment_mul_eq Ek n2k p μ2k hp hμ

/-- Legacy name of `puncturedMoment_eq_div`. The object is the punctured (uncentered
nonzero-frequency) moment, not a mean-zero norm (audit R-305). -/
@[deprecated puncturedMoment_eq_div (since := "2026-10-28")]
theorem meanZero_eq_dc_subtracted_energy' (Ek n2k p μ2k : ℝ) (hp : (1 : ℝ) < p)
    (hrel : μ2k * (p - 1) = p * Ek - n2k) :
    μ2k = (p * Ek - n2k) / (p - 1) :=
  puncturedMoment_eq_div Ek n2k p μ2k hp hrel

/-- **`L^∞ ≤ L^{2k}` over the NONZERO frequencies.** The worst-case index `b₀` is nonzero
(`hb₀ : b₀ ∈ s` with `s` the nonzero frequencies), so its `2k`-th power is one nonneg term of the sum
over `s`, hence `M^{2k} = |η(b₀)|^{2k} ≤ Σ_{b∈s} |η(b)|^{2k}`. The DC term `|η(0)|^{2k} = n^{2k}` is
NOT in `s`, so it is correctly excluded from the bound — the punctured (DC-sample-removed) feature,
which is not a mean subtraction. Formally this is just a single nonnegative term of a finite sum. -/
theorem worst_case_pow_le_sum_nonzero {ι : Type*} (s : Finset ι) (f : ι → ℝ) (b₀ : ι) (hb₀ : b₀ ∈ s)
    (hf : ∀ b ∈ s, 0 ≤ f b) (k : ℕ) :
    f b₀ ^ (2 * k) ≤ ∑ b ∈ s, f b ^ (2 * k) :=
  Finset.single_le_sum (fun b hb => pow_nonneg (hf b hb) (2 * k)) hb₀

/-- **★ The worst-case sup is controlled by the punctured moment: `M^{2k} ≤ (p−1)·μ₂ₖ`.**

Given:
* `M = f b₀` the worst-case sup (`b₀ ∈ s`, the nonzero frequencies, `hM : M = f b₀`),
* the Parseval/energy bridge as the nonzero `L^{2k}` sum equaling `(p−1)·μ₂ₖ`
  (`hsum : Σ_{b∈s} f b^{2k} = (p−1)·μ₂ₖ`; recall `Σ_{b∈s} f b^{2k} = Σ_b|η|^{2k} − |η(0)|^{2k}
  = p·E_k − n^{2k} = (p−1)·μ₂ₖ`),

then `M^{2k} ≤ (p−1)·μ₂ₖ`. Combined with the open-core bound `μ₂ₖ ≤ Wick_k = (2k−1)‼·n^k`
(`_OpenCoreMonotoneReduction`), this yields the sub-Gaussian `L^{2k}` bound
`M^{2k} ≤ (p−1)·(2k−1)‼·n^k` feeding the Λ(q) optimization of `_LambdaQRudinEndToEnd`. -/
theorem worst_case_pow_le_mu {ι : Type*} (s : Finset ι) (f : ι → ℝ) (b₀ : ι) (hb₀ : b₀ ∈ s)
    (hf : ∀ b ∈ s, 0 ≤ f b) (k : ℕ) (M p μ2k : ℝ) (hM : M = f b₀)
    (hsum : ∑ b ∈ s, f b ^ (2 * k) = (p - 1) * μ2k) :
    M ^ (2 * k) ≤ (p - 1) * μ2k := by
  rw [hM, ← hsum]
  exact worst_case_pow_le_sum_nonzero s f b₀ hb₀ hf k

/-- **The full chain, packaged: DC-subtracted moment bound ⟹ worst-case `L^{2k}` bound.** From the
energy-sum bridge `Σ_{b∈s} f b^{2k} = (p−1)·μ₂ₖ`, the worst-case identification `M = f b₀` (`b₀` nonzero),
and the **open-core Wick bound** `μ₂ₖ ≤ Wick` (the DERIVED-but-open input, = `_OpenCoreMonotoneReduction`),
with `p ≥ 1` so `p−1 ≥ 0`, the worst-case sup obeys `M^{2k} ≤ (p−1)·Wick`. This is the exact statement
that the Λ(q) route (`prize_floor_of_lambdaQ`) consumes: at `Wick = (2k−1)‼·n^k` it is the sub-Gaussian
`L^{2k}` bound, optimized at `k ≈ log m` to the prize floor `M ≤ C·√(n·log m)`. -/
theorem worst_case_pow_le_wick {ι : Type*} (s : Finset ι) (f : ι → ℝ) (b₀ : ι) (hb₀ : b₀ ∈ s)
    (hf : ∀ b ∈ s, 0 ≤ f b) (k : ℕ) (M p μ2k Wick : ℝ) (hM : M = f b₀) (hp1 : (1 : ℝ) ≤ p)
    (hsum : ∑ b ∈ s, f b ^ (2 * k) = (p - 1) * μ2k)
    (hopen : μ2k ≤ Wick) :
    M ^ (2 * k) ≤ (p - 1) * Wick := by
  have hstep : M ^ (2 * k) ≤ (p - 1) * μ2k :=
    worst_case_pow_le_mu s f b₀ hb₀ hf k M p μ2k hM hsum
  have hp1' : (0 : ℝ) ≤ p - 1 := by linarith
  exact le_trans hstep (mul_le_mul_of_nonneg_left hopen hp1')

end ArkLib.ProximityGap.LambdaQMeanZeroEnergy

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx/native_decide) -/
#print axioms ArkLib.ProximityGap.LambdaQMeanZeroEnergy.puncturedMoment_mul_eq
#print axioms ArkLib.ProximityGap.LambdaQMeanZeroEnergy.puncturedMoment_eq_div
#print axioms ArkLib.ProximityGap.LambdaQMeanZeroEnergy.worst_case_pow_le_sum_nonzero
#print axioms ArkLib.ProximityGap.LambdaQMeanZeroEnergy.worst_case_pow_le_mu
#print axioms ArkLib.ProximityGap.LambdaQMeanZeroEnergy.worst_case_pow_le_wick
