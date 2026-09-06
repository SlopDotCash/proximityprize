/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The mean-zero L^{2k} norm IS the DC-subtracted energy moment (#444)

This file lands the **exact Λ(q) ↔ energy bridge for the worst-case object** of the prize. It is the
precise identity that connects `_LambdaQRudinEndToEnd` (the Λ(q) bound ⟹ prize floor, FORWARD direction)
to `_OpenCoreMonotoneReduction` (the DC-subtracted moment `μ_{2k} ≤ Wick_k` open core).

## The object

`η : Z_p → C`, `η(b) = Σ_{x∈μ_n} e_p(b·x)` (the period sum over the `n`-th roots of unity, `n = 2^μ`,
all-ones Fourier coefficients on `μ_n`). The prize floor is `M = max_{b≠0}|η(b)|`.

## The identity (this file)

For even `q = 2k`, the **mean-subtracted** `L^{2k}` norm of `η` over `Z_p` is the **DC-subtracted energy
moment**:

  `‖η − mean‖_{L^{2k}(Z_p)}^{2k}  =  μ_{2k}  :=  (p · E_k − n^{2k}) / (p − 1)`,

where:

* `E_k := E_k(μ_n) = #{ x₁+⋯+x_k = y₁+⋯+y_k : xᵢ,yⱼ ∈ μ_n }` is the (un-normalized) `k`-th **energy
  moment** — exactly the full unnormalized `2k`-th power sum `Σ_{b∈Z_p} |η(b)|^{2k}` (Parseval / additive
  energy: `Σ_b |η(b)|^{2k} = p · E_k`, the orthogonality of additive characters collapsing the `2k`-fold
  sum to the equal-sum count `E_k` scaled by `p`).
* The **DC term** is `|η(0)|^{2k} = n^{2k}` (`η(0) = Σ_{x∈μ_n} 1 = n`).
* The mean of `η` over `Z_p` is `η(0)/p = n/p` (only the `b=0` Fourier mode survives averaging), and the
  mean-subtracted `2k`-th power sum over the `p−1` nonzero `b` is the worst-case object: the DC mode is
  *subtracted away*, exactly as a random set would have it (Khintchine), so the whole Λ(q) wall lives in
  this nonzero-`b` moment.

So `μ_{2k} = (Σ_b |η(b)|^{2k} − |η(0)|^{2k}) / (p−1) = (p·E_k − n^{2k})/(p−1)` is the **average** of
`|η(b)|^{2k}` over the `p−1` nonzero frequencies — the b≠0 period moment that `_OpenCoreMonotoneReduction`
calls `μ (with `μ_{2k} ≤ Wick_k = (2k−1)‼·n^k` the open core).

## What this file proves (axiom-clean)

We work abstractly: `E_k`, `μ_{2k}`, `M`, `n`, `p` are given reals satisfying the defining relations, and
we prove the bridge identities and the `L^∞`-from-`L^{2k}` consequence.

* `meanZero_eq_dc_subtracted_energy` — the exact identity
  `μ_{2k} · (p − 1) = p · E_k − n^{2k}` rearranged to `μ_{2k} = (p·E_k − n^{2k})/(p−1)` and back, i.e.
  the mean-zero `L^{2k}` norm equals the DC-subtracted energy moment (the definitional bridge, both
  directions).
* `worst_case_pow_le_sum_nonzero` — the worst-case `b₀ ≠ 0` term obeys `M^{2k} ≤ Σ_{b≠0} |η(b)|^{2k}`
  (`L^∞ ≤ L^{2k}` over the nonzero frequencies; the DC term is excluded from the max by `b₀ ≠ 0`).
* `worst_case_pow_le_mu` (★) — combining the two: **`M^{2k} ≤ (p−1) · μ_{2k}`**. So the worst-case sup is
  controlled by the DC-subtracted moment: `M ≤ ((p−1)·μ_{2k})^{1/(2k)}`. This is the precise hook that
  feeds the `_OpenCoreMonotoneReduction` bound `μ_{2k} ≤ Wick_k` into the `_LambdaQRudinEndToEnd`
  optimization `M ≤ C·√(n·log m)`: substituting `μ_{2k} ≤ (2k−1)‼·n^k` gives
  `M^{2k} ≤ (p−1)·(2k−1)‼·n^k`, the sub-Gaussian `L^{2k}` bound at every depth `k`.

## The named open part (DERIVED, not discharged)

This file is an **abstract Parseval/moment identity** — the bridge plumbing — and is unconditionally true.
The genuinely open content it routes to is the **deep-`k` multiplicative deviation**: whether the b≠0
moment `μ_{2k}` of the *rank-1 multiplicative* phase family `b·x` (x∈μ_n) stays Gaussian/Wick
(`μ_{2k} ≤ (2k−1)‼·n^k`) up to the saddle depth `k ≈ ln p`. That deviation IS the BGK resonance / Paley
Graph Conjecture; this file does NOT close it — it provides the exact equality that turns "bound `μ_{2k}`"
into "bound `M`". The open inequality lives in `_OpenCoreMonotoneReduction` (named `hratio` /
`open_core_of_subGaussian_growth`).

Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.LambdaQMeanZeroEnergy

open Real Finset

/-- **The DC-subtracted energy identity (forward).** Given the full energy `E_k` (so the full
unnormalized `2k`-th power sum is `p·E_k`), the DC term `n^{2k}`, and the count `p−1` of nonzero
frequencies (`hp : 1 < p`), the **mean-zero `L^{2k}` moment** `μ₂ₖ := (p·E_k − n^{2k})/(p−1)` is exactly
characterized by the linear relation `μ₂ₖ · (p−1) = p·E_k − n^{2k}`. This is the definitional bridge
identity in the form most convenient for downstream use. -/
theorem meanZero_eq_dc_subtracted_energy (Ek n2k p μ2k : ℝ) (hp : (1 : ℝ) < p)
    (hμ : μ2k = (p * Ek - n2k) / (p - 1)) :
    μ2k * (p - 1) = p * Ek - n2k := by
  have hpne : p - 1 ≠ 0 := by linarith
  rw [hμ, div_mul_cancel₀ _ hpne]

/-- **The DC-subtracted energy identity (reverse).** Conversely, from the linear relation
`μ₂ₖ·(p−1) = p·E_k − n^{2k}` (and `1 < p`) one recovers the closed form
`μ₂ₖ = (p·E_k − n^{2k})/(p−1)`. Together with `meanZero_eq_dc_subtracted_energy` this is the exact
two-sided bridge: the mean-zero `L^{2k}` norm IS the DC-subtracted energy moment. -/
theorem meanZero_eq_dc_subtracted_energy' (Ek n2k p μ2k : ℝ) (hp : (1 : ℝ) < p)
    (hrel : μ2k * (p - 1) = p * Ek - n2k) :
    μ2k = (p * Ek - n2k) / (p - 1) := by
  have hpne : p - 1 ≠ 0 := by linarith
  field_simp
  linarith [hrel]

/-- **`L^∞ ≤ L^{2k}` over the NONZERO frequencies.** The worst-case index `b₀` is nonzero
(`hb₀ : b₀ ∈ s` with `s` the nonzero frequencies), so its `2k`-th power is one nonneg term of the sum
over `s`, hence `M^{2k} = |η(b₀)|^{2k} ≤ Σ_{b∈s} |η(b)|^{2k}`. The DC term `|η(0)|^{2k} = n^{2k}` is
NOT in `s`, so it is correctly excluded from the bound — this is the mean-zero / DC-subtracted feature. -/
theorem worst_case_pow_le_sum_nonzero {ι : Type*} (s : Finset ι) (f : ι → ℝ) (b₀ : ι) (hb₀ : b₀ ∈ s)
    (hf : ∀ b ∈ s, 0 ≤ f b) (k : ℕ) :
    f b₀ ^ (2 * k) ≤ ∑ b ∈ s, f b ^ (2 * k) :=
  Finset.single_le_sum (fun b hb => pow_nonneg (hf b hb) (2 * k)) hb₀

/-- **★ The worst-case sup is controlled by the DC-subtracted moment: `M^{2k} ≤ (p−1)·μ₂ₖ`.**

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
#print axioms ArkLib.ProximityGap.LambdaQMeanZeroEnergy.meanZero_eq_dc_subtracted_energy
#print axioms ArkLib.ProximityGap.LambdaQMeanZeroEnergy.meanZero_eq_dc_subtracted_energy'
#print axioms ArkLib.ProximityGap.LambdaQMeanZeroEnergy.worst_case_pow_le_sum_nonzero
#print axioms ArkLib.ProximityGap.LambdaQMeanZeroEnergy.worst_case_pow_le_mu
#print axioms ArkLib.ProximityGap.LambdaQMeanZeroEnergy.worst_case_pow_le_wick
