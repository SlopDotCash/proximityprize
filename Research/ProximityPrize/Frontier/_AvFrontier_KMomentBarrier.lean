/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The K-moment orthogonality barrier (#444, "New Frontiers" paper §2)

**SCOPE (CORRECTED 2026-06-21 — honesty audit):** the SHARP claim "`M = max_{b≠0}|η_b|` cannot be
bounded below `α(K)` by **any** functional of `{E_1,…,E_K}`" is the MODELING thesis of the §2 paper,
**not** what this Lean file proves. This file FORMALIZES ONLY: (a) the trivial sup-from-moment
inequality `(x i₀)^K ≤ Σ_i (x i)^K` (= `Finset.single_le_sum`, the single channel through which the max
enters the moment method), and (b) the elementary algebra of the chosen exponent
`α(K) := ½ + β/(2K)` (`> ½` for finite `K`, antitone in `K`, overshoot `= β/(2K) → 0`). The
statement that NO functional of the first `K` energies reaches `½` is carried by the *definition*
`α(K) = ½ + β/(2K)` (which encodes the optimal-moment-method exponent), asserted from the paper, not
derived in-kernel — no `η_b`/spectral object and no quantification "over all functionals" appears in
any theorem here. The intended reading: the optimal moment exponent overshoots `½` and reaches it
only as `K ≈ log p`, where the char-`p` energy excess `W_K` is the open kernel (BGK at β=4).

## What this file actually proves (kernel-checked)

* `single_pow_le_sum_pow` — sup-from-moment: `(x i₀)^K ≤ Σ_i (x i)^K` for nonnegative `x` (literally
  `Finset.single_le_sum`). With `x_b = |η_b|^2`, `i₀ = argmax`: `M^{2K} ≤ Σ_b |η_b|^{2K} = p·E_K`. This
  is the only way the max enters the moment method; the `K`-th root is the resulting bound. (The
  claim that this is **sharp among ALL functionals** of `E_1,…,E_K` is the modeling thesis, not
  formalized here — extremality "concentrate one value" is sharpness for the moment method itself.)
* `kMomentExp` `:= ½ + β/(2K)` is a bare DEFINITION (the moment-method exponent from the paper);
  `kMomentExp_gt_half` (`> ½` for finite `K`), `kMomentExp_antitone` (decreasing in `K`), and
  `kMomentExp_sub_half` (`= β/(2K) → 0`) are elementary algebra of that definition. They record that
  the *defined* exponent crosses `½` only as `K → ∞`; they do not prove no functional can do better.

## Why this is the frontier (honest scope)

The "barrier" is a MODELING claim backed by elementary in-kernel algebra of the moment-method
exponent, NOT a kernel-proven impossibility over all functionals. As a heuristic it *explains* the
resistance: structural methods (moments, covariances, kernels, regularities, conductors) extract
finite-order data, and the kernel lives at order `K ≈ log p`, conjecturally orthogonal to all of it.
The file does **not** prove BGK, and does **not** prove the cross-functional optimality; it records
the exponent algebra (overshoot `β/(2K)`) and the sup-from-moment channel, which together MOTIVATE
that BGK requires a genuinely new *type* of tool (deterministic, sup-controlling, depth-`log p`,
thinness-essential). Formalizing the cross-functional barrier itself is open (see the companion
paper `docs/kb/deltastar-444-new-frontiers-ANT-2026-06-19.md`). Issue #444.
-/

namespace ProximityGap.Frontier.KMomentBarrier

open Finset

/-- **Sup-from-moment (the only entry of the max).** For nonnegative `x : ι → ℝ` and `i₀ ∈ s`,
`(x i₀)^K ≤ Σ_{i∈s} (x i)^K`. With `x_b=|η_b|²`, `i₀`=argmax: `M^{2K} ≤ Σ_b |η_b|^{2K} = p·E_K`
— the `K`-th moment bound, the sharpest a functional of `E_1,…,E_K` gives. -/
theorem single_pow_le_sum_pow {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    (K : ℕ) (i₀ : ι) (hi₀ : i₀ ∈ s) :
    (x i₀) ^ K ≤ ∑ i ∈ s, (x i) ^ K :=
  Finset.single_le_sum (fun i hi => pow_nonneg (hx i hi) K) hi₀

/-- The **`K`-energy optimal exponent** `α(K) = ½ + β/(2K)` (`β = log p / log n` the aspect
ratio). -/
noncomputable def kMomentExp (β : ℝ) (K : ℕ) : ℝ := 1 / 2 + β / (2 * K)

/-- **`α(K) > ½` for every finite `K`** (when `β > 0`) — the DEFINED moment-method exponent
`α(K) = ½ + β/(2K)` overshoots `½`. (This is positivity of `β/(2K)`; the broader "no `K`-energy
functional reaches `½`" is the modeling thesis, not proven by this lemma.) -/
theorem kMomentExp_gt_half (β : ℝ) (hβ : 0 < β) (K : ℕ) (hK : 0 < K) :
    1 / 2 < kMomentExp β K := by
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have : (0 : ℝ) < β / (2 * K) := by positivity
  unfold kMomentExp; linarith

/-- The barrier exponent is the pure overshoot `α(K) − ½ = β/(2K)`, which `→ 0` as `K → ∞`:
crossing `½`
forces unbounded moment depth `K ≈ log p`, where the char-`p` excess `W_K` is the open kernel. -/
theorem kMomentExp_sub_half (β : ℝ) (K : ℕ) :
    kMomentExp β K - 1 / 2 = β / (2 * K) := by
  unfold kMomentExp; ring

/-- **The exponent is decreasing in the depth `K`**: deeper moments give better (but never `½`)
bounds. -/
theorem kMomentExp_antitone (β : ℝ) (hβ : 0 ≤ β) {K L : ℕ} (hK : 0 < K) (hKL : K ≤ L) :
    kMomentExp β L ≤ kMomentExp β K := by
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le hK hKL)
  have hle : (K : ℝ) ≤ (L : ℝ) := by exact_mod_cast hKL
  unfold kMomentExp
  have : β / (2 * L) ≤ β / (2 * K) := by
    apply div_le_div_of_nonneg_left hβ (by positivity)
    linarith
  linarith

end ProximityGap.Frontier.KMomentBarrier

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.KMomentBarrier.single_pow_le_sum_pow
#print axioms ProximityGap.Frontier.KMomentBarrier.kMomentExp_gt_half
#print axioms ProximityGap.Frontier.KMomentBarrier.kMomentExp_sub_half
#print axioms ProximityGap.Frontier.KMomentBarrier.kMomentExp_antitone
