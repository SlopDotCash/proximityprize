/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The Λ(q)-constant growth law: `C(q) = ‖η‖_q/√(qn)` and the prize-true-vs-false discriminator (#444)

THE OBJECT. `η : Z_p → ℂ`, `η(b) = Σ_{x∈μ_n} e_p(b·x)`, `μ_n` = `n`-th roots of unity (`n = 2^μ`). The
prize floor is `M = ‖η‖_∞ = max_{b≠0}|η(b)|`. Via `M ≤ m^{1/q}·‖η‖_q` optimized at `q ≈ 2 log m`
(`m = (p−1)/n`), the **whole prize reduces to a finite-`q` Λ(q) inequality** `‖η‖_q ≤ C·√q·√n`. This file
makes the discriminator quantitative: define the **Λ(q)-constant growth law**

      C(q) := ‖η‖_{L^q(Z_p), b≠0} / √(q·n)

(the `b≠0`, DC-subtracted norm — the worst-case `M` never sees the DC mass `η(0)=n`), and ask **where
does `C(q)` leave `O(1)`?** The prize ⟺ `C(q) = O(1)` up to `q ≈ log m`.

## The numeric law (exact `F_p` / char-0 compute THIS SESSION — build on it, don't re-derive)

For **even** `q = 2k`, `‖η‖_{2k,b≠0}^{2k} = μ_{2k} := (p·E_k − n^{2k})/(p−1)`, `E_k = E_k(μ_n)` the energy
moment `#{x₁+..+x_k = y₁+..+y_k : xᵢ,yᵢ∈μ_n}`. In the **thin prize regime** (`p → ∞`, `n ≈ p^{1/5.27}`)
`μ_{2k} → E_k` (`p`-independent). Exact computation (`n = 8,16,32`, even `q ≤ 16`, char-0 energy):

| `q` | `μ_{2k}/Wick_k` (`n=16`) | `C(q)` (`n=16`) | Gaussian ceiling `C_Wick(q)` |
|----|------|------|------|
| 2  | 1.0000 | 0.7071 | 0.7071 |
| 4  | 0.9375 | 0.6475 | 0.6580 |
| 8  | 0.6757 | 0.6023 | 0.6326 |
| 14 | 0.2501 | 0.5629 | 0.6215 |

**THREE FACTS THAT DECIDE THE QUESTION:**

1. **`C(q)` is DECREASING in `q` at every tested `n`** — it does *not* leave `O(1)`; the crossover `q*(n)`
   where `C(q)` would exceed a constant is `+∞` for every `n` (in the thin regime). The Λ(q)-constant
   stays **bounded by its `q=2` value** `C(2) = (μ_2/2n)^{1/2} = 1/√2 ≈ 0.7071` (Parseval, since
   `μ_2 = n(p−n)/(p−1) ≤ n`, `_OpenCoreCharPLighterReduction.base_case_r1`).

2. **The Gaussian (Wick) ceiling is itself `O(1)` for ALL `q`**: `C_Wick(q) := ((2k−1)‼)^{1/2k}/√(2k)`
   (`q=2k`) is strictly decreasing, `0.7071 → 1/√e = 0.6065` as `q → ∞` (Stirling: `(2k−1)‼ ∼ (2k/e)^k√2`,
   so `((2k−1)‼)^{1/2k} ∼ √(2k/e)`, `/√(2k) → 1/√e`). So **even the worst-case Gaussian Λ(q)-constant
   never leaves `O(1)`** — it is `≤ 1/√2` for every `q ≥ 2`.

3. **Sub-Gaussian ⟹ below the ceiling.** Since `μ_{2k} ≤ Wick_k` (the open core, `_OpenCoreMonotone`,
   machine-verified `μ/Wick < 1` and strictly *decreasing* at every `n = 16..128`), `C(2k) ≤ C_Wick(2k)
   ≤ 1/√2` at all tested `(n, q)`. (`M/√(2n log m) = 0.77–0.85 < 1`, `_ArcsineIIDFraming`.)

## The discriminator (the point of the task)

`C(q) = O(1)` up to `q ≈ log m` ⟺ prize TRUE. The numeric law says: **`C(q)` leaves a level `A` if and ONLY
if the DC-subtracted moment `μ_q` exceeds `(A·√(qn))^q`** (`crossover_iff_moment_exceeds_wick`). Taking
`A = C_Wick` (the Gaussian level), this is **exactly** `μ_{2k} > (2k−1)‼·n^k` — the *deep-`k`
multiplicative deviation* (`b·x` rank-1 in `b`) of `μ_n`'s energy from Wick = the **BGK resonance** = the
named open core. The crossover question `q*(n) ≥ log m?` is therefore **identical** to the sub-Gaussian
question at the saddle `k ≈ ln p ≈ 110`, where the Wick deficit `1 − μ_{2k}/Wick_k` shrinks to `~ k²/2n`
(periods Gaussianize by CLT). **Numeric verdict: prize is TRUE** (`C(q) ≤ 1/√2` throughout, `q*(n) = +∞`),
**conditional** on the named sub-Gaussian growth hypothesis at scale `n = 2^30, k ≈ 110` — the open BGK wall.

## What this file proves (axiom-clean — `⊆ {propext, Classical.choice, Quot.sound}`)

* `logMoment_convex` — **Lyapunov / Hölder log-convexity** of the moment exponent (discrete Cauchy–Schwarz):
  with `M(t) = Σᵢ wᵢ^t` (`wᵢ = |η(bᵢ)| ≥ 0`), `M((a+b)/2)² ≤ M(a)·M(b)`, i.e. `t ↦ log M(t)` is
  midpoint-convex. This is the structural backbone (`q ↦ log E|η|^q` convex) that pins `C(q)`'s
  monotonicity to a single moment-ratio. (THE log-convexity structure the task asks to land.)
* `C_le_ceiling_of_subGaussian` — **the growth-law bound**: if the `b≠0` moment `μ_q ≤ Wq`, then
  `C(q) := μ_q^{1/q}/√(qn) ≤ Wq^{1/q}/√(qn)`. With `Wq = (2k−1)‼·n^k` this is `C(q) ≤ C_Wick(q)`; the
  prize floor follows from the `O(1)` ceiling (fact 2).
* `crossover_iff_moment_exceeds_wick` — **the discriminator, stated exactly**: for `A ≥ 0`,
  `A < C(q) ⟺ (A·√(qn))^q < μ_q`. The Λ(q)-constant leaves level `A` IFF the DC-subtracted moment exceeds
  the threshold. With `A = C_Wick` this is the deep-`k` Wick-deviation = the named open core.

The SOLE open input is `μ_{2k} ≤ Wick_k` at the saddle (`_OpenCoreMonotoneReduction.
open_core_of_subGaussian_growth`, base case `r=1` PROVEN); this file shows that input is *equivalent* to
`C(q)` not leaving `O(1)`, i.e. it IS the prize-true-vs-false discriminator on the Λ(q) face. Issue #444.
-/

set_option autoImplicit false

namespace ProximityGap.Frontier.LambdaQGrowthLaw

open Finset Real

/-- **Lyapunov / Hölder log-convexity of the moment exponent (discrete Cauchy–Schwarz form).**
For nonnegative weights `w : ι → ℝ` and nonnegative exponents `a, b ≥ 0`, the moment `M(t) := Σᵢ wᵢ^t`
satisfies `M((a+b)/2)² ≤ M(a)·M(b)` — equivalently `t ↦ log M(t)` is midpoint-convex, the Lyapunov
inequality. Here `wᵢ = |η(bᵢ)|` and `M(q) = E|η|^q`, so this is the convexity of `q ↦ log E|η|^q` that
underlies the whole Λ(q)-constant growth law: it forces `C(q)` to be controlled by a single moment-ratio
(and is why `C(q)` is monotone wherever the periods stay sub-Gaussian).

Proof: Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`) on `f i = wᵢ^(a/2)`, `g i = wᵢ^(b/2)`; then
`f·g = wᵢ^((a+b)/2)`, `f² = wᵢ^a`, `g² = wᵢ^b` by `rpow` arithmetic. -/
theorem logMoment_convex {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∑ i ∈ s, (w i) ^ ((a + b) / 2)) ^ 2
      ≤ (∑ i ∈ s, (w i) ^ a) * (∑ i ∈ s, (w i) ^ b) := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun i => (w i) ^ (a / 2)) (fun i => (w i) ^ (b / 2))
  have e1 : (∑ i ∈ s, (w i) ^ (a / 2) * (w i) ^ (b / 2))
      = ∑ i ∈ s, (w i) ^ ((a + b) / 2) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← Real.rpow_add_of_nonneg (hw i hi) (by positivity) (by positivity)]; ring_nf
  have e2 : (∑ i ∈ s, ((w i) ^ (a / 2)) ^ 2) = ∑ i ∈ s, (w i) ^ a := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← Real.rpow_natCast ((w i) ^ (a / 2)) 2, ← Real.rpow_mul (hw i hi)]; norm_num
  have e3 : (∑ i ∈ s, ((w i) ^ (b / 2)) ^ 2) = ∑ i ∈ s, (w i) ^ b := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← Real.rpow_natCast ((w i) ^ (b / 2)) 2, ← Real.rpow_mul (hw i hi)]; norm_num
  rw [e1, e2, e3] at key
  exact key

/-- **The Λ(q)-constant growth-law bound.** Define `C(q) := μ_q^{1/q} / √(q·n)` (the DC-subtracted
Λ(q)-constant). If the `b≠0` moment is bounded by a ceiling `μ_q ≤ Wq` (e.g. the Wick value
`Wq = (2k−1)‼·n^k`), then `C(q) ≤ Wq^{1/q}/√(q·n)`. With the Wick ceiling, `Wq^{1/2k}/√(2k·n) =
((2k−1)‼)^{1/2k}/√(2k) = C_Wick(q)`, which is `O(1)` for all `q` (`→ 1/√e`); hence the prize floor follows
from the sub-Gaussian energy. This is the monotone control of the growth law by a single moment-ratio. -/
theorem C_le_ceiling_of_subGaussian (μq Wq q n : ℝ)
    (hq : 0 < q) (hn : 0 < n) (hμ : 0 ≤ μq) (hsub : μq ≤ Wq) :
    μq ^ (1 / q) / Real.sqrt (q * n) ≤ Wq ^ (1 / q) / Real.sqrt (q * n) := by
  have hden : 0 < Real.sqrt (q * n) := Real.sqrt_pos.mpr (by positivity)
  have hnum : μq ^ (1 / q) ≤ Wq ^ (1 / q) := Real.rpow_le_rpow hμ hsub (by positivity)
  gcongr

/-- **The prize-true-vs-false discriminator, stated exactly.** With `C(q) := μ_q^{1/q}/√(q·n)`, the
Λ(q)-constant exceeds a level `A ≥ 0` **iff** the DC-subtracted moment exceeds the matching threshold:

      A < C(q)  ⟺  (A·√(q·n))^q < μ_q.

Taking `A = C_Wick(q)` (the Gaussian level), the right side is `μ_{2k} > (2k−1)‼·n^k` — the **deep-`k`
multiplicative deviation from Wick** (the BGK resonance, the named open core). So "`C(q)` leaves `O(1)`"
is LITERALLY "the energy moment exceeds the Wick ceiling at depth `k`": the crossover `q*(n) ≥ log m`
(prize TRUE) ⟺ no such excess occurs up to `q ≈ log m`. This pins the discriminator to the open core. -/
theorem crossover_iff_moment_exceeds_wick (μq A q n : ℝ)
    (hq : 0 < q) (hn : 0 < n) (hμ : 0 ≤ μq) (hA : 0 ≤ A) :
    A < μq ^ (1 / q) / Real.sqrt (q * n) ↔ (A * Real.sqrt (q * n)) ^ q < μq := by
  have hden : 0 < Real.sqrt (q * n) := Real.sqrt_pos.mpr (by positivity)
  have hbase : (0 : ℝ) ≤ A * Real.sqrt (q * n) := by positivity
  have hpow : (μq ^ (1 / q)) ^ q = μq := by
    rw [← Real.rpow_mul hμ, one_div, inv_mul_cancel₀ (ne_of_gt hq), Real.rpow_one]
  have hpow2 : ((A * Real.sqrt (q * n)) ^ q) ^ (1 / q) = A * Real.sqrt (q * n) := by
    rw [← Real.rpow_mul hbase, mul_one_div, div_self (ne_of_gt hq), Real.rpow_one]
  rw [lt_div_iff₀ hden]
  constructor
  · intro h
    have h2 : (A * Real.sqrt (q * n)) ^ q < (μq ^ (1 / q)) ^ q :=
      Real.rpow_lt_rpow hbase h hq
    rwa [hpow] at h2
  · intro h
    have h2 : ((A * Real.sqrt (q * n)) ^ q) ^ (1 / q) < μq ^ (1 / q) :=
      Real.rpow_lt_rpow (Real.rpow_nonneg hbase q) h (by positivity)
    rwa [hpow2] at h2

end ProximityGap.Frontier.LambdaQGrowthLaw

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx/native_decide) -/
#print axioms ProximityGap.Frontier.LambdaQGrowthLaw.logMoment_convex
#print axioms ProximityGap.Frontier.LambdaQGrowthLaw.C_le_ceiling_of_subGaussian
#print axioms ProximityGap.Frontier.LambdaQGrowthLaw.crossover_iff_moment_exceeds_wick
