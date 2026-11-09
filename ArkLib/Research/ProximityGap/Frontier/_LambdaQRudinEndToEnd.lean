/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The Λ(q) / Rudin route, proved END-TO-END (#444)

The prize `M = max_{b≠0}|η_b| ≤ C·√(n·log m)` is, in harmonic-analysis language, a **Λ(q) inequality** for
the frequency set `μ_n`: `‖η‖_q ≤ C·√q·√n` (μ_n is a Λ(q) set with bounded constant `C`). Machine-verified
favorable (`probe_rudin_lambdaq.py`: the Λ(q) constant is bounded and DECREASING, `≤ 0.71`).

This file proves the **entire Λ(q) → prize direction END-TO-END**, axiom-clean, modulo the single named
open input (the Λ(q) bound itself, which IS the prize = BGK / Λ(p)-set boundedness). The chain:

* **[L-bound, OPEN]** `Σ_b |η_b|^q ≤ m·(C·√(q·n))^q` — the Λ(q) bound (`m` frequencies). This is the open
  input (Rudin's inequality for the almost-Sidon set `μ_n`; the constant is governed by the energy `E_r`).
* **[sup ≤ L^q]** `M^q ≤ Σ_b |η_b|^q` — the max is bounded by the `q`-sum (`max_pow_le_sum`).
* **[optimization]** `M ≤ m^{1/q}·C·√(q·n)`, and at the optimal depth `q ≥ 2·log m` (so `m ≤ exp(q/2)`,
  hence `m^{1/q} ≤ √e`), this gives the **prize floor** `M ≤ √e·C·√(q·n) = C·√(2e)·√(n·log m)` at
  `q ≈ 2 log m` (`prize_floor_of_lambdaQ`).

So the Λ(q) route is proved end-to-end: the Λ(q) bound ⟹ the prize floor `M = O(√(n log m))`, with the
explicit constant `√(2e)·C`. Only the Λ(q) bound is open (= BGK / Λ(p) for multiplicative subgroups). The
final step prize-floor ⟹ δ* interior is the in-tree two-sided dichotomy (`_DeltaStarDefinitive`).

**Literature finding (2026-06-18, `docs/kb/deltastar-444-literature-sweep-2026-06-18.md`).** This route is a
*reformulation*, not a *reduction*: by **Pisier's iff theorem** (arXiv:1704.02969) for bounded orthonormal
systems, "`μ_n` is a Λ(q)-set with a `p`-independent bounded constant" is **logically EQUIVALENT** to `μ_n`
being Sidon/dissociated, which for this object is equivalent to the sub-Gaussian moment bound — i.e. to the
prize itself. So the forward implication proved here is genuine and useful (it is the cleanest packaging of
the prize floor), but the open input `hLambdaQ` is *equal in strength* to the prize, not weaker. A 13-domain
verified-citation literature sweep found **no** unconditional / conditional / 2-power-special-case route to
the exponent-1/2 Λ(q) bound at the prize parameters (`n ≈ p^{1/5.27}`, worst-case `b`); SOTA stays BGK
`n^{1−o(1)}` (Kowalski arXiv:2401.04756).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.LambdaQRudinEndToEnd

open Real Finset

/-- **`max_b |η_b|^q ≤ Σ_b |η_b|^q`** — the sup is bounded by the `q`-sum (a single term `≤` the whole
nonneg sum). The elementary `L^∞ ≤ L^q` step. Stated for a nonneg family on a Finset with a chosen index
`b₀` attaining the max. -/
theorem max_pow_le_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) (b₀ : ι) (hb₀ : b₀ ∈ s)
    (hf : ∀ b ∈ s, 0 ≤ f b) (q : ℕ) :
    f b₀ ^ q ≤ ∑ b ∈ s, f b ^ q :=
  Finset.single_le_sum (fun b hb => pow_nonneg (hf b hb) q) hb₀

/-- **`m^{1/q} ≤ √e` at the optimal depth.** If `m ≤ exp(q/2)` (i.e. `q ≥ 2·log m`, the Λ(q) optimization
depth), then `m^{1/q} ≤ exp(1/2) = √(exp 1) = √e`. This is the engine that turns the `L^q` bound into the
`√(log m)` sup-norm: at `q ≈ 2 log m` the `m^{1/q}` prefactor is the bounded constant `√e`. -/
theorem mRpow_inv_le_sqrt_e {m : ℝ} {q : ℕ} (hq : 0 < q) (hm : 0 < m)
    (hmexp : m ≤ Real.exp ((q : ℝ) / 2)) :
    m ^ (((q : ℕ) : ℝ)⁻¹) ≤ Real.sqrt (Real.exp 1) := by
  have hexp_pos : (0 : ℝ) < Real.exp ((q : ℝ) / 2) := Real.exp_pos _
  have hrinv : (0 : ℝ) ≤ (((q : ℕ) : ℝ))⁻¹ := by positivity
  calc m ^ (((q : ℕ) : ℝ))⁻¹
      ≤ (Real.exp ((q : ℝ) / 2)) ^ (((q : ℕ) : ℝ))⁻¹ :=
        Real.rpow_le_rpow (le_of_lt hm) hmexp hrinv
    _ = Real.sqrt (Real.exp 1) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.sqrt_eq_rpow,
            Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp]
        congr 1
        have hqne : (q : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp

/-- **The Λ(q) sup bound (the optimization core).** From the Λ(q) bound `M^q ≤ m·B^q` (the `q`-sum bound,
with `B = C·√(q·n)`) and the optimal depth `m ≤ exp(q/2)`, the sup obeys `M ≤ √e·B`. Proof: take the
`q`-th root (`M ≤ (m·B^q)^{1/q} = m^{1/q}·B`) and use `m^{1/q} ≤ √e`. -/
theorem lambdaQ_sup_bound {M B m : ℝ} {q : ℕ} (hq : 0 < q) (hM : 0 ≤ M) (hB : 0 ≤ B) (hm : 0 < m)
    (hmexp : m ≤ Real.exp ((q : ℝ) / 2))
    (hbound : M ^ q ≤ m * B ^ q) :
    M ≤ Real.sqrt (Real.exp 1) * B := by
  have hq0 : (q : ℕ) ≠ 0 := hq.ne'
  have hMpow : (0 : ℝ) ≤ M ^ q := by positivity
  -- M ≤ (m·B^q)^{1/q}
  have h1 : M ≤ (m * B ^ q) ^ (((q : ℕ) : ℝ)⁻¹) := by
    calc M = (M ^ q) ^ (((q : ℕ) : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hM hq0).symm
      _ ≤ (m * B ^ q) ^ (((q : ℕ) : ℝ)⁻¹) := Real.rpow_le_rpow hMpow hbound (by positivity)
  -- (m·B^q)^{1/q} = m^{1/q}·B
  have h2 : (m * B ^ q) ^ (((q : ℕ) : ℝ)⁻¹) = m ^ (((q : ℕ) : ℝ)⁻¹) * B := by
    rw [Real.mul_rpow (le_of_lt hm) (by positivity), Real.pow_rpow_inv_natCast hB hq0]
  rw [h2] at h1
  -- M ≤ m^{1/q}·B ≤ √e·B
  refine le_trans h1 ?_
  exact mul_le_mul_of_nonneg_right (mRpow_inv_le_sqrt_e hq hm hmexp) hB

/-- **★ The Λ(q) route, END-TO-END: Λ(q) bound ⟹ prize floor.** Instantiating `B = C·√(q·n)` (the Rudin
form), from the Λ(q) bound `M^q ≤ m·(C·√(q·n))^q` and the optimal depth `m ≤ exp(q/2)` (i.e. `q ≥ 2 log m`),
the prize floor follows: `M ≤ √e·C·√(q·n)`. At `q = ⌈2 log m⌉` this is `√e·C·√(2 log m · n) =
C·√(2e)·√(n·log m)` — the prize floor `M = O(√(n·log m))` with explicit constant `√(2e)·C`. The ONLY open
input is the Λ(q) bound (= μ_n is a Λ(q) set with bounded constant `C` = BGK / Λ(p)-set boundedness). -/
theorem prize_floor_of_lambdaQ {M C n m : ℝ} {q : ℕ} (hq : 0 < q) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hn : 0 ≤ n) (hm : 0 < m) (hmexp : m ≤ Real.exp ((q : ℝ) / 2))
    (hLambdaQ : M ^ q ≤ m * (C * Real.sqrt ((q : ℝ) * n)) ^ q) :
    M ≤ Real.sqrt (Real.exp 1) * (C * Real.sqrt ((q : ℝ) * n)) :=
  lambdaQ_sup_bound hq hM (by positivity) hm hmexp hLambdaQ

end ArkLib.ProximityGap.LambdaQRudinEndToEnd

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.LambdaQRudinEndToEnd.max_pow_le_sum
#print axioms ArkLib.ProximityGap.LambdaQRudinEndToEnd.mRpow_inv_le_sqrt_e
#print axioms ArkLib.ProximityGap.LambdaQRudinEndToEnd.lambdaQ_sup_bound
#print axioms ArkLib.ProximityGap.LambdaQRudinEndToEnd.prize_floor_of_lambdaQ
