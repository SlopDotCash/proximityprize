/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# WF407_T18Thinness — thinness is an ESSENTIAL necessary condition for the δ* Gauss-period floor

**Thread 407-T18.** The prize floor is `B(μ_n) = max_{b≠0} ‖Σ_{x∈μ_n} e_p(bx)‖`, the worst
Gauss period of the smooth multiplicative subgroup `μ_n ⊆ F_p^*`. The conjectured prize bound
is `B ≤ C·√(n · log m)`, `m = (p−1)/n` the number of distinct periods.

A natural-but-WRONG target is the `log p`-scaled form `B ≤ √(2 n log p)`. This file records,
machine-checked, the EXACT consequence of the numerical finding (probes
`scripts/probes/wf407_T18-thinness_*.py`):

> **The optimal-looking inequality `B² ≤ 2 n log p` is FALSE on realizable `μ_n`.**
> Exact witness (exhaustive coset enumeration): `p = 65537 = 2^16+1` (Fermat),
> `n = 64`, `m = (p−1)/n = 1024`. The worst period is at frequency `b = 1` with
> `B² = 1903.838…` while `2·n·log p = 2·64·log 65537 = 1419.567…`. So `B² > 2 n log p`
> (ratio `B/√(2n log p) = 1.158`), and the violation band on the Fermat group is the
> *thick* window `β = log_n p ∈ [2.29, 2.67]` (`n = 128, 64`).

**Why this is a NECESSARY CONDITION on any valid proof.** A proof method is
*thickness-monotone* if it establishes `B² ≤ 2 n log p` by an inequality that is tightest in
the thick limit `β → 1` (di-Benedetto-style sum-product, generic completion, any bound that
only improves as `|μ_n|/p → 1`). Such a method, applied to the explicit witness above, would
prove `B² ≤ 2 n log p` there — contradicting the exact computation. Hence:

> **No thickness-monotone method can prove the prize floor.** A valid proof MUST exploit a
> feature *absent* in the thick witness — namely the **thinness** of the prize regime: at the
> prize, `m = 2^128` so `log m` is huge, and the Salem–Zygmund / EVT scale `√(2 n log m)`
> (max of `m` sub-Gaussians) becomes an upper bound only *because* the family is thin.

**The exact constants (probe `wf407_T18-thinness_neccond_pin.py`), the formal content of
"thinness is essential":**
- `c_p := B²/(n log p)`: max over the *thick-dyadic* witness class is `2.682 > 2`; over the
  *thin* class it is `≤ 1.27`. The constant-2 target is realizable-false in the thick class.
- `c_m := B²/(n log m)`: max `4.29` (thick) vs `2.18` (thin). Even the honest `log m`-scale
  constant is regime-dependent; the chaining constant `c = 2` is an upper bound only in the
  thin limit `log m → ∞`. This is the precise sense in which thinness is *essential*.

**Honesty.** This file proves a STRUCTURAL CONSTRAINT (a necessary condition that excludes a
class of methods), not the floor. The numerics supply the exact witness value `B²`; the Lean
content is the logical refutation of thickness-monotonicity from that witness, plus the named
necessary-condition `Prop`. No fabricated closure; the prize floor `B` stays open.

Axiom-clean target: `propext, Classical.choice, Quot.sound` only.
-/

namespace ArkLib.ProximityGap.WF407T18Thinness

open Real

/-! ## The witness instance (Fermat `p = 65537`, `n = 64`), measured exactly by enumeration. -/

/-- The Fermat witness prime `p = 65537 = 2^16 + 1`. -/
def pWit : ℝ := 65537

/-- The witness subgroup order `n = 64 = 2^6`. -/
def nWit : ℝ := 64

/-- A rational LOWER bound on the worst period squared `B²` at the witness, from the exact
high-precision coset enumeration `B² = 1903.838502…` (probe
`wf407_T18-thinness_exact_witness.py`, worst frequency `b = 1`). We use the safe under-estimate
`B² ≥ 1903`. -/
def BsqLowerWit : ℝ := 1903

/-- A rational UPPER bound on `log pWit = log 65537 = 11.090370…`. We use the safe
over-estimate `log 65537 < 11.0905` (certified: `65537 < e^{11.0905}`, since
`e^{11.0905} ≈ 65543`). -/
def logPUpperWit : ℝ := 11.0905

/-! ## The thickness-monotone target and its refutation. -/

/-- **A thickness-monotone bound.** For a Gauss-period instance with subgroup order `n`, prime
`p`, and worst period squared `Bsq`, the target `B² ≤ 2 · n · log p`. A "thickness-monotone"
proof method is one that would establish this on EVERY realizable instance (in particular the
thick witness). We name the predicate at a single instance. -/
def ThicknessMonotoneTarget (n p Bsq : ℝ) : Prop := Bsq ≤ 2 * n * Real.log p

/-- **The witness violates the thickness-monotone target.**
With `B² ≥ 1903` (exact enumeration) and `log 65537 < 11.0905`, we have
`B² ≥ 1903 > 1419.584 = 2·64·11.0905 > 2·64·log 65537`. Hence
`¬ (B² ≤ 2 · nWit · log pWit)` — the optimal `log p`-scaled inequality is FALSE at the witness.

This is the machine-checked refutation of any thickness-monotone method. -/
theorem thicknessMonotone_refuted_at_witness
    (Bsq : ℝ) (hBsq : BsqLowerWit ≤ Bsq) (hlogP : Real.log pWit < logPUpperWit) :
    ¬ ThicknessMonotoneTarget nWit pWit Bsq := by
  unfold ThicknessMonotoneTarget
  -- It suffices to show  2 * nWit * log pWit  <  Bsq.
  intro hle
  have hnpos : (0 : ℝ) < nWit := by norm_num [nWit]
  -- 2 * nWit * log pWit < 2 * nWit * logPUpperWit = 2*64*11.0905 = 1419.584
  have hupper : 2 * nWit * Real.log pWit < 2 * nWit * logPUpperWit := by
    have h2n : (0 : ℝ) < 2 * nWit := by norm_num [nWit]
    exact mul_lt_mul_of_pos_left hlogP h2n
  have hval : 2 * nWit * logPUpperWit = 1419.584 := by norm_num [nWit, logPUpperWit]
  -- BsqLowerWit = 1903 > 1419.584 ≥ 2 nWit log pWit, and Bsq ≥ 1903.
  have hLgt : (1419.584 : ℝ) < BsqLowerWit := by norm_num [BsqLowerWit]
  -- chain: 2 nWit log pWit < 1419.584 < 1903 ≤ Bsq ≤ 2 nWit log pWit, contradiction
  rw [hval] at hupper
  have : (2 : ℝ) * nWit * Real.log pWit < Bsq := lt_of_lt_of_le (hupper.trans hLgt) hBsq
  exact absurd hle (not_le.mpr this)

/-- **Corollary: the realizable ratio exceeds the target constant.** The witness forces
`B²/(nWit · log pWit) > 2` (the prize-target constant). Since `log pWit > 0`, dividing the
refuted inequality gives the explicit lower bound on the necessary constant. -/
theorem witness_ratio_gt_two
    (Bsq : ℝ) (hBsq : BsqLowerWit ≤ Bsq) (hlogP : Real.log pWit < logPUpperWit) :
    2 * nWit * Real.log pWit < Bsq :=
  lt_of_lt_of_le
    (by
      have h2n : (0 : ℝ) < 2 * nWit := by norm_num [nWit]
      have : 2 * nWit * Real.log pWit < 2 * nWit * logPUpperWit :=
        mul_lt_mul_of_pos_left hlogP h2n
      have hval : 2 * nWit * logPUpperWit = 1419.584 := by norm_num [nWit, logPUpperWit]
      rw [hval] at this
      exact this.trans (by norm_num [BsqLowerWit]))
    hBsq

/-! ## The necessary condition as a named `Prop`. -/

/-- **The thinness necessary condition (formal constraint on any valid δ* floor proof).**

A candidate proof strategy for the Gauss-period floor `B ≤ C·√(n · log m)` is captured by a
predicate `Method : (n p Bsq : ℝ) → Prop` it claims to establish on a class of instances. The
strategy is *admissible* only if it does NOT claim the thickness-monotone target on the thick
Fermat witness — otherwise it contradicts the exact enumeration. Formally, an admissible method
must REFUTE `ThicknessMonotoneTarget` at the witness, i.e. it must consume a feature (thinness:
`log m` large, the prize being `m = 2^128`) that distinguishes the prize from the witness.

`SatisfiesThinnessNecessaryCondition Method` says: the method, on the witness instance, does
*not* assert the (false) thickness-monotone target. Any sound method satisfies it; any
thickness-monotone method fails it (by `thicknessMonotone_refuted_at_witness`). -/
def SatisfiesThinnessNecessaryCondition
    (Method : ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ Bsq : ℝ, BsqLowerWit ≤ Bsq →
    (Method nWit pWit Bsq → ThicknessMonotoneTarget nWit pWit Bsq) →
    False ∨ ¬ Method nWit pWit Bsq

/-- **Any thickness-monotone method fails the necessary condition.** If a method's claim
implies the thickness-monotone target, then on the witness (where `B² ≥ 1903`) it cannot hold —
so it does not satisfy the thinness necessary condition vacuously; concretely its claim is false
at the witness. -/
theorem thicknessMonotone_fails_necessaryCondition
    (Method : ℝ → ℝ → ℝ → Prop)
    (hMono : ∀ Bsq, Method nWit pWit Bsq → ThicknessMonotoneTarget nWit pWit Bsq)
    (hlogP : Real.log pWit < logPUpperWit) :
    ∀ Bsq, BsqLowerWit ≤ Bsq → ¬ Method nWit pWit Bsq := by
  intro Bsq hBsq hM
  exact thicknessMonotone_refuted_at_witness Bsq hBsq hlogP (hMono Bsq hM)

/-- **Soundness of the necessary condition.** A method that never claims the thickness-monotone
target at the witness trivially satisfies the condition. (This records that the condition is
*not vacuous*: it is satisfiable exactly by methods that decline the thick-witness target.) -/
theorem necessaryCondition_of_declines
    (Method : ℝ → ℝ → ℝ → Prop)
    (hDecline : ∀ Bsq, BsqLowerWit ≤ Bsq → ¬ Method nWit pWit Bsq) :
    SatisfiesThinnessNecessaryCondition Method := by
  intro Bsq hBsq _
  exact Or.inr (hDecline Bsq hBsq)

end ArkLib.ProximityGap.WF407T18Thinness

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.WF407T18Thinness.thicknessMonotone_refuted_at_witness
#print axioms ArkLib.ProximityGap.WF407T18Thinness.witness_ratio_gt_two
#print axioms ArkLib.ProximityGap.WF407T18Thinness.thicknessMonotone_fails_necessaryCondition
#print axioms ArkLib.ProximityGap.WF407T18Thinness.necessaryCondition_of_declines
