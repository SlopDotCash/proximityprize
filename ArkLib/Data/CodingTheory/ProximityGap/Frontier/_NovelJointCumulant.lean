/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MomentMethodNoGo

/-!
# N1 cross-prime JOINT-CUMULANT: ADVERSARIAL AUDIT — verdict REDUCES (#444)

This file records the result of a ruthless stress-test of the "N1 joint-cumulant" escape idea.
**Verdict: REDUCES to BGK / violates the in-tree moment-method necessity obstruction.** It does
NOT close the char-`p` prize, and (contra the claimed SKELETON status) it is not even a viable
skeleton: the central inequality, when unfolded, *contains the obstructed magnitude as an additive
lower term*, so any honest discharge would already have to prove the BGK baseline — the very thing
N1 was supposed to bypass.

## The N1 idea (as proposed)

Let `P = {p_j : p_j ≡ 1 (mod n)}` be the prime family (the `Z_2`-tower of #444), all carrying the
same multiplicative subgroup `μ_n`. For a per-prime wraparound-excess observable `W : ι → ℝ`,
`W p = W_r^(p)`, define
* `fmean P W` — the *disconnected* family mean `= Σ_s ρ_s` (the BGK random-divisibility baseline);
* `fvar P W = (1/m)·Σ_{s,s'} Cov(χ_s, χ_{s'})` — the *connected* second joint cumulant.
The proposed claim is
  `JointCumulantDecay P W slack : fmean P W + √(P.card · fvar P W) ≤ slack`,
with the **claimed escape**: the obstruction `MomentLadderExceedsPrize.moment_ladder_exceeds_prize`
only bounds a *single* prime's magnitude `(q·Σc²)^{1/2r} ≥ n`; N1 "never bounds a single prime by a
magnitude" — the connected cumulant supposedly *subtracts* the disconnected (obstructed) part.

## Why it REDUCES (four independent breaks)

**Break 1 — quantifier defeat (decisive).** The prize is a `∀`-prime statement: `M(p) ≤ C·√(n·log m)`
must hold at the *specific* prize prime `p ≈ n·2¹²⁸` (and uniformly in `p`, with `C` quantified
*before* `∀p` — see the in-tree `MomentLadderExceedsPrize`, and the recorded `∀q`-uniform retraction
issue444-thinness-essential). A family aggregate `fmean + √(card·fvar)` (a mean plus a spread)
controls the *typical* prime, never the *worst*/specific one. The structured primes where
`CumulantGaussPeriodBound.not_cumulantBound_of_excess` fires (Fermat `p = 65537`) are exactly the
outliers a mean+variance functional washes out. `fmean + √(card·fvar) ≤ slack` ⇏ `W p ≤ slack` for
the prize `p`. (`familyMean_le_does_not_bound_pointwise` below: an explicit two-prime countermodel.)

**Break 2 — `fmean` IS the obstructed magnitude (so the LHS already contains it).** By the proposer's
own identification `fmean P W = Σ_s ρ_s = the disconnected part = the BGK baseline = the obstructed
per-prime magnitude`. Since `√(P.card · fvar) ≥ 0` whenever the claim is even well-typed in `ℝ`
(`fvar ≥ 0`, it is a covariance quadratic form), the claim `fmean + √(card·fvar) ≤ slack` *implies*
`fmean ≤ slack` — i.e. it implies the BGK baseline bound itself. N1 does not subtract the baseline;
it ADDS a non-negative fluctuation on top of it. (`jointCumulant_implies_baseline` below.)

**Break 3 — the necessity obstruction survives averaging.** `moment_ladder_exceeds_prize` is
`∀ c, Σc = nʳ → (q·Σc²)^{1/2r} ≥ n`, holding for *each* prime's own count function. The family mean
of quantities each `≥ n` is `≥ n`: averaging cannot drop below the per-prime floor.
(`familyMean_moment_ge_card` below.) So the disconnected/mean channel is `≥ n > target` — REDUCES.

**Break 4 — the connected cumulant has no sign cancellation (it is a second magnitude).**
`Cov(χ_s, χ_{s'})` over the family is a count of *co-occurring* wraparound events `p | d_s ∧ p | d_{s'}`.
These are governed by independent congruence conditions; by CRT/Chebotarev they are asymptotically
uncorrelated (periods = exchangeable white-noise, issue444-periods-exchangeable), so `fvar ≈ 0` and
the claim degenerates to `fmean ≤ slack` (Break 2). Forcing `fvar < 0` to get genuine cancellation
makes `√(P.card · fvar)` ill-defined (`Real.sqrt` of a negative = 0), again collapsing to
`fmean ≤ slack`. Either way `fvar` is a non-negative-definite *quadratic form* (another count), not a
phase/sign cancellation — exactly the "just another count / second-order bound" the obstruction
forbids.

## What is proven here (axiom-clean countermodels)

* `familyMean_moment_ge_card` — averaging the per-prime moment bound over the family stays `≥ n`
  (Break 3): the disconnected channel cannot beat `n`.
* `jointCumulant_implies_baseline` — the N1 inequality implies the bare baseline `fmean ≤ slack`
  (Break 2): the obstructed magnitude is an additive lower term, not subtracted.
* `familyMean_le_does_not_bound_pointwise` — an explicit countermodel: a family mean below `slack`
  with one member far above it (Break 1): the aggregate does not bound the worst/prize prime.

**Honest scope.** REDUCES, not SKELETON: the claimed escape is illusory. `closesCharP = false`.
Axiom target `[propext, Classical.choice, Quot.sound]`. Issue #444.
-/

open Finset

namespace ProximityGap.Frontier.NovelJointCumulant

/-- **Break 3 (averaging does not escape the per-prime floor).** Suppose for each prime `j` in a
nonempty finite family we have a per-prime count function `c j : σ → ℝ` with total mass `nʳ`. By the
in-tree obstruction (`MomentMethodNoGo.moment_bound_ge_card`) every per-prime moment bound is `≥ n`.
Then the **family mean** of those per-prime moment bounds is still `≥ n` — the disconnected/mean
channel `fmean` cannot drop below the trivial count `n`. So the N1 "average over the family" move
inherits the obstruction verbatim. -/
theorem familyMean_moment_ge_card {σ ι : Type*} [Fintype σ] [Fintype ι]
    (c : ι → σ → ℝ) (n r : ℕ) (hr : 0 < r) (P : Finset ι) (hP : P.Nonempty)
    (hcount : ∀ j, ∑ s, c j s = (n : ℝ) ^ r) :
    (n : ℝ)
      ≤ (∑ j ∈ P,
          ((Fintype.card σ : ℝ) * ∑ s, (c j s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹)) / (P.card : ℝ) := by
  have hcard : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast hP.card_pos
  rw [le_div_iff₀ hcard]
  have hterm : ∀ j ∈ P, (n : ℝ)
      ≤ ((Fintype.card σ : ℝ) * ∑ s, (c j s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) := by
    intro j _
    exact MomentMethodNoGo.moment_bound_ge_card (c j) n r hr (hcount j)
  calc (n : ℝ) * (P.card : ℝ)
      = ∑ _j ∈ P, (n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ j ∈ P, ((Fintype.card σ : ℝ) * ∑ s, (c j s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) :=
        Finset.sum_le_sum hterm

/-- **Break 2 (the N1 inequality contains the obstructed magnitude as an additive lower term).**
The N1 claim is `fmean + √(card · fvar) ≤ slack`. Whenever it is even well-typed over `ℝ` — i.e. the
covariance quadratic form `fvar ≥ 0`, so `√(card · fvar) ≥ 0` — the inequality *implies* the bare
baseline bound `fmean ≤ slack`. But `fmean = Σ_s ρ_s` is, by the proposer's own identification, the
BGK random-divisibility baseline = the obstructed per-prime magnitude. So N1 does not subtract the
baseline; it stacks a non-negative fluctuation on top of it, and discharging N1 already requires
discharging BGK. (Here `fmean, fvar, slack, card` are abstract reals with `card, fvar ≥ 0`.) -/
theorem jointCumulant_implies_baseline
    {fmean fvar slack card : ℝ} (hcard : 0 ≤ card) (hfvar : 0 ≤ fvar)
    (hN1 : fmean + Real.sqrt (card * fvar) ≤ slack) :
    fmean ≤ slack := by
  have hsqrt : 0 ≤ Real.sqrt (card * fvar) := Real.sqrt_nonneg _
  linarith

/-- **Break 1 (a family aggregate does not bound the worst/prize member).** Concrete two-prime
countermodel. Take `slack = 2`, a family `{A, B}` with observables `W A = 0` and `W B = 100` (the
structured/Fermat outlier). The family mean is `(0 + 100)/2 = 50`… that already exceeds slack, so to
make N1's *mean* channel pass we instead exhibit the sharper failure: even a mean *below* slack
fails to bound the max. Take `W A = 0`, `W B = 3`, `slack = 2`. Then the family mean `3/2 ≤ slack`,
yet `W B = 3 > slack`. Hence `fmean ≤ slack` (the surviving content of N1 after Breaks 2–4) does NOT
imply `W p ≤ slack` at the prize prime `p = B`. The prize needs the pointwise/worst-case bound,
which the aggregate cannot deliver. -/
theorem familyMean_le_does_not_bound_pointwise :
    ∃ (W : Bool → ℝ) (slack : ℝ),
      (W false + W true) / 2 ≤ slack ∧ ¬ (W true ≤ slack) := by
  refine ⟨fun b => if b then 3 else 0, 2, ?_, ?_⟩
  · norm_num
  · norm_num

end ProximityGap.Frontier.NovelJointCumulant

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.NovelJointCumulant.familyMean_moment_ge_card
#print axioms ProximityGap.Frontier.NovelJointCumulant.jointCumulant_implies_baseline
#print axioms ProximityGap.Frontier.NovelJointCumulant.familyMean_le_does_not_bound_pointwise
