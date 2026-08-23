/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PowerSumRatioMonotone

/-!
# The two-sided nested bracket on the spectral max (#444)

**What this assembles.** The moment localization of `max_i a_i` on a nonnegative finite spectrum now
has both ends in tree:
- the LOWER side rises: `powerSum_ratio_monotone` (`S_{t+1}/S_t ↑`) with `powerSum_ratio_le_max`
  (`S_{t+1}/S_t ≤ max a`), so the ratio rises to `max a` from below;
- the UPPER side falls: the moment root `(S_{2r})^{1/(2r)}` is antitone toward `max a`
  (`_MomentLadderAntitone.ladder_antitone`) and dominates it
  (`MomentSupNormBridge.sup_le_moment_root`).

This file states the assembled **two-sided bracket at a fixed depth** as one statement and proves the
genuinely new structural fact the assembly was missing: the LOWER bracket is itself bounded by EVERY
power-sum root (`S_{t+1}/S_t ≤ (S_s)^{1/s}` for the relevant exponents), so the rising ratio and the
falling root form a *nested* interval whose ends never cross.

## What is PROVEN here (axiom target `{propext, Classical.choice, Quot.sound}`)

* `ratio_le_max_le_pow_root` (HEADLINE) — the two-sided bracket: for `t ≥ 1`, `S_t > 0`, `M` an
  entrywise upper bound, `(S_{t+1})/S_t ≤ M` and `M ≤ (S_t)^{1/t}` simultaneously when `M = max a`
  is realised, i.e. `S_{t+1}/S_t ≤ max a ≤ (S_t)^{1/t}` whenever the max is attained in the spectrum.
  (We state it with `max a` supplied as a realised upper bound `b₀ ∈ s`, `a b₀ = M`.)
* `ratio_le_pow_root` — the nesting: the LOWER ratio is ≤ the UPPER `t`-th root directly,
  `S_{t+1}/S_t ≤ (S_t)^{1/t}` (no realisation hypothesis), so the bracket ends are ordered for free.

## Honesty / scope (rules 1,3,6 + ASYMPTOTIC GUARD)

Field-universal structural identity on an arbitrary nonnegative spectrum. The EASY/honest LOWER
direction localizes `max a = M(n)²` (the prize sup-norm squared on `b ≠ 0`) from BELOW; the UPPER
root is the same wrong-side direction's companion. By rule 3 this cannot prove the thinness-essential
prize and does not pretend to. NO CORE closure, no char-p transfer / capacity / beyond-Johnson /
growth-law claim; orthogonal to the cliff-at-n/2 (a localization of the max value, not the over-det
face). The matching UPPER bound `M(n) ≤ C√(n log(p/n))` is the wall, untouched.

## References
- `PowerSumRatioMonotone` (the lower-bracket monotonicity this builds on).
- `_MomentLadderAntitone.ladder_antitone` / `MomentSupNormBridge.sup_le_moment_root` (the upper side).
-/

open Finset

set_option linter.unusedSectionVars false

namespace ProximityGap.Frontier.PowerSumMaxBracket

open ProximityGap.Frontier.PowerSumRatioMonotone

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **The lower ratio is bounded by the `t`-th power-sum root** (the bracket-nesting fact). For a
nonnegative spectrum `a` and `t ≥ 1` with `S_t = ∑ a_i^t > 0`:
`S_{t+1}/S_t ≤ (S_t)^{1/t}`. So the rising ratio (lower bracket) never exceeds the falling
moment-root (upper bracket): the two-sided interval around `max a` is *nested*. -/
theorem ratio_le_pow_root (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (t : ℕ) (ht : 1 ≤ t)
    (hSt : 0 < ∑ i, (a i) ^ t) :
    (∑ i, (a i) ^ (t + 1)) / (∑ i, (a i) ^ t) ≤ (∑ i, (a i) ^ t) ^ ((1 : ℝ) / t) := by
  -- the max realises an upper bound `M`; both ends are ≤ `M`, but we prove the direct ordering
  -- via `max a ≤ root` and `ratio ≤ max a`. Pick `M = max_i a_i`.
  classical
  obtain ⟨b₀, -, hb₀⟩ := Finset.exists_max_image Finset.univ a ⟨Classical.arbitrary ι,
    Finset.mem_univ _⟩
  set M : ℝ := a b₀ with hMdef
  have hMnn : 0 ≤ M := ha b₀
  have hub : ∀ i, a i ≤ M := fun i => hb₀ i (Finset.mem_univ i)
  -- lower: ratio ≤ M
  have hlow : (∑ i, (a i) ^ (t + 1)) / (∑ i, (a i) ^ t) ≤ M :=
    powerSum_ratio_le_max a ha M hub t hSt
  -- upper: M ≤ (S_t)^{1/t}, since M^t = (a b₀)^t ≤ S_t and `x ↦ x^{1/t}` is monotone
  have hup : M ≤ (∑ i, (a i) ^ t) ^ ((1 : ℝ) / t) := by
    have hterm : M ^ t ≤ ∑ i, (a i) ^ t :=
      Finset.single_le_sum (f := fun i => (a i) ^ t)
        (fun i _ => pow_nonneg (ha i) t) (Finset.mem_univ b₀)
    have hroot : (M ^ t : ℝ) ^ ((1 : ℝ) / t) ≤ (∑ i, (a i) ^ t) ^ ((1 : ℝ) / t) :=
      Real.rpow_le_rpow (pow_nonneg hMnn t) hterm (by positivity)
    have hMlhs : (M ^ t : ℝ) ^ ((1 : ℝ) / t) = M := by
      rw [one_div, Real.pow_rpow_inv_natCast hMnn (by omega)]
    rwa [hMlhs] at hroot
  exact le_trans hlow hup

/-- **The two-sided nested bracket on the realised spectral max.** If `b₀` realises the max
(`∀ i, a i ≤ a b₀`) and `S_t > 0`, then
`S_{t+1}/S_t ≤ a b₀ ≤ (S_t)^{1/t}` — the rising lower ratio and the falling moment root bracket the
spectral max simultaneously. -/
theorem ratio_le_max_le_pow_root (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (b₀ : ι)
    (hmax : ∀ i, a i ≤ a b₀) (t : ℕ) (ht : 1 ≤ t) (hSt : 0 < ∑ i, (a i) ^ t) :
    (∑ i, (a i) ^ (t + 1)) / (∑ i, (a i) ^ t) ≤ a b₀
      ∧ a b₀ ≤ (∑ i, (a i) ^ t) ^ ((1 : ℝ) / t) := by
  refine ⟨powerSum_ratio_le_max a ha (a b₀) hmax t hSt, ?_⟩
  have hMnn : 0 ≤ a b₀ := ha b₀
  have hterm : (a b₀) ^ t ≤ ∑ i, (a i) ^ t :=
    Finset.single_le_sum (f := fun i => (a i) ^ t)
      (fun i _ => pow_nonneg (ha i) t) (Finset.mem_univ b₀)
  have hroot : ((a b₀) ^ t : ℝ) ^ ((1 : ℝ) / t) ≤ (∑ i, (a i) ^ t) ^ ((1 : ℝ) / t) :=
    Real.rpow_le_rpow (pow_nonneg hMnn t) hterm (by positivity)
  have hMlhs : ((a b₀) ^ t : ℝ) ^ ((1 : ℝ) / t) = a b₀ := by
    rw [one_div, Real.pow_rpow_inv_natCast hMnn (by omega)]
  rwa [hMlhs] at hroot

end ProximityGap.Frontier.PowerSumMaxBracket

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.PowerSumMaxBracket.ratio_le_pow_root
#print axioms ProximityGap.Frontier.PowerSumMaxBracket.ratio_le_max_le_pow_root
