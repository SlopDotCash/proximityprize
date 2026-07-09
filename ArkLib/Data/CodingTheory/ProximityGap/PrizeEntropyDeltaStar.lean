/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# A proposed closed-form prize δ*: `δ* = 1 − ρ − H(ρ)/log₂(q·ε*)` (#389)

> **Status warning (2026-07-09).** `PrizePinConjecture` below is refuted as stated: its
> parameter `k` is the polynomial degree bound in `evalCode g n k`, whose dimension is
> `k + 1`, but the right-hand side uses the stale rate `k / n`.  The degree-zero
> counterexample is machine-checked in `PrizeEntropyPinRefuted`.  That file also proves
> that the naive actual-rate repair is false at the same finite instance:
> `3/4 < prizeDeltaStar (1/8) 14`.  Moreover, `Real.binEntropy` uses natural logarithms
> while the denominator below uses `logb 2`; the obvious base-consistent actual-rate repair
> is also false there, now in the opposite direction.  The four production prize instances
> remain open.

This file records a historical **closed-form candidate answer** to the Proximity Prize
(proximityprize.org, ABF26) for explicit constant-rate smooth-domain Reed–Solomon codes,
together with a rigorous discrete ladder ceiling and the historical statement that was
intended to supply its matching floor.

## The closed form

For rate `ρ = k/n`, list budget `B = q·ε*` (`≈ n` in the prize regime), the historical
Lean candidate defines `prizeDeltaStar ρ B := 1 − ρ − binEntropy ρ / log₂ B`.  Mathlib's
`binEntropy` is measured with natural logarithms, so this definition mixes entropy and
denominator units.  It lies strictly inside the prize
window `(1 − √ρ, 1 − ρ)` at every prize rate `ρ ∈ {1/2,1/4,1/8,1/16}` and budget
`log₂ B ∈ {40,64,128}` (numerically verified, `scripts/probes/probe_entropy_ceiling.py`).

## Historical derivation

The threshold `δ*` is where the **worst-case list** (= `q·ε_mca`) crosses `B = q·ε*`.
The explicit ladder family `w = x^{rm}+λx^{(r−1)m}` on the dyadic subgroup `μ_s` (`s = 2^μ`,
`m = n/s`) realises **exactly** the maximal subset-sum fibre count
`N_fib(s,r) = C(s/2 − r%2, ⌊r/2⌋)` (`TwoPowerFibreValue`, char 0; Lam–Leung antipodal
structure).  At constant rate `k = ρn` the construction forces `r ≈ ρs+2`, radius
`δ = 1 − r/s = 1 − ρ − 2/s`, list `C(s/2, ρ·s/2) = 2^{(s/2)·H(ρ)}`.  This exceeds `B` —
making `δ` BAD — exactly when `s > 2 log₂ B / H(ρ)`, i.e. `δ` drops below
`1 − ρ − H(ρ)/log₂ B`.  Thus the derivation uses base-two entropy; the Lean definition below
does not perform that conversion.  So **`δ* ≤ prizeDeltaStar ρ B`** was the proposed ceiling
(the ladder is an explicit bad family).  The conjecture was that this ceiling is **tight** —
equivalently,
that no word beats the ladder/`N_fib` count in the worst case (the worst-case list upper
bound, the one open wall).

## The proven ceiling (this file)

`kkh26_epsMCA_lower_bound_of_not_dvd` (KKH26WitnessSpread) gives the ladder lower bound on
`ε_mca` in the prize regime under the **mild, explicit, decidable** hypothesis `q > 2^μ`
and `q ∤ (collision resultants)` — a finite checkable prime spectrum, NOT the `s^{s/2} < q`
transfer wall.  Feeding it into `mcaDeltaStar_le_of_bad` gives the rigorous ceiling
`prizeDeltaStar_ceiling`.  No `CensusDomination`, no incomputable lemma.

## What remains

The intended matching lower bound is still the worst-case list bound for explicit smooth
RS above Johnson.  The historical `PrizeFloorStatement` and `PrizePinConjecture` definitions
below use the degree ratio `k / n`.  Replacing it by `(k + 1) / n` repairs that parameter
but does not make the generic finite equality true.  Dividing `Real.binEntropy` by `log 2`
repairs the unit mismatch but also fails at the finite counterexample.  No exact entropy pin
for a production prize instance is proved here.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `axiom`.
-/

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26

namespace ProximityGap.PrizeEntropy

/-- **The historical mixed-base closed-form candidate.**  The expression uses Mathlib's
natural-log `binEntropy` over the base-two denominator `logb 2 B`.  It is retained for the
historical results in this module; see `PrizeEntropyPinRefuted` for both the finite
counterexample and the refutation of the base-consistent repair. -/
noncomputable def prizeDeltaStar (ρ B : ℝ) : ℝ :=
  1 - ρ - Real.binEntropy ρ / Real.logb 2 B

/-- The closed form is strictly below capacity `1 − ρ` whenever `0 < ρ < 1`, `B > 2`
(the binary entropy is positive, the log is positive). -/
theorem prizeDeltaStar_lt_capacity {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hB : 2 < B) :
    prizeDeltaStar ρ B < 1 - ρ := by
  unfold prizeDeltaStar
  have hH : 0 < Real.binEntropy ρ := Real.binEntropy_pos hρ0 hρ1
  have hlog : 0 < Real.logb 2 B := Real.logb_pos (by norm_num) (by linarith)
  have : 0 < Real.binEntropy ρ / Real.logb 2 B := div_pos hH hlog
  linarith

/-- **The closed form is strictly ABOVE the Johnson radius** `1 − √ρ` (hence strictly inside
the prize window `(1−√ρ, 1−ρ)` together with `prizeDeltaStar_lt_capacity`), exactly when the
list budget is large enough: `log₂ B > H(ρ)/(√ρ − ρ)`.  At the prize rates and
`log₂ B ∈ {40,64,128}` this holds with room to spare — so the entropy ceiling is a genuine
*in-window* (beyond-Johnson) result, not a below-Johnson triviality. -/
theorem prizeDeltaStar_gt_johnson {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hbudget : Real.binEntropy ρ / (Real.sqrt ρ - ρ) < Real.logb 2 B) :
    1 - Real.sqrt ρ < prizeDeltaStar ρ B := by
  have hsqrt : ρ < Real.sqrt ρ := by
    have h1 : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ0.le
    nlinarith [Real.sqrt_nonneg ρ, Real.sqrt_pos.mpr hρ0]
  have hden : 0 < Real.sqrt ρ - ρ := by linarith
  have hH : 0 < Real.binEntropy ρ := Real.binEntropy_pos hρ0 hρ1
  have hlog : 0 < Real.logb 2 B := lt_trans (div_pos hH hden) hbudget
  -- from hbudget: H(ρ) < (√ρ − ρ)·logb, i.e. H(ρ)/logb < √ρ − ρ
  have hkey : Real.binEntropy ρ / Real.logb 2 B < Real.sqrt ρ - ρ := by
    rw [div_lt_iff₀ hlog]
    rw [div_lt_iff₀ hden] at hbudget
    linarith
  unfold prizeDeltaStar
  linarith

/-- **Historical degree-parameterized prize floor statement.**

This definition uses `k / n`, although `k` is the degree bound of `evalCode g n k` and the
actual code dimension is `k + 1`.  It is retained for compatibility; a corrected prize
statement must use the actual rate.

For the explicit smooth-domain RS code at constant rate `ρ`, every received word's list at
any radius strictly below `prizeDeltaStar ρ (q·ε*)` has at most `q·ε*` codewords — i.e. the
worst-case `ε_mca ≤ ε*`.  Proving this (the worst-case list upper bound for explicit smooth
RS strictly above Johnson) pins `δ* = prizeDeltaStar` exactly and resolves both grand
challenges.  This is the only remaining obligation; it contains no further open lemma. -/
def PrizeFloorStatement
    {p n : ℕ} [Fact p.Prime] [NeZero n] (g : ZMod p) (k : ℕ) (εstar : ℝ≥0∞) : Prop :=
  ∀ δ : ℝ≥0, (δ : ℝ) < prizeDeltaStar ((k : ℝ) / n) ((p : ℝ) * εstar.toReal) →
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n k) δ ≤ εstar

/-- **Refuted historical prize pin.**  This definition passes the degree ratio `k / n` to
`prizeDeltaStar` instead of the actual rate `(k + 1) / n`.  The theorem
`prizePinConjecture_degreeZero_F12289_REFUTED` gives a machine-checked counterexample. -/
def PrizePinConjecture
    {p n : ℕ} [Fact p.Prime] [NeZero n] (g : ZMod p) (k : ℕ) (εstar : ℝ≥0∞) : Prop :=
  (MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (A := ZMod p)
      (evalCode g n k) εstar : ℝ)
    = prizeDeltaStar ((k : ℝ) / n) ((p : ℝ) * εstar.toReal)

/-- **A rigorous discrete ladder ceiling (unconditional in its stated regime).**  The explicit
ladder family forces `δ* ≤ 1 − r/2^μ` for the dyadic construction, under the mild decidable
hypothesis
that `q` divides no collision resultant (NOT the `s^{s/2} < q` transfer wall).  This is the
machine-checked rung ceiling, with no `CensusDomination` and no incomputable input.  This theorem
does not identify its right-hand side with the mixed-base `prizeDeltaStar` definition above. -/
theorem prizeDeltaStar_ceiling {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m) (hpμ : 2 ^ μ < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1))
    (hndvd : ∀ d₁ ∈ sigData (2 ^ (μ - 1)) r, ∀ d₂ ∈ sigData (2 ^ (μ - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant μ d₁ d₂)
    (εstar : ℝ≥0∞)
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n ((r - 2) * m)) εstar
      ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) :=
  MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar
      (kkh26_epsMCA_lower_bound_of_not_dvd hμ hm hn hg hpμ hr2 hr hndvd))

end ProximityGap.PrizeEntropy

#print axioms ProximityGap.PrizeEntropy.prizeDeltaStar_lt_capacity
#print axioms ProximityGap.PrizeEntropy.prizeDeltaStar_gt_johnson
#print axioms ProximityGap.PrizeEntropy.prizeDeltaStar_ceiling
