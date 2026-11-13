/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# WF407 / T357-10-derand — fold-transport co-location: the unfolding-loss arithmetic

**Thread.** `T357-10-derand` (= 357-T10 / 232-T06): "derandomize random-RS capacity to explicit
smooth". Random/folded Reed–Solomon list-decodes to capacity `1 − ρ − η`. The question is whether a
**FRI fold-transport** carries that capacity result down the smooth 2-power tower to an EXPLICIT
smooth domain `μ_n`, `n = 2^μ`.

This file is the **fold-transport / co-location half** of the target (the companion
`Sweep_A20_ThirdMomentDerandGap.lean` is the *moment* half: M1/M2 are domain-independent — proven —
so the smooth-vs-random difference first appears at the third moment, whose signal is `Θ(1/q²)`,
super-exponentially below `ε*` at prize scale).

## The reduction (companion probe `scripts/probes/probe_fold_transport_feasibility.py`)

Fold arity `s = 2` on the squaring tower `μ_n → μ_{n/2}` (sends `x` and `−x = g^{n/2}x` to `x²`; a
downstairs BLOCK is the antipodal pair `{x, −x}`). A coordinate-error fraction `δ` unfolds to a
folded-symbol-error fraction in `[δ, s·δ]`; write the realized multiplier as the **unfolding loss**
`L ∈ [1, s]`. The fold route certifies a (MCA-good) radius `δ` iff `L·δ ≤ 1 − ρ − ε`, so it beats
the Johnson radius `1 − √ρ` iff

  `(1 − ρ)/L > 1 − √ρ`  ⇔  `L < L*(ρ) := (1 − ρ)/(1 − √ρ)`.

**Exact closed form** (proven below): `L*(ρ) = 1 + √ρ`, since `1 − ρ = (1 − √ρ)(1 + √ρ)`.

## What is proven here (axiom-clean real/NNReal arithmetic)

* `Lstar_eq` : `L*(ρ) = 1 + √ρ` for `0 ≤ ρ < 1` (the exact closed form).
* `Lstar_lt_two` : `L*(ρ) < 2` for `0 < ρ < 1` — so the smallest fold arity `s = 2` gives a
  worst-case (full-spread) loss `L = s = 2 ≥ L*(ρ)`: **naive fold-transport never beats Johnson**.
* `colocation_threshold_eq` : the co-location fraction the smooth tower must FORCE for the route to
  survive at `s = 2` is exactly `1 − √ρ` (`= L* − 1`), i.e. the Johnson radius itself.
* `route_dead_if_colocation_below_threshold` : if some MCA-bad error support has co-location
  fraction `< 1 − √ρ` (the probe's measured finding — named as a `Prop`, NOT proven here), then the
  realized unfolding loss `L = 1 + spread = 2 − coloc > 1 + √ρ = L*`, so the fold route does NOT
  beat Johnson on that pattern: the derandomization is dead.

## Honesty

`L*(ρ) = 1 + √ρ`, `L* < 2`, and the co-location threshold are **exact theorems** about the route's
numerology. The *empirical* input — "MCA-bad error supports on smooth `μ_n` spread below `1 − √ρ`"
— is the companion probe's measurement (`probe_fold_transport_feasibility.py` set up the question;
`wf407_T357-10-derand_colocation.py` ran it: min co-location `≈ 0.40` at `ρ = 1/4` vs threshold
`0.50`, `≈ 0.0` at `ρ = 1/2` vs `0.293`, over all bad `γ` for KKH26-monomial AND random stacks on
`μ_8`, exact over `F_17/F_41/F_97`). It is named here as the hypothesis `SpreadWitness` and
*consumed*, not re-derived in Lean. No fabricated closure: this CLOSES the fold-transport route by
an honest size/spread argument, it does NOT prove `δ*`.
-/

namespace ArkLib.ProximityGap.WF407.FoldColocation

open Real

/-- The unfolding-loss threshold `L*(ρ) = (1 − ρ)/(1 − √ρ)`: the fold route beats the Johnson radius
`1 − √ρ` iff the realized unfolding loss `L` is strictly below `L*(ρ)`. -/
noncomputable def Lstar (ρ : ℝ) : ℝ := (1 - ρ) / (1 - Real.sqrt ρ)

/-- **The exact closed form `L*(ρ) = 1 + √ρ`.** Key fact: `1 − ρ = (1 − √ρ)(1 + √ρ)` (difference of
squares with `(√ρ)² = ρ`), and `1 − √ρ ≠ 0` since `ρ < 1 ⟹ √ρ < 1`. -/
theorem Lstar_eq {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Lstar ρ = 1 + Real.sqrt ρ := by
  have hsq : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ0
  have hsqlt1 : Real.sqrt ρ < 1 := by
    have : Real.sqrt ρ < Real.sqrt 1 := by
      apply Real.sqrt_lt_sqrt hρ0 hρ1
    simpa using this
  have hden : (1 : ℝ) - Real.sqrt ρ ≠ 0 := by
    have : (0 : ℝ) < 1 - Real.sqrt ρ := by linarith
    exact ne_of_gt this
  unfold Lstar
  rw [div_eq_iff hden]
  -- (1 + √ρ)(1 − √ρ) = 1 − (√ρ)² = 1 − ρ
  nlinarith [hsq]

/-- **Naive fold-transport never beats Johnson.** `L*(ρ) < 2` for `0 < ρ < 1`, so the smallest fold
arity `s = 2` gives a worst-case (full-spread) loss `L = s = 2 ≥ L*(ρ)` — the route is DEAD under
worst-case error spreading at every prize rate `ρ ∈ {1/2, 1/4, 1/8, 1/16}`. -/
theorem Lstar_lt_two {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Lstar ρ < 2 := by
  rw [Lstar_eq (le_of_lt hρ0) hρ1]
  have hsqlt1 : Real.sqrt ρ < 1 := by
    have : Real.sqrt ρ < Real.sqrt 1 := Real.sqrt_lt_sqrt (le_of_lt hρ0) hρ1
    simpa using this
  linarith

/-- The required co-location fraction at fold arity `s = 2`. With `s = 2`, the realized unfolding
loss is `L = 1 + spread`, where `spread = 1 − coloc` is the fraction of error coordinates landing in
FRESH downstairs blocks (antipodal partner NOT also an error). The route beats Johnson iff
`L < L* = 1 + √ρ`, i.e. iff `spread < √ρ`, i.e. iff `coloc > 1 − √ρ`. So the threshold the smooth
tower must force is exactly `1 − √ρ`. -/
noncomputable def colocationThreshold (ρ : ℝ) : ℝ := 1 - Real.sqrt ρ

/-- The required co-location fraction equals `L* − 1 = √ρ`'s complement, i.e. the Johnson radius
itself: `colocationThreshold ρ = (1 − √ρ)` and also `= 2 − L*(ρ)` (the spread budget complement). -/
theorem colocation_threshold_eq {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    colocationThreshold ρ = 2 - Lstar ρ := by
  rw [Lstar_eq hρ0 hρ1]
  unfold colocationThreshold
  ring

/-- The realized unfolding loss at fold arity `s = 2` given a co-location fraction `coloc`:
`L = 1 + spread = 1 + (1 − coloc) = 2 − coloc`. -/
noncomputable def realizedLoss (coloc : ℝ) : ℝ := 2 - coloc

/-- **A spread witness** (the probe's measured finding, named as a hypothesis): there is an MCA-bad
error support on the smooth domain whose co-location fraction is strictly below the threshold
`1 − √ρ`. This is what `wf407_T357-10-derand_colocation.py` found at every tested toy instance (min
co-location `≈ 0.40 < 0.50` at `ρ = 1/4`; `≈ 0.0 < 0.293` at `ρ = 1/2`). It is OPEN to prove this
for all prize instances; we name it and consume it. -/
def SpreadWitness (ρ coloc : ℝ) : Prop := coloc < colocationThreshold ρ

/-- **The fold route is dead on a spread pattern.** If an MCA-bad error support has co-location
fraction `coloc` strictly below the threshold `1 − √ρ` (`SpreadWitness`), then its realized
unfolding loss `L = 2 − coloc` strictly exceeds `L*(ρ) = 1 + √ρ`. Hence on that pattern the fold
route certifies only `δ ≤ (1 − ρ)/L < 1 − √ρ` (below Johnson): the derandomization cannot carry
capacity to the explicit smooth domain. -/
theorem route_dead_if_colocation_below_threshold {ρ coloc : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : SpreadWitness ρ coloc) :
    Lstar ρ < realizedLoss coloc := by
  rw [Lstar_eq hρ0 hρ1]
  unfold realizedLoss
  unfold SpreadWitness colocationThreshold at hw
  linarith

/-- **Quantitative corollary at `ρ = 1/4` (rate the probe measured most).** The threshold is
`1 − √(1/4) = 1/2`, and the probe's minimum co-location `coloc = 2/5 = 0.4 < 1/2` is a spread
witness, so the realized loss `2 − 2/5 = 8/5 = 1.6` exceeds `L*(1/4) = 1 + 1/2 = 3/2 = 1.5`. -/
theorem route_dead_at_quarter_rate :
    Lstar (1/4 : ℝ) < realizedLoss (2/5 : ℝ) := by
  apply route_dead_if_colocation_below_threshold (by norm_num) (by norm_num)
  unfold SpreadWitness colocationThreshold
  rw [show Real.sqrt (1/4 : ℝ) = 1/2 by
    rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
  norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms Lstar_eq
#print axioms Lstar_lt_two
#print axioms colocation_threshold_eq
#print axioms route_dead_if_colocation_below_threshold
#print axioms route_dead_at_quarter_rate

end ArkLib.ProximityGap.WF407.FoldColocation
