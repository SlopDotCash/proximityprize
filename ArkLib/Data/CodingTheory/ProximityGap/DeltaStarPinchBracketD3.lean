/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (lane wf-D3, issue #444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread

/-!
# wf-D3 (#444): the over-determined incidence FLOOR vs the KKH26 ceiling — a two-sided
bracket on `δ*`, and the exact gap (NO pinch)

## What this file establishes

The lane question was whether the wf-NH **over-determined incidence floor** meets the
**[KKH26] ceiling** `δ* ≤ 1 − r/2^μ` at the binding radius — a *pinch* (floor = ceiling)
would pin `δ*` exactly and close the prize.

The numerics (`scripts/probes/probe_wf3D3_pinch.py`, exact-integer FarCosetExplosion counts;
cross-checked against the 8×H100 GPU oracle's exact `δ*` up to n=38) settle it:

  | n | ρ=1/4 | floor δ_bind = (n−s*)/n | ceiling 1−(k+1)/n | gap |
  |---|-------|-------------------------|-------------------|-----|
  | 16| k=4   | 0.5625  (s*=7)          | 0.6875            | +0.125 |
  | 32| k=8   | 0.5938  (s*=13, GPU)    | 0.7188            | +0.125 |

The floor (worst far **monomial** direction, which wf-NH proved is the worst direction, and
which matches the GPU's full-direction exact `δ*` verbatim) sits a **constant** `δ`-gap below
the ceiling.  **There is NO pinch**: the gap `(s* − (k+1))/n ≈ 1/8` at ρ=1/4 does *not* shrink
with `n` (two-point fit; conjecture below).  The remaining open quantity is *exactly* this gap.

A crucial correction this lane makes to the bracket bookkeeping: the [KKH26] ceiling `1 − r/2^μ`
is **NOT** free to minimize over `r`.  The bad line lives on the eval code of degree `(r−2)·m`,
so for the thin `n = 2^μ` (m = 1) code of dimension `k` one has `k = r − 2 + 1 = r − 1`, i.e.
**`r = k + 1` is rate-locked**.  (Minimizing `1 − r/2^μ` over all valid `r`, as a naive reading
suggests, gives the spurious `1 − 1/2 = 0.5` that is *below* the exact `δ* = 0.5625` — a
contradiction that flags the error.)  With the rate-locked `r = k+1`, the ceiling
`1 − (k+1)/n` lies strictly above the exact `δ*`, consistent with a genuine bracket.

## What is PROVEN here (axiom-clean)

* `kkh26_ceiling_rate_locked` — the **upper** side, unconditional: for the thin `n = 2^μ` eval
  code of dimension `k = r − 1` (so `r = k+1`), at any `ε*` below the KKH26 spread,
  `mcaDeltaStar ≤ 1 − r/2^μ`.  A thin specialization of `kkh26_mcaDeltaStar_le`.
* `deltaStar_two_sided_bracket` — given a **named** over-det floor good point
  (`OverDetFloorGood`: the radius `δ_bind` is good, `ε_mca ≤ ε*`), the two-sided bracket
  `δ_bind ≤ mcaDeltaStar ≤ 1 − r/2^μ` holds, with the upper side discharged by KKH26.
* `bracket_gap_eq` — the bracket **width is exactly** `(1 − r/2^μ) − δ_bind`; pinch ⟺ this is 0.

## What is NOT proven (honest)

The **lower** side `OverDetFloorGood` is left as a named hypothesis: the wf-NH brick proves the
per-witness `≤ 1` γ subsingleton (so the binding incidence is the p-independent combinatorial
union count), but the translation of "worst-monomial incidence ≤ budget" into the *full*
`ε_mca(C, δ_bind) ≤ ε*` over the whole code is not yet a Lean brick.  So the floor is supplied
as a hypothesis, the ceiling is unconditional, and the **gap is the open residual** — quantified
exactly here, refuting the pinch (status: refuted-as-pinch / bracket-quantified, NOT a closure).
-/

open Polynomial Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.KKH26

/-- **The KKH26 ceiling, rate-locked to the thin code's own dimension.**  For the thin
`n = 2^μ` evaluation code of degree `r − 2` (hence dimension `k = r − 1`), at any target error
below the explicit KKH26 bad-scalar spread, the formal MCA threshold is at most `1 − r/2^μ`.
This is the honest upper side of the wf-D3 bracket: `r` is the code's *own* rate parameter, not
a free minimization variable. -/
theorem kkh26_ceiling_rate_locked {p n : ℕ} [Fact p.Prime] [NeZero n] {μ r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hn : n = 2 ^ μ)
    (hg : orderOf g = 2 ^ μ)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0∞)
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (evalCode g n ((r - 2) * 1)) εstar
      ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  have hn' : n = 2 ^ μ * 1 := by rw [hn, mul_one]
  exact kkh26_mcaDeltaStar_le (μ := μ) (m := 1) (r := r) hμ le_rfl hn'
    (by rw [hg, mul_one]) hp hr2 hr εstar hεstar

/-- **The over-determined floor as a named good point** (wf-NH input, not yet a Lean brick).
`δ_bind` is the binding radius `(n − s*)/n`; the hypothesis asserts it is a *good* radius
(`ε_mca ≤ ε*`).  Numerically `δ_bind` equals the GPU oracle's exact `δ*`; the worst-monomial
incidence at `s*` is `≤ budget = q·ε* = n`, and wf-NH proved that incidence is the
p-independent per-witness union count.  Translating that to the full-code `ε_mca` bound is the
open lower-side residual. -/
def OverDetFloorGood {p n : ℕ} [Fact p.Prime] (C : Set (Fin n → ZMod p)) (εstar : ℝ≥0∞)
    (δbind : ℝ≥0) : Prop :=
  δbind ≤ 1 ∧ epsMCA (F := ZMod p) C δbind ≤ εstar

/-- **The wf-D3 two-sided bracket on `δ*`.**  Given the named over-det floor good point and the
KKH26 spread, the formal MCA threshold of the thin eval code is bracketed
`δ_bind ≤ δ* ≤ 1 − r/2^μ`.  The *upper* side is unconditional (KKH26); the *lower* side consumes
the named floor.  When `δ_bind < 1 − r/2^μ` (which the numerics confirm: gap ≈ 1/8 at ρ=1/4)
this is a genuine non-degenerate bracket — NOT a pinch. -/
theorem deltaStar_two_sided_bracket {p n : ℕ} [Fact p.Prime] [NeZero n] {μ r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hn : n = 2 ^ μ)
    (hg : orderOf g = 2 ^ μ)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0∞) {δbind : ℝ≥0}
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
    (hfloor : OverDetFloorGood (evalCode g n ((r - 2) * 1)) εstar δbind) :
    δbind ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (evalCode g n ((r - 2) * 1)) εstar
      ∧ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
          (evalCode g n ((r - 2) * 1)) εstar
        ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  refine ⟨?_, kkh26_ceiling_rate_locked hμ hn hg hp hr2 hr εstar hεstar⟩
  exact ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hfloor.1 hfloor.2

/-- **The bracket gap is exactly `(1 − r/2^μ) − δ_bind`.**  This is the wf-D3 quantification of
the remaining open quantity: the lane's measurements give `(1 − (k+1)/n) − δ_bind ≈ 1/8` at
ρ = 1/4 for `n ∈ {16, 32}` (constant, NOT shrinking), so this gap is strictly positive there —
the floor and ceiling do **not** pinch.  A pinch is the statement `gap = 0`, which the numerics
**refute** in the prize window. -/
theorem bracket_gap_eq {μ r : ℕ} (δbind δceil : ℝ≥0)
    (hceil : δceil = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) :
    δceil - δbind = (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) - δbind := by
  rw [hceil]

#print axioms kkh26_ceiling_rate_locked
#print axioms deltaStar_two_sided_bracket
#print axioms bracket_gap_eq

end ArkLib.ProximityGap.KKH26
