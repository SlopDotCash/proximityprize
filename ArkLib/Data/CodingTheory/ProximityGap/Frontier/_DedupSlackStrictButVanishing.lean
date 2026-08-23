/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The dedup slack `N_r < C(n,r)` is STRICT but FRACTIONALLY VANISHING at `r = log n` (#444)

## The A3 escape question (what this measures)

`_CoreA3_BackwardProof.lean` reduces the prize escape question to one combinatorial dichotomy
(dossier `deltastar-444-prize-regime-established-2026-06-16.md` sec VI lever 2 + sec IX): the
candidate weaker-sufficient statement `WeakestSuff` is weaker-or-equal to BCHKS 1.12, the gap being
the **dedup slack** `Sigma_r - D >= 0`. Whether `WeakestSuff` is a REAL escape (strictly below the
wall) or EQUAL to it (the wall) reduces to:

> Is the deduplication `D <= Sigma_r` **STRICT** at logarithmic depth `r ~ log n`?

This file instantiates that question on a concrete, p-INDEPENDENT object using the just-landed
spectrum closed form `_SubsetSumSpectrumClosedForm.spectrumCount` (push `89151523f`), over the thin
dyadic group `mu_n` (`n = 2^a`, `m = n/2`):

* `Sigma_r` (un-deduplicated) `= C(n, r)`: all `r`-subsets counted with multiplicity.
* `D = N_r = spectrumCount m r = Σ_{k ≡ r (2)} C(m,k) 2^k`: the DISTINCT `r`-subset-sum count.
* dedup slack `slack(n,r) = C(n,r) − N_r >= 0`, STRICT iff `> 0` (two distinct `r`-subsets collide).

## The finding (exact, p-independent, NON-moment; probe
`scripts/probes/probe_dedup_slack_strict_at_log_depth.py` + `..._ratio_trend_...`)

At the BINDING log depth `r = log₂ n` the dedup is **STRICT at every tested tower level** AND the
slack GROWS in absolute terms:

| n   | r=log₂n | C(n,r)  | N_r     | slack  |
|-----|---------|---------|---------|--------|
| 8   | 3       | 56      | 40      | 16     |
| 16  | 4       | 1820    | 1233    | 587    |
| 32  | 5       | 201376  | 144288  | 57088  |

BUT the slack **FRACTION** `f(n) = slack/C(n,r)` is monotonically DECREASING from `n=16` onward
(`0.323 → 0.283 → 0.219 → 0.156 → … → 0.0055` at `n = 16384`), with survival `N_r/C(n,r) → 1`.

## Honest verdict (rule 4 constraint lemma; ASYMPTOTIC GUARD compliant)

The dedup at the binding log depth is STRICT (so the A3 `WeakestSuff` escape direction is
NON-vacuous as a strict inequality) but **fractionally vanishing**: asymptotically almost all
`r`-subsets have distinct sums at `r = log n`, so the dedup yields no fractional savings there. This
QUANTIFIES the dossier's "in-tree evidence leans wall": a strict-but-fractionally-thin dedup is NOT
a real escape. It does NOT close BCHKS 1.12 (the slack could still matter at the budget scale `~n`,
which this does not bound), makes NO capacity / beyond-Johnson / sub-linear / growth-law claim, and
leaves the cliff-at-n/2 untouched. CORE `M(mu_n) <= C sqrt(n log(p/n))` is UNCHANGED / OPEN.

No `sorry`, no `axiom`. The slack values are exact `Nat`; the fraction monotonicity is exact `Nat`
cross-multiplication (`slack₁ · C₂ > slack₂ · C₁`), decided by `norm_num`.

Issue #444.
-/

open Finset

namespace ProximityGap.DedupSlackStrictVanishing

/-- The distinct `r`-subset-sum count over `mu_{2m}` (the in-tree `spectrumCount`, re-declared
locally so this file is self-contained): `N_r = Σ_{k ≡ r (2), 0 ≤ k ≤ min(r, 2m−r)} C(m,k) 2^k`. -/
def specCount (m r : ℕ) : ℕ :=
  ∑ k ∈ (range (min r (2 * m - r) + 1)).filter (fun k => k % 2 = r % 2), m.choose k * 2 ^ k

/-- The un-deduplicated `r`-subset count `Sigma_r = C(n, r)`. -/
def sigmaCount (n r : ℕ) : ℕ := n.choose r

/-- The dedup slack `Sigma_r − N_r` at `(n = 2m, r)`. -/
def dedupSlack (m r : ℕ) : ℕ := sigmaCount (2 * m) r - specCount m r

/-! ## Exact anchor values at the binding log depth `r = log₂ n` -/

/-- `n = 8` (`m = 4`, `r = 3`): `C(8,3) = 56`, `N_3 = 40`, slack `16 > 0` (STRICT). -/
theorem anchor_n8 :
    sigmaCount 8 3 = 56 ∧ specCount 4 3 = 40 ∧ dedupSlack 4 3 = 16 ∧ 0 < dedupSlack 4 3 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- `n = 16` (`m = 8`, `r = 4`): `C(16,4) = 1820`, `N_4 = 1233`, slack `587 > 0` (STRICT). -/
theorem anchor_n16 :
    sigmaCount 16 4 = 1820 ∧ specCount 8 4 = 1233 ∧ dedupSlack 8 4 = 587
      ∧ 0 < dedupSlack 8 4 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- `n = 32` (`m = 16`, `r = 5`): `C(32,5) = 201376`, `N_5 = 144288`, slack `57088 > 0` (STRICT). -/
theorem anchor_n32 :
    sigmaCount 32 5 = 201376 ∧ specCount 16 5 = 144288 ∧ dedupSlack 16 5 = 57088
      ∧ 0 < dedupSlack 16 5 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **Dedup is STRICT at the binding log depth across the tower `n ∈ {8,16,32}`.** Each binding
`r = log₂ n` has `N_r < C(n,r)` (some two distinct `r`-subsets collide). -/
theorem dedup_strict_on_tower :
    specCount 4 3 < sigmaCount 8 3 ∧
    specCount 8 4 < sigmaCount 16 4 ∧
    specCount 16 5 < sigmaCount 32 5 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The slack GROWS in absolute terms** up the tower at the binding depth: `16 < 587 < 57088`. -/
theorem slack_grows_absolute :
    dedupSlack 4 3 < dedupSlack 8 4 ∧ dedupSlack 8 4 < dedupSlack 16 5 := by
  refine ⟨by decide, by decide⟩

/-! ## The wall-leaning mechanism: the slack FRACTION decreases (exact Nat cross-multiplication)

`f(n) = slack(n)/C(n,r)`. `f(n₁) > f(n₂) ⟺ slack₁ · C₂ > slack₂ · C₁` (positive denominators). -/

/-- **`f(16) > f(32)`** at the binding depth: `587 · 201376 > 57088 · 1820`
(`118207712 > 103900160`). -/
theorem frac_dec_16_32 :
    dedupSlack 8 4 * sigmaCount 32 5 > dedupSlack 16 5 * sigmaCount 16 4 := by
  decide

/-- **`f(32) > f(64)`**, the fraction continues to drop (binding depth `r=6` at `n=64`):
`C(64,6) = 74974368`, `N_6 = 58573633`, slack `16400735`; `57088 · 74974368 > 16400735 · 201376`. -/
theorem frac_dec_32_64 :
    sigmaCount 64 6 = 74974368 ∧ specCount 32 6 = 58573633 ∧ dedupSlack 32 6 = 16400735 ∧
    dedupSlack 16 5 * sigmaCount 64 6 > dedupSlack 32 6 * sigmaCount 32 5 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The wall-leaning verdict (headline).** At the binding log depth `r = log₂ n`, the dedup is
STRICT (`N_r < C(n,r)`) at every tower level `n ∈ {8,16,32}`, the slack GROWS in absolute terms,
YET the slack FRACTION strictly DECREASES (`f(16) > f(32) > f(64)`). A strict-but-fractionally-
vanishing dedup is the precise quantitative form of "the dedup gives no asymptotic fractional
savings at the binding depth", the A3 `WeakestSuff` escape is strict but asymptotically thin,
leaning WALL, NOT a real fractional escape. (Does NOT close BCHKS 1.12: the budget-scale `~n`
relevance is not bounded here.) -/
theorem strict_but_fractionally_vanishing :
    -- strict at the binding depth across the tower
    (specCount 4 3 < sigmaCount 8 3 ∧ specCount 8 4 < sigmaCount 16 4
      ∧ specCount 16 5 < sigmaCount 32 5) ∧
    -- slack grows in absolute terms
    (dedupSlack 4 3 < dedupSlack 8 4 ∧ dedupSlack 8 4 < dedupSlack 16 5) ∧
    -- but the slack fraction strictly decreases (f(16) > f(32) > f(64))
    (dedupSlack 8 4 * sigmaCount 32 5 > dedupSlack 16 5 * sigmaCount 16 4 ∧
      dedupSlack 16 5 * sigmaCount 64 6 > dedupSlack 32 6 * sigmaCount 32 5) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

end ProximityGap.DedupSlackStrictVanishing

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.DedupSlackStrictVanishing.anchor_n8
#print axioms ProximityGap.DedupSlackStrictVanishing.anchor_n16
#print axioms ProximityGap.DedupSlackStrictVanishing.anchor_n32
#print axioms ProximityGap.DedupSlackStrictVanishing.dedup_strict_on_tower
#print axioms ProximityGap.DedupSlackStrictVanishing.slack_grows_absolute
#print axioms ProximityGap.DedupSlackStrictVanishing.frac_dec_16_32
#print axioms ProximityGap.DedupSlackStrictVanishing.frac_dec_32_64
#print axioms ProximityGap.DedupSlackStrictVanishing.strict_but_fractionally_vanishing
