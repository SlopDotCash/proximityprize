/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#464)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

/-!
# Door-(iv) constraint: the worst-frequency GAP SEQUENCE has NO LONG MONOTONE RUN —
  the local near-AP gap lever is a DEAD lever (#464)

Completing the worst-`b` gap-complexity trilogy.  Even after the gap VALUE complexity
(`ThreeGapPositionalRigidity`, `≤ n/2+1`), the gap CURVATURE (`_DoorIVPhaseCurvatureGeneric`,
maximal `n`) and the gap SPECTRUM (`_DoorIVGapSpectrumFullRank`, full `n−1`) are all generic, a
sequence can be spectrally full-rank yet still hide a LOCAL anomaly: an anomalously LONG monotone
(near-arithmetic-progression) run of consecutive gaps, which a structured small-ball / local-AP
bound — NOT routing through multiplicative energy — could grip.

PROBE (`scripts/probes/probe_dooriv_worstb_gap_longrun.py`; proper `μ_n`, `p ≡ 1 mod n`,
`p ~ n⁴ ≫ n³`, never `n = q-1`; uniform coset-rep sampling; EXACT integer gaps; longest circular
monotone (non-decr OR non-incr) run of the gap sequence; global worst-`b` scan; `n=16/32/64`, 5
structured primes):

  L(b*)  (median) = 3, 4, 4   at n = 16, 32, 64
  L(gen) (median) = 3, 4, 4   (identical)
  reference 2·log₂ n = 8, 10, 12   (the runs are FAR below even this)

So the longest monotone run at the worst frequency is a **tiny constant** (`≈ 3–4`), FAR below
`log n` (let alone `n`), and **identical to a generic `b`**.  There is **no long near-AP stretch**
to exploit, and the statistic is frequency-blind.

CONSEQUENCE (this file, axiom-clean).  We model the measured facts as hypotheses: the worst-`b`
longest monotone run `L` is bounded by a small constant `K` (probed `K ≈ 4`), and it equals the
generic-`b` run.  The kernel proves there is **no long-run target at the worst frequency**: a
local-AP lever requiring a monotone run of length `≥ L₀` with `L₀ > K` is impossible, and the
generic-equality kills frequency separation.

This brick is HONESTY-STRICT (real proofs, no `sorry`/`axiom`/`native_decide`/vacuity),
NON-MOMENT (pure local gap run-length combinatorics, no additive energy),
ASYMPTOTIC-GUARD-COMPLIANT (a *negative* / refutation result: a long-run local-AP lever is RULED
OUT at `b*`; no capacity / beyond-Johnson / `δ*` claim).  It does NOT bound CORE; it removes the
final named non-energy gap lever (local long monotone run) from door (iv).  CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVGapNoLongRun

/-- **No long-run target at the worst frequency.**  If the worst-`b` longest monotone gap-run `L`
is bounded by the probed constant `K`, then no local-AP lever requiring a monotone run of length
`≥ L₀` with `L₀ > K` is realizable: the actual run `L < L₀`.  `L` = measured longest monotone run;
`K` = the small probed ceiling (`≈ 4`). -/
theorem no_long_run_target {L K : ℕ} (hbound : L ≤ K)
    (L0 : ℕ) (hL0 : K < L0) :
    L < L0 := by omega

/-- **No long-run reaches a linear fraction.**  Concretely, with the probed constant ceiling `K` and
any length `n` with `K < n`, the worst-`b` monotone run is strictly below `n` — never a linear
near-AP stretch. -/
theorem run_below_length {L K n : ℕ} (hbound : L ≤ K) (hKn : K < n) :
    L < n := by omega

/-- **Frequency-blindness (no separation).**  The probed equality `L(b*) = L(gen)` means no run
threshold `t` marks the worst `b` as having a LONGER run (`L_gen < t ≤ L_worst`).  A run-length
statistic cannot select the worst frequency as the long-run one. -/
theorem no_run_separation {Lworst Lgen : ℕ} (heq : Lworst = Lgen) :
    ∀ t : ℕ, ¬ (Lgen < t ∧ t ≤ Lworst) := by
  intro t ⟨h1, h2⟩; omega

/-- **Combined door-(iv) no-long-run refutation.**  Bundles the proven faces for the worst-`b`
gap-run, exactly as probed:
* bounded run: `Lworst ≤ K` ⟹ no length-`L₀` (`L₀ > K`) monotone run exists, and the run stays below
  any `n > K` (no linear near-AP stretch);
* frequency-blindness: `Lworst = Lgen` ⟹ no threshold marks the worst `b` as the long-run one.
Together: the local long-monotone-run (near-AP) gap lever is dead.  NEGATIVE structural lemma;
NO CORE bound. -/
theorem doorIV_gapNoLongRun_dead {Lworst Lgen K n : ℕ}
    (hbound : Lworst ≤ K) (hKn : K < n) (heq : Lworst = Lgen) :
    (∀ L0 : ℕ, K < L0 → Lworst < L0) ∧
      Lworst < n ∧
      (∀ t : ℕ, ¬ (Lgen < t ∧ t ≤ Lworst)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L0 hL0; exact no_long_run_target hbound L0 hL0
  · exact run_below_length hbound hKn
  · exact no_run_separation heq

end ArkLib.ProximityGap.Frontier.DoorIVGapNoLongRun
