/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The char-`p` transfer decomposition `G_p = G_0 + L + Q` (#444)

The last open piece of the prize: the **char-`p` transfer** of the step-ratio monotonicity gap
`G(r) = (2r+3)·E_{r+1}² − (2r+1)·E_r·E_{r+2} ≥ 0` (proven char-0 in `_CharZeroStepRatioMonotone` for
`r=2..5`). Writing the char-`p` energies as `E_r(F_p) = E_r^0 + W_r` (char-0 value plus the wraparound
excess `W_r ≥ 0`), the gap splits **exactly** (a ring identity) into three pieces:

  `G_p = G_0 + L + Q`,   where
  * `G_0 = (2r+3)·(E_{r+1}^0)² − (2r+1)·E_r^0·E_{r+2}^0`   — the char-0 gap, **PROVEN ≥ 0**;
  * `L = 2(2r+3)·E_{r+1}^0·W_{r+1} − (2r+1)·(E_r^0·W_{r+2} + E_{r+2}^0·W_r)`  — linear in `W`;
  * `Q = (2r+3)·W_{r+1}² − (2r+1)·W_r·W_{r+2}`            — the wraparound's OWN log-convexity gap.

**Machine data (`charp_transfer.py`, prize primes):** `G_0 > 0` (the dominant term), `L < 0` (the
wraparound hurts the gap linearly), `Q > 0` (the wraparound is itself sub-Gaussian-monotone), and
crucially **`G_0` dominates `|L+Q|` at every depth** (so `G_p > 0`), with the margin GROWING at deep `r`
and `W_r/slack_r ≤ 0.02`.

**This file** lands (1) the exact decomposition (`gap_decompose`), and (2) the sufficient condition
`gap_p_nonneg_of_dominance`: the char-`p` transfer `G_p ≥ 0` follows from **`G_0 + L ≥ 0`** (the proven
char-0 gap dominates the linear wraparound perturbation) **and `Q ≥ 0`** (the wraparound's own
monotonicity). Both are data-favorable and strictly sharper than "bound `E_r(F_p)` directly". So the open
wall is reduced to these two localized wraparound-control inequalities, with the char-0 backbone already
proven.

⚠ CORRECTION (2026-06-20): the "data-favorable" / "`G₀` dominates `|L+Q|` at every depth" claims above
rested on a probe with an INCORRECT char-0 energy `E_r(ℂ)` (naive integer-lift, wrong at `r ≥ 4`). With the
CORRECT cyclotomic/antipodal `E_r(ℂ)`, the dominance `0 ≤ G₀ + L` is FALSE and the assembled char-`p` gap
`G_p = G₀ + L + Q` is NEGATIVE at prize-regime points (e.g. `n=32, p=786433, r=3`: `G_p = −1235923403258880`;
`n=64, p=2752513, r=2`: `G_p = −2341415014400`). See `_CharPStepRatioMonotoneFails.lean` for the
kernel-checked refuting witnesses. So `gap_p_nonneg_of_dominance`/`charP_transfer_of_dominance` below are
VALID conditional lemmas but their hypotheses are UNSATISFIABLE in the prize regime: this route does NOT
close CORE. The `gap_decompose` ring identity is correct and unaffected.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.CharPTransferDecomposition

/-- The monotonicity gap functional `gap s a b c = (s+2)·b² − s·a·c`, with `s = 2r+1` (so `s+2 = 2r+3`),
`a = E_r`, `b = E_{r+1}`, `c = E_{r+2}`. The char-0 step-ratio monotonicity is `0 ≤ gap s E_r E_{r+1} E_{r+2}`. -/
def gap (s a b c : ℝ) : ℝ := (s + 2) * b ^ 2 - s * a * c

/-- **The exact char-`p` decomposition `G_p = G_0 + L + Q` (ring identity).** Substituting the char-`p`
energies `a₀+wa, b₀+wb, c₀+wc` (char-0 values plus wraparound `wa=W_r, wb=W_{r+1}, wc=W_{r+2} ≥ 0`) into
the gap splits it exactly into the char-0 gap `G_0 = gap s a₀ b₀ c₀`, the linear-in-`W` term `L`, and the
wraparound's own gap `Q = gap s wa wb wc`. -/
theorem gap_decompose (s a₀ b₀ c₀ wa wb wc : ℝ) :
    gap s (a₀ + wa) (b₀ + wb) (c₀ + wc)
      = gap s a₀ b₀ c₀
        + (2 * (s + 2) * b₀ * wb - s * (a₀ * wc + c₀ * wa))
        + gap s wa wb wc := by
  simp only [gap]; ring

/-- **The char-`p` transfer reduces to two localized inequalities.** Given the proven char-0 gap
`G_0 ≥ 0` packaged as `G_0 + L ≥ 0` (the char-0 backbone dominates the linear wraparound perturbation `L`,
machine-confirmed: `L < 0` but `|L| ≤ G_0` with growing margin) AND the wraparound's own monotonicity
`Q ≥ 0` (machine-confirmed `Q > 0`), the char-`p` gap is nonnegative: `G_0 + L + Q ≥ 0`. Hence the
char-`p` step-ratio monotonicity `G_p ≥ 0` holds. -/
theorem gap_p_nonneg_of_dominance {G₀ L Q : ℝ} (hdom : 0 ≤ G₀ + L) (hQ : 0 ≤ Q) :
    0 ≤ G₀ + L + Q := by linarith

/-- **The assembled char-`p` transfer (conditional on the two wraparound-control inputs).** With
`E_r(F_p) = E_r^0 + W_r`, the char-`p` gap `gap s E_r(F_p) E_{r+1}(F_p) E_{r+2}(F_p) ≥ 0` follows from
the proven char-0 gap dominating the linear term (`0 ≤ gap s a₀ b₀ c₀ + L`) and the wraparound gap being
nonneg (`0 ≤ gap s wa wb wc`). This is the precise reduction of the open wall: char-`p` Wick/monotonicity
⟸ (char-0 monotonicity, PROVEN) + (linear-perturbation dominance) + (wraparound log-convexity). -/
theorem charP_transfer_of_dominance {s a₀ b₀ c₀ wa wb wc : ℝ}
    (hdom : 0 ≤ gap s a₀ b₀ c₀ + (2 * (s + 2) * b₀ * wb - s * (a₀ * wc + c₀ * wa)))
    (hQ : 0 ≤ gap s wa wb wc) :
    0 ≤ gap s (a₀ + wa) (b₀ + wb) (c₀ + wc) := by
  rw [gap_decompose]
  linarith

end ArkLib.ProximityGap.CharPTransferDecomposition

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CharPTransferDecomposition.gap_decompose
#print axioms ArkLib.ProximityGap.CharPTransferDecomposition.gap_p_nonneg_of_dominance
#print axioms ArkLib.ProximityGap.CharPTransferDecomposition.charP_transfer_of_dominance
