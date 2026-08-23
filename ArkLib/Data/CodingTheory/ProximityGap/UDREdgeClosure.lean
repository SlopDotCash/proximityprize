/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CeilingMarch

/-!
# The UDR-edge band closure: below-UDR radius coverage is gapless (#371)

The universal below-UDR dichotomy (`UniversalBelowUDR.lean`) covers `2w + 2k ≤ n`; the
DISPROOF_LOG fifth no-go shows the band `n ∈ [2w+k+1, 2w+2k)` (width `k/n` in radius) is
**intrinsic to that dichotomy**: for directions at distance `e ∈ (w, w+k]` from the code,
the multiplicity factor `e − w − k` is nonpositive and the popular-codeword count needs
`m = n − w − e ≥ k` off-support agreement points, which fails exactly there.

This file records that the gap is a gap of the *method*, not of the radius coverage: the
subset-ownership law (`march_badScalars_card_mul_le` / `fit_subsets_card_le_one`, the
glueing constant of the dimension ladder) is **radius-free** — its only hypothesis is
agreement above `d + 2` — so it covers the band (and everything else below the ceiling)
at the polynomial budget `C(n, d+2)/((d+2)·p)`.

* `le_mcaDeltaStar_subset_law` — the threshold form of `march_epsMCA_le`: any radius with
  agreement above `d + 2` is a good point at the subset budget.
* `le_mcaDeltaStar_subset_law_w` — the integer-radius form `δ = w/n`, every
  `1 ≤ w ≤ n − d − 3`.
* `udrEdgeBand_closure` — the named instance on the fifth no-go's band
  `2w + k + 1 ≤ n < 2w + 2k` (`k = d + 1`): the formerly uncovered sliver moves at the
  subset budget.  Together with `le_mcaDeltaStar_universal` (whose budget is sharper when
  `2w + 2k ≤ n`), below-UDR radius coverage is gapless at every rate.

Honest scope: on the band the budget is `C(n, k+1)/((k+1)·p)` — the `n^{k+1}`-shape mass,
meaningful at fixed `k` (production form `q ≥ n^{k+1}·2^{128}`), the same fixed-`k` sense
as the rest of the below-UDR chapter.  The dichotomy's sharper `(n−2w−2k+1)^{−k}` budget
remains unavailable on the band; improving it there needs the γ-line recursion flagged in
the no-go.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction
open ArkLib.ProximityGap.KKH26CeilingMarch

namespace ArkLib.ProximityGap.UDREdgeClosure

variable {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]

/-- **The threshold form of the subset-ownership law** (radius-free): every radius with
agreement above `d + 2` is a good point of the degree-`d` evaluation code at the subset
budget `C(n, d+2)/((d+2)·p)`. -/
theorem le_mcaDeltaStar_subset_law (hg : orderOf g = n) {d : ℕ} {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδ : ((d + 2 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    {εstar : ℝ≥0∞}
    (hbudget : ((n.choose (d + 2) / (d + 2) : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar :=
  le_mcaDeltaStar_of_good _ _ hδ1 (le_trans (march_epsMCA_le hg hδ) hbudget)

/-- **The integer-radius form**: `δ* ≥ w/n` for every `1 ≤ w` with `w + d + 3 ≤ n`, at the
subset budget — all of below-UDR, the edge band, and the window up to the ceiling. -/
theorem le_mcaDeltaStar_subset_law_w (hg : orderOf g = n) {d w : ℕ}
    (hw1 : 1 ≤ w) (hwn : w + d + 3 ≤ n)
    {εstar : ℝ≥0∞}
    (hbudget : ((n.choose (d + 2) / (d + 2) : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar) :
    ((w : ℝ≥0) / (n : ℝ≥0)) ≤
      mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar := by
  have hn0 : (n : ℝ≥0) ≠ 0 := by
    have := NeZero.ne n
    exact_mod_cast this
  have hwle : (w : ℝ≥0) ≤ (n : ℝ≥0) := by
    have : w ≤ n := by omega
    exact_mod_cast this
  refine le_mcaDeltaStar_subset_law hg ?_ ?_ hbudget
  · exact div_le_one_of_le₀ hwle (zero_le _)
  · have hmul : ((1 : ℝ≥0) - (w : ℝ≥0) / (n : ℝ≥0)) * (Fintype.card (Fin n) : ℝ≥0)
        = (n : ℝ≥0) - (w : ℝ≥0) := by
      rw [Fintype.card_fin, tsub_mul, one_mul, div_mul_cancel₀ _ hn0]
    rw [hmul]
    rw [lt_tsub_iff_right]
    have : d + 2 + w < n := by omega
    exact_mod_cast this

/-- **THE UDR-EDGE BAND CLOSURE.**  On the fifth no-go's band `2w + k + 1 ≤ n < 2w + 2k`
(`k = d + 1` the code dimension) — where the universal dichotomy is provably silent —
the threshold still moves: `δ* ≥ w/n` at the subset budget.  Below-UDR radius coverage
is gapless at every rate. -/
theorem udrEdgeBand_closure (hg : orderOf g = n) {d w : ℕ} (hw1 : 1 ≤ w)
    (hband_lo : 2 * w + (d + 1) + 1 ≤ n) (_hband_hi : n < 2 * w + 2 * (d + 1))
    {εstar : ℝ≥0∞}
    (hbudget : ((n.choose (d + 2) / (d + 2) : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar) :
    ((w : ℝ≥0) / (n : ℝ≥0)) ≤
      mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar := by
  refine le_mcaDeltaStar_subset_law_w hg hw1 ?_ hbudget
  omega

end ArkLib.ProximityGap.UDREdgeClosure

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.UDREdgeClosure.le_mcaDeltaStar_subset_law
#print axioms ArkLib.ProximityGap.UDREdgeClosure.le_mcaDeltaStar_subset_law_w
#print axioms ArkLib.ProximityGap.UDREdgeClosure.udrEdgeBand_closure
