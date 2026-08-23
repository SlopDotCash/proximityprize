/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.HalfJohnsonDeltaStar
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandDeltaStarCeiling

/-!
# The unconditional δ* bracket (#389) — capstone

This file combines the two landed, axiom-clean one-sided bounds on the mutual-correlated-
agreement threshold `δ*` of the explicit Reed–Solomon code into a SINGLE two-sided bracket
for ONE `mcaDeltaStar` term:

* FLOOR (half the Johnson radius), landed in `HalfJohnsonDeltaStar.lean`:
  `rsCode_deltaStar_ge_halfJohnson` — under its half-Johnson budget,
  `δ_floor ≤ δ*(rsCode dom k, ε*)`, with `δ_floor` any radius below `(1 − √ρ)/2`.

* CEILING (capacity minus the deep-band entropy defect), landed in
  `DeepBandDeltaStarCeiling.lean`: `mcaDeltaStar_le_of_deep_band` — under its deep-band
  closed-form budget, `δ*(rsCode dom k, ε*) ≤ δ_ceil`, with `δ_ceil` any deep-band radius
  `(1−δ)n ≤ k+m+1`.

The only obstruction to chaining them was a Set representation mismatch:

* the FLOOR is stated for `↑(codeFinset dom k) : Set (Fin n → F)` (the Finset coercion);
* the CEILING is stated for `((rsCode dom k : Submodule …) : Set (Fin n → F))` (the
  submodule carrier).

These are the SAME code.  The bridge `codeFinset_coe_eq_rsCode` proves the two Sets are
literally equal, so a single `mcaDeltaStar` term satisfies both hypotheses, giving:

> **`deltaStar_bracket`** — under BOTH budget hypotheses, for the SAME code,
> `δ_floor ≤ mcaDeltaStar (rsCode dom k) ε* ≤ δ_ceil`.

This is the clean citable unconditional δ* bracket
`(1 − √ρ)/2 ≤ δ* ≤ capacity − H(ρ)/(β log n)` (here in its exact finite, machine-checked
closed form, with no entropy approximation and no list-decoding/all-pairs input).

## References
* Issue #389; `HalfJohnsonDeltaStar.lean` (FLOOR), `DeepBandDeltaStarCeiling.lean` (CEILING),
  `MCAThresholdLedger.lean` (the `mcaDeltaStar` bracketing engine),
  `CappedSupplyMassIdentity.lean` (`codeFinset`), `GranularityLadderRS.lean` (`rsCode`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset Polynomial
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.DeltaStarBracket

open ProximityGap ProximityGap.PairRank ProximityGap.MCAThresholdLedger Code
open ProximityGap.SpikeFloor
open ArkLib.ProximityGap.HalfJohnson

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## Part 1 — the Set-representation bridge: `codeFinset` ≡ `rsCode` -/

/-- **The Set-coercion bridge.**  The coercion of the RS-code Finset `codeFinset dom k` to a
`Set` is literally the carrier set of the RS-code submodule `rsCode dom k`.  By definition
`codeFinset dom k = univ.filter (· ∈ rsCode dom k)`, so a word lies in the Finset coercion
iff it lies in the submodule.  This identifies the FLOOR's domain
`↑(codeFinset dom k)` with the CEILING's domain `↑(rsCode dom k : Submodule …)`, making one
`mcaDeltaStar` term satisfy both one-sided bounds. -/
theorem codeFinset_coe_eq_rsCode (dom : Fin n ↪ F) (k : ℕ) :
    (↑(codeFinset dom k) : Set (Fin n → F))
      = ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) := by
  classical
  ext w
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
    codeFinset, SetLike.mem_coe]

/-! ## Part 2 — the two-sided δ* bracket for the SAME code -/

/-- **The unconditional δ\* bracket.**  For the explicit Reed–Solomon code `rsCode dom k`
over ANY evaluation domain `dom : Fin n ↪ F`, with degree `1 ≤ k`:

* if the FLOOR radius `δ_floor ≤ 1` lies in the half-Johnson window
  (`2·δ_floor + √((k−1)/n) < 1`) and its proven half-Johnson `ε_mca` bound clears the
  budget `ε*`, and
* if the CEILING radius `δ_ceil` lies in a deep band (`(1−δ_ceil)·n ≤ k+m+1`) whose
  closed-form failure count clears the same budget `ε*`,

then the single threshold term is bracketed:

  `δ_floor ≤ mcaDeltaStar (rsCode dom k) ε* ≤ δ_ceil`.

In rate units (`ρ = k/n`, `e/n = ρ − 1/n`) this is the unconditional, machine-checked
two-sided pin `(1 − √ρ)/2 ≤ δ* ≤ capacity − H(ρ)/(β log n)`, with no list-decoding,
extraction, or all-pairs (`SmallSubgroupGoodList`) input.  Both faces are proven
unconditionally; the only chaining ingredient is the Set bridge
`codeFinset_coe_eq_rsCode`, which makes both faces speak about ONE code. -/
theorem deltaStar_bracket (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    -- FLOOR side: a half-Johnson radius below `(1 − √ρ)/2` that clears the budget
    {δfloor : ℝ≥0} (hδfloor1 : δfloor ≤ 1)
    (hδfloor : 2 * δfloor + NNReal.sqrt (((k - 1 : ℕ) : ℝ≥0) / Fintype.card (Fin n)) < 1)
    -- CEILING side: a deep-band radius `(1−δ)n ≤ k+m+1`
    {δceil : ℝ≥0}
    (hδceilhi : (1 - δceil) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    -- the common budget
    (εstar : ℝ≥0∞)
    (hfloorBudget : ((1 + (Fintype.card (Fin n) -
          (2 * ⌈(1 - δfloor) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n))) *
          (Fintype.card (Fin n) ^ 2 /
            ((2 * ⌈(1 - δfloor) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n)) ^ 2 -
              Fintype.card (Fin n) * (k - 1))) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hceilBudget : εstar * ((Fintype.card F : ℝ≥0∞)
        * (↑(((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
              / (Fintype.card F) ^ (m + 1)
            + (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2) : ℝ≥0∞) ^ 2)
      < (↑(((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
          * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
              / (Fintype.card F) ^ (m + 1)
            + (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2)
          / (Fintype.card F) ^ m) : ℝ≥0∞)) :
    δfloor ≤ mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar
      ∧ mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar ≤ δceil := by
  classical
  refine ⟨?_, ?_⟩
  · -- FLOOR: rewrite the Finset domain to the submodule domain, then apply the landed floor.
    have hfloor := rsCode_deltaStar_ge_halfJohnson dom hk hδfloor1 hδfloor εstar hfloorBudget
    rwa [codeFinset_coe_eq_rsCode dom k] at hfloor
  · -- CEILING: directly the landed deep-band ceiling (already in submodule vocabulary).
    exact mcaDeltaStar_le_of_deep_band dom hk hδceilhi εstar hceilBudget

/-- **The bracket, stated on the Finset-coercion domain.**  The same two-sided pin, but with
the threshold term written over `↑(codeFinset dom k)` (the FLOOR's native vocabulary).  Pure
rewrite of `deltaStar_bracket` through the Set bridge — provided for callers that consume the
half-Johnson `ε_mca` surface in Finset form. -/
theorem deltaStar_bracket_codeFinset (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    {δfloor : ℝ≥0} (hδfloor1 : δfloor ≤ 1)
    (hδfloor : 2 * δfloor + NNReal.sqrt (((k - 1 : ℕ) : ℝ≥0) / Fintype.card (Fin n)) < 1)
    {δceil : ℝ≥0}
    (hδceilhi : (1 - δceil) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (εstar : ℝ≥0∞)
    (hfloorBudget : ((1 + (Fintype.card (Fin n) -
          (2 * ⌈(1 - δfloor) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n))) *
          (Fintype.card (Fin n) ^ 2 /
            ((2 * ⌈(1 - δfloor) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n)) ^ 2 -
              Fintype.card (Fin n) * (k - 1))) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hceilBudget : εstar * ((Fintype.card F : ℝ≥0∞)
        * (↑(((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
              / (Fintype.card F) ^ (m + 1)
            + (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2) : ℝ≥0∞) ^ 2)
      < (↑(((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
          * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
              / (Fintype.card F) ^ (m + 1)
            + (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2)
          / (Fintype.card F) ^ m) : ℝ≥0∞)) :
    δfloor ≤ mcaDeltaStar (F := F) (A := F)
        (↑(codeFinset dom k) : Set (Fin n → F)) εstar
      ∧ mcaDeltaStar (F := F) (A := F)
        (↑(codeFinset dom k) : Set (Fin n → F)) εstar ≤ δceil := by
  classical
  have h := deltaStar_bracket dom hk hδfloor1 hδfloor hδceilhi εstar hfloorBudget hceilBudget
  rwa [codeFinset_coe_eq_rsCode dom k]

end ArkLib.ProximityGap.DeltaStarBracket

/-! ## Source audit -/
#print axioms ArkLib.ProximityGap.DeltaStarBracket.codeFinset_coe_eq_rsCode
#print axioms ArkLib.ProximityGap.DeltaStarBracket.deltaStar_bracket
#print axioms ArkLib.ProximityGap.DeltaStarBracket.deltaStar_bracket_codeFinset
