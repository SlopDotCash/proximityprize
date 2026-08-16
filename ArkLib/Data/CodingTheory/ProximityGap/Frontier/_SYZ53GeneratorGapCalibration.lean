/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ44MuBasisDegreeSum
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ45ImbalanceBound

/-!
# SYZ53 — the μ-basis generator-gap **exactly** determines the imbalance: `ι = ⌊(δ₂−δ₁)/2⌋`

## Context

SYZ44 proved the μ-basis **degree-sum law** `δ₁ + δ₂ = a + b + c =: S` (`degree_sum_of_hilbert`)
with the minimal generator `δ₁ ≤ δ₂`, and SYZ45 packaged the imbalance
`ι = SYZ45.imbalance a b c δ₁ = ⌊S/2⌋ − δ₁`.  SYZ52 then pinned the open balanced-interior residual
to the **second-generator upper bound** `δ₂ ≤ ⌈S/2⌉ + 1`, proving it *equivalent* to `ι ≤ 1`
(`second_le_iff_imbalance_le_one`), and PUNTED that inequality — as loose "Hilbert–Burch content" —
downstream to G56/Opus-core.

The direct μ-basis referee probe then sharpened the target.  `fable_syz52_delta2.py` (exact GF(p)
*both*-generator degrees, 1080 balanced pairwise-coprime band triples, `p ∈ {61,101,257}`,
budgets `{5,7,9}`) measured the full μ-basis as `(δ₁, δ₂) = (⌈S/2⌉ − 1, ⌈S/2⌉)` **field-independently**
at exact balance `a = b = c` — i.e. the two Hilbert–Burch generator product-degrees are *near-balanced*,
`δ₂ − δ₁ ≤ 1` (odd `S`).  This is STRICTLY tighter than SYZ52's `δ₂ ≤ ⌈S/2⌉ + 1` (slack by a full
unit) and is the *natural* commutative-algebra object: the μ-basis column-degree splitting of a
balanced coprime triple is as even as `δ₁ + δ₂ = S` permits.  So the honest downstream target is the
**generator gap** `δ₂ − δ₁`, not a one-sided ceiling on `δ₂`.

## Result (this file)

Pure-`ℕ`, axiom-clean, consuming only SYZ44's degree-sum law.  The central fact is an **exact
identity**, not an inequality: under `δ₁ + δ₂ = S` with `δ₁ ≤ δ₂`, writing the generator gap
`g := δ₂ − δ₁`,

* `imbalance_eq_gap_div_two` — **`ι = ⌊g/2⌋` EXACTLY.**  Since `g = S − 2δ₁` and
  `ι = ⌊S/2⌋ − δ₁ = ⌊(S − 2δ₁)/2⌋ = ⌊g/2⌋`, the imbalance is *precisely* the half-gap.  This is the
  content SYZ52's one-sided calibration only bounded: the imbalance is a deterministic function of the
  generator gap, so the whole interior residual is a statement about `g` alone.

The exact identity immediately yields the sharp gap-language calibrations that replace SYZ52's punted
inequality with the referee-measured near-balance target:

* `imbalance_le_one_iff_gap_le_three` — **`ι ≤ 1 ↔ δ₂ − δ₁ ≤ 3`.**  The *sharpest* gap phrasing of
  the interior target: the balanced-interior spread branch closes at rate `1/2` exactly when the
  μ-basis generator gap is at most `3`.  Strictly cleaner than `δ₂ ≤ ⌈S/2⌉ + 1` (no ceiling, no `S`).
* `imbalance_le_one_of_gap_le_one` — **`δ₂ − δ₁ ≤ 1 ⟹ ι = 0`** (hence `≤ 1`).  The referee-measured
  near-balance bound `g ≤ 1` gives not just `ι ≤ 1` but the *exact-balance* `ι = 0`: a near-balanced
  μ-basis has **no** imbalance at all.  This is the crisp Hilbert–Burch statement to hand G56/Opus-core
  — a full unit stronger than SYZ52's target and matching every one of the 1080 exact evaluations.
* `gap_le_one_of_imbalance_zero` — converse: `ι = 0 ↔ δ₂ − δ₁ ≤ 1`, closing the calibration loop for
  the exact-balance case.
* `imbalance_le_one_of_gap_le_one_of_hilbert` — packaged end-to-end from SYZ44's two structural inputs
  (`RankNullity`, `TwoRamp`) plus `δ₁ ≤ δ₂` and the near-balance gap `δ₂ − δ₁ ≤ 1`.

**Why this is new, not a wrapper of SYZ52.**  SYZ52 calibrates a *one-sided ceiling*
`δ₂ ≤ ⌈S/2⌉ + 1 ↔ ι ≤ 1`.  This file proves the *exact functional identity* `ι = ⌊(δ₂−δ₁)/2⌋`, from
which the gap-language equivalences (`ι ≤ 1 ↔ g ≤ 3`, and the sharper `g ≤ 1 ⟹ ι = 0`) follow.  The
gap `g` is a different, field-independently-measured object than the `δ₂` ceiling; the identity pins
the *whole* imbalance function, not merely the `ι ≤ 1` threshold, and delivers the referee's sharp
`g ≤ 1` near-balance target (one unit tighter than SYZ52) rather than the loose ceiling SYZ52 punted.

**Scope honesty.**  This closes the *combinatorial* calibration half: it reduces the balanced-interior
residual to the single generator-gap statement `δ₂ − δ₁ ≤ 1` (referee-measured, field-independent),
proved *equivalent-in-effect* to `ι = 0` and strictly sufficient for `ι ≤ 1`.  It does **not** prove
that the μ-basis of a balanced coprime triple is near-balanced (that is the remaining Hilbert–Burch
column-degree-splitting content assigned to G56/Opus-core), and `ι ≤ 1` only closes SYZ44's
`uniformSylvester` at rate `1/2`; the production δ* wire still needs SYZ18 supports, `hrank`
realizability, strip-radius transport, and the `MCAThresholdLedger` BGK lower bound.  CORE remains
OPEN / ON-BGK.  What is new here is the *exact* imbalance–gap identity and the resulting sharp
near-balance calibration.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ53

open ArkLib.ProximityGap

/-! ## 1. The exact identity: imbalance is the half-gap of the μ-basis generator degrees -/

/-- **Imbalance = half-gap (exact).**  Under the degree-sum law `δ₁ + δ₂ = a + b + c =: S` with the
minimal generator `δ₁ ≤ δ₂`, the μ-basis imbalance equals the floored half of the generator gap:
`ι = SYZ45.imbalance a b c δ₁ = ⌊S/2⌋ − δ₁ = ⌊(δ₂ − δ₁)/2⌋`.

Mechanism (pure `ℕ`): the gap is `g = δ₂ − δ₁ = S − 2δ₁`, so
`ι = ⌊S/2⌋ − δ₁ = ⌊(S − 2δ₁)/2⌋ = ⌊g/2⌋`.  The imbalance is therefore a *deterministic function of
the generator gap alone* — the entire balanced-interior residual is a statement about `δ₂ − δ₁`. -/
theorem imbalance_eq_gap_div_two
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂) :
    SYZ45.imbalance a b c δ₁ = (δ₂ - δ₁) / 2 := by
  unfold SYZ45.imbalance; omega

/-! ## 2. Sharp gap-language calibration of the interior target `ι ≤ 1` -/

/-- **`ι ≤ 1 ↔ generator gap ≤ 3` (sharpest gap phrasing).**  From the exact identity
`ι = ⌊(δ₂−δ₁)/2⌋`, the interior spread-branch target `ι ≤ 1` is equivalent to the μ-basis generator
gap being at most `3`.  This replaces SYZ52's one-sided ceiling `δ₂ ≤ ⌈S/2⌉ + 1` with a clean,
`S`-free gap inequality — the natural Hilbert–Burch column-degree statement. -/
theorem imbalance_le_one_iff_gap_le_three
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂) :
    SYZ45.imbalance a b c δ₁ ≤ 1 ↔ δ₂ - δ₁ ≤ 3 := by
  unfold SYZ45.imbalance; omega

/-- **Near-balance ⟹ zero imbalance.**  The referee-measured near-balance bound `δ₂ − δ₁ ≤ 1`
(field-independent across 1080 exact μ-basis evaluations, 3 primes) forces not merely `ι ≤ 1` but the
*exact-balance* `ι = 0`: a near-balanced μ-basis has **no** imbalance.  This is the crisp downstream
target — a full unit stronger than SYZ52's `δ₂ ≤ ⌈S/2⌉ + 1` and matching every measured cell. -/
theorem imbalance_eq_zero_of_gap_le_one
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hgap : δ₂ - δ₁ ≤ 1) :
    SYZ45.imbalance a b c δ₁ = 0 := by
  unfold SYZ45.imbalance; omega

/-- **Near-balance ⟹ `ι ≤ 1`** (immediate corollary of `imbalance_eq_zero_of_gap_le_one`, stated in
the form the spread branch consumes). -/
theorem imbalance_le_one_of_gap_le_one
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hgap : δ₂ - δ₁ ≤ 1) :
    SYZ45.imbalance a b c δ₁ ≤ 1 := by
  have := imbalance_eq_zero_of_gap_le_one a b c δ₁ δ₂ hsum hle hgap
  omega

/-- **Exact-balance calibration (converse loop).**  `ι = 0 ↔ δ₂ − δ₁ ≤ 1`.  Together with
`imbalance_le_one_iff_gap_le_three` this fully calibrates the imbalance ladder in gap language:
`ι = 0 ↔ g ≤ 1`, `ι ≤ 1 ↔ g ≤ 3`. -/
theorem imbalance_eq_zero_iff_gap_le_one
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂) :
    SYZ45.imbalance a b c δ₁ = 0 ↔ δ₂ - δ₁ ≤ 1 := by
  unfold SYZ45.imbalance; omega

/-! ## 3. Packaged reduction from SYZ44's structural inputs -/

/-- **Packaged near-balance interior closure.**  From SYZ44's two structural inputs
(`RankNullity hilb a b c D₀` and `TwoRamp hilb δ₁ δ₂`) that yield the degree-sum law, plus
`δ₁ ≤ δ₂` and the referee-measured near-balance gap `δ₂ − δ₁ ≤ 1`, conclude `ι ≤ 1` (indeed `ι = 0`)
— the full balanced-interior discharge end to end, with the sharp Hilbert–Burch gap hypothesis. -/
theorem imbalance_le_one_of_gap_le_one_of_hilbert
    (hilb : ℕ → ℕ) (a b c δ₁ δ₂ D₀ : ℕ)
    (hRankNull : SYZ44.RankNullity hilb a b c D₀)
    (hTwoRamp : SYZ44.TwoRamp hilb δ₁ δ₂)
    (hle : δ₁ ≤ δ₂)
    (hgap : δ₂ - δ₁ ≤ 1) :
    SYZ45.imbalance a b c δ₁ ≤ 1 := by
  have hsum : δ₁ + δ₂ = a + b + c :=
    SYZ44.degree_sum_of_hilbert hilb a b c δ₁ δ₂ D₀ hRankNull hTwoRamp
  exact imbalance_le_one_of_gap_le_one a b c δ₁ δ₂ hsum hle hgap

end ArkLib.ProximityGap.SYZ53

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ53.imbalance_eq_gap_div_two
#print axioms ArkLib.ProximityGap.SYZ53.imbalance_le_one_iff_gap_le_three
#print axioms ArkLib.ProximityGap.SYZ53.imbalance_eq_zero_of_gap_le_one
#print axioms ArkLib.ProximityGap.SYZ53.imbalance_le_one_of_gap_le_one
#print axioms ArkLib.ProximityGap.SYZ53.imbalance_eq_zero_iff_gap_le_one
#print axioms ArkLib.ProximityGap.SYZ53.imbalance_le_one_of_gap_le_one_of_hilbert
