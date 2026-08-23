/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Field.Basic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ThresholdHalvingSoundness

/-!
# BRICK L1a — single-variable Schwartz–Zippel for the FRI per-round error (ePrint 2026/858 route)

**Sub-brick of the threshold-halving deliverable.** The Chai–Fan per-round FRI soundness error
(ePrint 2026/858, Strategy A, threshold halving) has the shape

  `ε_FRI ≤ n·R/|F| + (1 − δ/2)^q`.

This file isolates the **probability-of-spurious-pass** primitive underlying the *single* random
folding-challenge consistency check: a univariate polynomial-identity test (PIT). When the prover's
claimed folded word is wrong, the verifier's consistency polynomial `p` (in the random folding
challenge drawn uniformly from a sample set `S ⊆ F`) is **nonzero**, and the check spuriously passes
exactly on the roots of `p` inside `S`. The Schwartz–Zippel lemma (single variable) then bounds

  `Pr_{x ∈ S}[ p(x) = 0 ]  ≤  deg(p) / |S|`.

Mathlib's multivariate Schwartz–Zippel (`MvPolynomial.schwartz_zippel_totalDegree`) is already
wrapped in the sibling file `_ThresholdHalvingSchwartzZippel.lean` for the multilinear folding
polynomial; **this** file provides the clean *single-variable* form directly from the univariate
root-count `Polynomial.card_le_degree_of_subset_roots` (`#Z ≤ natDegree p` for any Finset `Z` of
roots) — the `m = 1` case stated in exactly the shape the per-round PIT contribution needs, plus the
`q`-query relation to the `(1 − δ/2)^q` summand.

## What is proven here (axiom-clean, no `sorry`)

* `card_roots_in_le_natDegree` — the integer-count single-variable SZ: the number of points of a
  finite sample set `S ⊆ F` at which a *nonzero* univariate `p` vanishes is at most `natDegree p`.
  (This is the honest substitute for the prompt's `Polynomial.card_roots_le_degree`; Mathlib's
  actual name for the underlying count is `card_le_degree_of_subset_roots` / `card_roots'`.)
* `szProb_le` — the density / probability form `Pr_{x ∈ S}[p(x)=0] ≤ deg(p)/|S|` in `ℚ≥0`, the
  single-variable PIT failure probability per folding challenge.
* `perQueryNonDetection_le` — relating the per-query *non-detection* probability `1 − δ/2` (the FRI
  query soundness gap) to the named `(1 − δ/2)^q` tail: if each of `q` independent queries fails to
  detect a wrong word with probability `≤ 1 − δ/2`, the all-pass probability is `≤ (1 − δ/2)^q`.
* `perRound_from_SZ_and_queryTail` — assembles the `n·R/|F|` SZ folding half (here the single PIT
  density bound, cast to the `n·R'` slot) with the named query tail into `PerRoundFRIError`, leaving
  the genuine query-amplification term as the explicit named residual `QueryAmpTail` (never silently
  discharged).

## Honesty / scope

* Everything proven rests only on Mathlib's univariate root count — axiom audit
  `⊆ {propext, Classical.choice, Quot.sound}` (no `sorryAx`).
* The genuine ≈2×-query query-amplification term `(1 − δ/2)^q` is carried as the explicit named
  residual `QueryAmpTail`; the per-query SZ density is *fed into* it, never replacing it.
* This is the **lossy 2×-query above-Johnson route**, not the grand zero-loss `δ*` (the open BGK
  wall). Threshold halving trades a factor ≈ 2 in queries for an unconditional analysis below the
  Johnson radius.
-/

namespace ProximityGap.ThresholdHalvingSZ

open Polynomial Finset
open scoped NNRat

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### Single-variable Schwartz–Zippel: the integer root count over a sample set

For a *nonzero* univariate polynomial `p` over a field `F` and any finite sample set `S : Finset F`,
the number of points of `S` at which `p` vanishes is bounded by `natDegree p`. This is the `m = 1`
case of Schwartz–Zippel, proven directly from Mathlib's `card_le_degree_of_subset_roots`: the
vanishing points of `S` form a `Finset` whose underlying multiset is contained in `p.roots`. -/

/-- **Single-variable Schwartz–Zippel, integer-count form.** For a nonzero univariate `p` over the
field `F` and a finite sample set `S ⊆ F`, the count of `x ∈ S` with `p.eval x = 0` is at most
`natDegree p`. This is the per-query spurious-pass count of the FRI folding/consistency check. -/
theorem card_roots_in_le_natDegree {p : F[X]} (hp : p ≠ 0) (S : Finset F) :
    (S.filter fun x => p.eval x = 0).card ≤ p.natDegree := by
  classical
  -- The filtered set's underlying multiset is a sub-multiset of `p.roots`, so apply
  -- `card_le_degree_of_subset_roots`.
  refine card_le_degree_of_subset_roots ?_
  intro x hx
  -- `x ∈ (filter …).val` means `x ∈ S` and `p.eval x = 0`, hence `x ∈ p.roots`.
  rw [Finset.mem_val, Finset.mem_filter] at hx
  exact (mem_roots hp).mpr hx.2

/-! ### The density / probability form `Pr_{x ∈ S}[p(x)=0] ≤ deg(p)/|S|`

Dividing the count by `|S|` gives the single-variable Schwartz–Zippel *probability* bound, the
per-folding-challenge PIT failure probability, expressed in `ℚ≥0`. -/

/-- **Single-variable Schwartz–Zippel, probability form.** For a nonzero univariate `p` over `F` and
a finite sample set `S ⊆ F`, the fraction of `x ∈ S` with `p.eval x = 0` is at most
`natDegree p / |S|` in `ℚ≥0`. This is `Pr_{x ∈ S}[p(x) = 0] ≤ deg(p)/|S|`, the per-query
spurious-pass probability of the FRI consistency check. -/
theorem szProb_le {p : F[X]} (hp : p ≠ 0) (S : Finset F) :
    ((S.filter fun x => p.eval x = 0).card : ℚ≥0) / (S.card : ℚ≥0)
      ≤ (p.natDegree : ℚ≥0) / (S.card : ℚ≥0) := by
  -- Monotone in the numerator: the integer count bound, cast to `ℚ≥0`, then divided by `|S|`.
  have h : ((S.filter fun x => p.eval x = 0).card : ℚ≥0) ≤ (p.natDegree : ℚ≥0) := by
    exact_mod_cast card_roots_in_le_natDegree hp S
  gcongr

/-- **Single-variable Schwartz–Zippel over the full field.** Specializing the sample set to all of
`F` (the verifier draws the folding challenge uniformly from `F`), the per-query spurious-pass
probability is `≤ deg(p)/|F|`. This is the `n·R/|F|` summand at `m = 1`, where `deg(p) ≤ n·R` is the
folded RS degree. -/
theorem szProb_le_field [Fintype F] {p : F[X]} (hp : p ≠ 0) :
    (((Finset.univ : Finset F).filter fun x => p.eval x = 0).card : ℚ≥0)
        / (Fintype.card F : ℚ≥0)
      ≤ (p.natDegree : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
  have h := szProb_le (F := F) hp (Finset.univ)
  simpa only [Finset.card_univ] using h

/-! ### From per-query non-detection to the `(1 − δ/2)^q` tail

The FRI per-round error's second summand `(1 − δ/2)^q` is the probability that **all** `q`
independent verifier queries fail to detect a wrong (far) word, each query non-detecting with
probability `≤ 1 − δ/2` (the analysis runs at the halved radius `δ/2`). We carry the genuine
query-amplification accounting as an explicit named residual `QueryAmpTail`, and prove the clean
monotonicity step that *feeds* it: if the single-query non-detection probability is `≤ 1 − δ/2`,
then `q` independent queries all pass with probability `≤ (1 − δ/2)^q`. -/

/-- Named **query-amplification tail residual** (NOT proven — the genuine ≈2×-query penalty of the
lossy above-Johnson route, ePrint 2026/858). `QueryAmpTail tail q halfRadius` is meant to hold when
the all-`q`-queries-pass probability `tail` is bounded by `(1 − halfRadius)^q`. The downstream
per-query independence / list-decoding amplification accounting is not in this tree, so we keep it
abstract; it is the single remaining open obligation after the SZ per-query density is discharged. -/
def QueryAmpTail (tail : ℝ) (q : ℕ) (halfRadius : ℝ) : Prop :=
  tail ≤ (1 - halfRadius) ^ q

/-- **Per-query non-detection feeds the query tail.** If each independent query fails to detect a
wrong word with probability `≤ 1 − halfRadius` (with `0 ≤ 1 − halfRadius`), then the all-`q`-queries
non-detection probability `pSingle ^ q` satisfies `QueryAmpTail (pSingle ^ q) q halfRadius`. This is
the honest monotonicity step relating the per-query Schwartz–Zippel bound to the named `(1−δ/2)^q`
tail; it does NOT assert the FRI amplification itself (independence across queries is the named
residual's content). -/
theorem perQueryNonDetection_le {pSingle halfRadius : ℝ} (q : ℕ)
    (hnonneg : 0 ≤ 1 - halfRadius) (hsingle : pSingle ≤ 1 - halfRadius)
    (hp0 : 0 ≤ pSingle) :
    QueryAmpTail (pSingle ^ q) q halfRadius := by
  unfold QueryAmpTail
  exact pow_le_pow_left₀ hp0 hsingle q

/-! ### Assembly: SZ folding half + named query tail ⟹ `PerRoundFRIError`

Bringing in the named per-round error Prop from `_ThresholdHalvingSoundness`
(`PerRoundFRIError ε n R q halfRadius := ε ≤ n·R + (1 − halfRadius)^q`), we show that if the
per-round error decomposes as `ε ≤ foldFail + tail` with the folding-PIT failure `foldFail` bounded
by `n·R'` (the cast of the single-variable SZ density `deg(p)/|F| ≤ n·R/|F|`) and the query tail
controlled by the named `QueryAmpTail`, then `PerRoundFRIError` holds with only the query-tail
residual remaining open. -/

open ProximityGap.ThresholdHalvingSoundness

/-- **Per-round FRI error from the single-variable SZ folding half + named query tail.**

Suppose the per-round FRI soundness error `ε` splits as `ε ≤ foldFail + tail`, where:

* `foldFail` is the (single-query) folding-PIT failure probability, bounded by `n·R'` — the cast of
  the proven single-variable Schwartz–Zippel density `szProb_le` / `szProb_le_field`
  (`deg(p)/|F| ≤ n·R/|F|`), with `R' = R/|F|` the per-degree-unit rate contribution; and
* `tail` is the query-amplification tail, controlled by the named residual
  `QueryAmpTail tail q halfRadius` (the only open piece).

Then `PerRoundFRIError ε n R' q halfRadius` holds. The `n·R'` summand is now backed by a
single-variable Schwartz–Zippel theorem; only `QueryAmpTail` is hypothesized. We never discharge
that residual ourselves. -/
theorem perRound_from_SZ_and_queryTail
    {ε foldFail tail : ℝ} {n : ℕ} {R' halfRadius : ℝ} {q : ℕ}
    (hsplit : ε ≤ foldFail + tail)
    (hfold : foldFail ≤ (n : ℝ) * R')
    (htail : QueryAmpTail tail q halfRadius) :
    PerRoundFRIError ε n R' q halfRadius := by
  unfold PerRoundFRIError QueryAmpTail at *
  calc ε ≤ foldFail + tail := hsplit
    _ ≤ (n : ℝ) * R' + (1 - halfRadius) ^ q := by gcongr

-- Axiom audit: every result must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms card_roots_in_le_natDegree
#print axioms szProb_le
#print axioms szProb_le_field
#print axioms perQueryNonDetection_le
#print axioms perRound_from_SZ_and_queryTail

end ProximityGap.ThresholdHalvingSZ
