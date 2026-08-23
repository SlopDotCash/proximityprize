/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ThresholdHalvingPerRound

/-!
# BRICK L1g — query-survival: the `(1 − δ/2)^q` term, combinatorial core PROVEN

**Target.** Attack the genuinely-open named residual carried by the threshold-halving per-round
accounting, `QuerySoundnessBound qErr halfRadius q := qErr ≤ (1 − halfRadius)^q` (from
`_ThresholdHalvingPerRound`). That `Prop` encodes the FRI **query-survival** tail of the
ePrint 2026/858 (Chai–Fan) lossy above-Johnson route:

> `q` INDEPENDENT FRI queries, each detecting a `δ/2`-far word with probability `≥ δ/2`
> (`= halfRadius`), so the *all-miss* (survival) probability is `≤ (1 − halfRadius)^q`.

The statement factors into two layers that live in two different mathematical realms:

1. **The deterministic product bound (PURELY COMBINATORIAL — PROVEN HERE).** Given a per-query
   *miss-probability vector* `pMiss : Fin q → ℝ` with `0 ≤ pMiss i ≤ 1 − halfRadius` for every
   query `i`, the product of the per-query miss probabilities is bounded by the `q`-th power:
   `∏ᵢ pMiss i ≤ (1 − halfRadius)^q`. This is a clean order-theoretic fact (`Finset.prod_le_prod`
   against the constant function, then `Finset.prod_const`). It is fully proven, `sorry`-free, and
   axiom-clean.

2. **The independence → product step (PROBABILISTIC — the ONE named residual).** That the *joint*
   all-`q`-queries-miss probability `survival` equals (or is bounded by) the **product** of the
   per-query miss probabilities `∏ᵢ pMiss i` is the measure-theoretic *independence* content
   (`Pr[⋂ᵢ Mᵢ] = ∏ᵢ Pr[Mᵢ]` for independent events `Mᵢ`). The FRI-specific probability space and
   the independence of the `q` query draws are **not** in this tree, so this step is carried as one
   explicit named `Prop` (`QueryIndependenceFactorization`), never silently discharged and never
   vacuous (it is a genuine non-trivial product inequality on reals).

Chaining (2) then (1) discharges the named `QuerySoundnessBound` into the proven combinatorial core.

## What is proven vs. named (honest scope)

| piece | status |
|---|---|
| `prod_miss_le_pow` (`∏ pMiss ≤ (1−h)^q`, the combinatorial core) | **PROVEN** |
| `prod_miss_le_pow_univ` (the `Fin q` specialization, `#univ = q`) | **PROVEN** |
| `querySoundness_of_prod_bound` (product bound ⟹ `QuerySoundnessBound`) | **PROVEN** |
| `QueryIndependenceFactorization` (`survival ≤ ∏ pMiss`, the measure step) | **NAMED** |
| `querySoundnessBound_of_independence` (independence + core ⟹ `QuerySoundnessBound`) | **DERIVED** |

The genuinely-open input has been *shrunk* from "the whole `(1 − δ/2)^q` survival tail" to the
single measure-theoretic independence factorization `survival ≤ ∏ pMiss` — the deterministic power
bound is now a theorem.

## Honesty / scope

This is the **LOSSY (≈ 2× query) above-Johnson route**, NOT the grand zero-loss `δ*` (the open BGK
wall). Everything proven rests only on Mathlib's ordered-semiring product monotonicity; the axiom
audit at the bottom must be `⊆ {propext, Classical.choice, Quot.sound}` (no `sorryAx`). The single
named `QueryIndependenceFactorization` is a genuine non-trivial real inequality (the FRI query
independence), never replaced by a vacuous/trivially-true Prop and never silently discharged.
-/

namespace ProximityGap.ThresholdHalvingQuerySurvival

open Finset
open ProximityGap.ThresholdHalvingPerRound

/-! ### The combinatorial core (PROVEN): product of per-query miss probabilities ≤ `(1−h)^q`

The deterministic heart of the query-survival bound. We do not assume independence here; we only
take a per-query miss-probability *vector* `pMiss` already known to be in `[0, 1 − halfRadius]`
entrywise, and bound its product by the constant power. The proof is `Finset.prod_le_prod` against
the constant `fun _ => 1 − halfRadius`, followed by `Finset.prod_const`. -/

/-- **Per-query product bound (PROVEN, general index `Finset`).** For a per-query miss-probability
function `pMiss : ι → ℝ` that is entrywise in `[0, c]` over a finite query set `s` (with
`c = 1 − halfRadius`), the product over `s` is bounded by `c ^ #s`:
`∏_{i ∈ s} pMiss i ≤ c ^ #s`. Pure ordered-semiring product monotonicity — no independence, no
probability, no `sorry`. -/
theorem prod_miss_le_pow {ι : Type*} (s : Finset ι) (pMiss : ι → ℝ) (c : ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ pMiss i) (hc : ∀ i ∈ s, pMiss i ≤ c) :
    ∏ i ∈ s, pMiss i ≤ c ^ s.card := by
  calc ∏ i ∈ s, pMiss i
      ≤ ∏ _i ∈ s, c := Finset.prod_le_prod h0 hc
    _ = c ^ s.card := Finset.prod_const c

/-- **Per-query product bound over `Fin q` (PROVEN).** For `q` queries indexed by `Fin q` with
per-query miss-probability vector `pMiss : Fin q → ℝ` entrywise in `[0, 1 − halfRadius]`, the
product of all per-query miss probabilities is bounded by `(1 − halfRadius)^q`. This is the exact
deterministic shape of the FRI survival tail's *combinatorial core* — the all-queries-miss product,
once independence has reduced the joint probability to the product. -/
theorem prod_miss_le_pow_univ {q : ℕ} (pMiss : Fin q → ℝ) (halfRadius : ℝ)
    (h0 : ∀ i, 0 ≤ pMiss i) (hc : ∀ i, pMiss i ≤ 1 - halfRadius) :
    ∏ i : Fin q, pMiss i ≤ (1 - halfRadius) ^ q := by
  have h := prod_miss_le_pow (Finset.univ : Finset (Fin q)) pMiss (1 - halfRadius)
    (fun i _ => h0 i) (fun i _ => hc i)
  simpa only [Finset.card_univ, Fintype.card_fin] using h

/-- **Product bound ⟹ `QuerySoundnessBound` (PROVEN bridge).** If the survival probability `qErr`
is bounded by the product of the per-query miss probabilities `∏ᵢ pMiss i`, and that product is in
turn bounded by `(1 − halfRadius)^q` (the proven combinatorial core), then the named
`QuerySoundnessBound qErr halfRadius q` holds. The product bound is supplied by
`prod_miss_le_pow_univ`; the `qErr ≤ ∏` premise is the (named, elsewhere) independence step. -/
theorem querySoundness_of_prod_bound {q : ℕ} {qErr halfRadius : ℝ} (pMiss : Fin q → ℝ)
    (h0 : ∀ i, 0 ≤ pMiss i) (hc : ∀ i, pMiss i ≤ 1 - halfRadius)
    (hfactor : qErr ≤ ∏ i : Fin q, pMiss i) :
    QuerySoundnessBound qErr halfRadius q := by
  unfold QuerySoundnessBound
  exact le_trans hfactor (prod_miss_le_pow_univ pMiss halfRadius h0 hc)

/-! ### The named probabilistic residual: independence → product factorization

The single genuinely-open step. The deterministic core above bounds the *product* of per-query miss
probabilities; turning the *joint* all-queries-miss (survival) probability `survival` into that
product is the measure-theoretic independence content `Pr[⋂ᵢ Mᵢ] = ∏ᵢ Pr[Mᵢ]`. The FRI probability
space and the mutual independence of the `q` query draws are not in this tree, so we carry the step
as one explicit named `Prop`. It is a genuine non-trivial inequality on reals (it relates a joint
survival probability to a product of marginals), not a vacuous carrier. -/

/-- Named **query-independence factorization residual** (NOT proven here — the measure-theoretic
independence content). `QueryIndependenceFactorization survival pMiss` is meant to hold exactly when
the joint all-`q`-queries-miss (survival) probability `survival` is dominated by the product of the
per-query miss probabilities `∏ᵢ pMiss i`. For genuinely *independent* query draws this is an
equality (`Pr[⋂ Mᵢ] = ∏ Pr[Mᵢ]`); the FRI-specific independence proof is not in this tree, so we
keep it abstract. This is the single remaining open obligation after the deterministic product core
`prod_miss_le_pow_univ` is discharged. -/
def QueryIndependenceFactorization {q : ℕ} (survival : ℝ) (pMiss : Fin q → ℝ) : Prop :=
  survival ≤ ∏ i : Fin q, pMiss i

/-- **The headline (DERIVED): independence factorization + combinatorial core ⟹
`QuerySoundnessBound`.**

Fix `q` queries with per-query miss-probability vector `pMiss : Fin q → ℝ`, each in
`[0, 1 − halfRadius]` (each query detects a `δ/2`-far word with probability `≥ halfRadius`, so it
*misses* with probability `≤ 1 − halfRadius`, and a probability is `≥ 0`). Given the single named
independence residual `QueryIndependenceFactorization survival pMiss` (the joint survival probability
is dominated by the product of marginals), the named `QuerySoundnessBound survival halfRadius q`
holds — i.e. `survival ≤ (1 − halfRadius)^q`.

The probabilistic content lives entirely in the named `QueryIndependenceFactorization`; the power
bound `∏ ≤ (1 − halfRadius)^q` is the proven combinatorial core. We never discharge the
independence residual ourselves. -/
theorem querySoundnessBound_of_independence {q : ℕ} {survival halfRadius : ℝ} (pMiss : Fin q → ℝ)
    (h0 : ∀ i, 0 ≤ pMiss i) (hc : ∀ i, pMiss i ≤ 1 - halfRadius)
    (hindep : QueryIndependenceFactorization survival pMiss) :
    QuerySoundnessBound survival halfRadius q :=
  querySoundness_of_prod_bound pMiss h0 hc hindep

/-! ### Sanity: the bound is a genuine (nonnegative, ≤ 1) survival probability

We record two non-vacuity checks so the produced bound is a real survival probability and not a
degenerate one. They are pure facts about the combinatorial core. -/

/-- The combinatorial core's bound `(1 − halfRadius)^q` is nonnegative whenever `halfRadius ≤ 1`
(`halfRadius = δ/2 ≤ 1/2 < 1` in the window), so the survival bound is a genuine nonnegative
probability bound and not vacuously negative. -/
theorem pow_bound_nonneg {q : ℕ} {halfRadius : ℝ} (h : halfRadius ≤ 1) :
    0 ≤ (1 - halfRadius) ^ q :=
  pow_nonneg (by linarith) q

/-- The combinatorial core's bound `(1 − halfRadius)^q ≤ 1` whenever `0 ≤ halfRadius ≤ 1`, so the
survival bound never exceeds a probability of `1`. (More queries `q` can only shrink it.) -/
theorem pow_bound_le_one {q : ℕ} {halfRadius : ℝ} (h0 : 0 ≤ halfRadius) (h1 : halfRadius ≤ 1) :
    (1 - halfRadius) ^ q ≤ 1 :=
  pow_le_one₀ (by linarith) (by linarith)

/-- The proven product core itself is nonnegative (a product of nonnegative per-query miss
probabilities), confirming the survival bound chain stays within `[0, (1−halfRadius)^q]`. -/
theorem prod_miss_nonneg {q : ℕ} (pMiss : Fin q → ℝ) (h0 : ∀ i, 0 ≤ pMiss i) :
    0 ≤ ∏ i : Fin q, pMiss i :=
  Finset.prod_nonneg (fun i _ => h0 i)

-- Axiom audit: every result must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms prod_miss_le_pow
#print axioms prod_miss_le_pow_univ
#print axioms querySoundness_of_prod_bound
#print axioms querySoundnessBound_of_independence
#print axioms pow_bound_nonneg
#print axioms pow_bound_le_one
#print axioms prod_miss_nonneg

end ProximityGap.ThresholdHalvingQuerySurvival
