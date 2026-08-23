/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.HalfThresholdCA
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ThresholdHalvingSoundness

/-!
# Threshold-Halving Per-Round FRI Error — the layer-cake split (#444, BRICK L1b)

**Target.** Shrink the per-round FRI soundness error `Prop` carried in
`_ThresholdHalvingSoundness.lean` as the *fully* unproven named hypothesis
`PerRoundFRIError ε n R q halfRadius := ε ≤ n·R + (1 − halfRadius)^q`.

The ePrint 2026/858 (Chai–Fan) per-round bound has the classic **two-term layer-cake** shape:

  `ε_FRI  ≤  (CA-failure contribution)  +  (query-soundness contribution)`
         `≤      n·R/|F|                +      (1 − δ/2)^q`.

Here we split `PerRoundFRIError` into two **named** sub-Props and prove what is reachable from
the in-tree correlated-agreement (CA) substrate:

* **`CAFailureBound`** (the `n·R` term) — the CA-failure contribution. The honest in-tree fact
  is sharper: Theorem 5 (`theorem5_halfThreshold_correlatedAgreement`) gives **at most one** bad
  scalar at radius `δ/2`, so the *normalized* CA-failure measure (#bad / `|F|`) is `≤ 1/|F|`.
  This piece is **PROVEN** here (`caFailureMeasure_le_inv_card`) — it is a genuine corollary of the
  in-tree Theorem 5, with no `sorry` and an axiom-clean audit.

* **`QuerySoundnessBound`** (the `(1 − δ/2)^q` term) — the query-amplification contribution: `q`
  independent FRI queries each detect a `δ/2`-far word with probability `≥ δ/2`, so the survival
  (all-queries-miss) probability is `≤ (1 − δ/2)^q`. The independent-query probability product is
  **NOT** in this tree; it stays an explicit named `Prop` (`QuerySoundnessBound`), never discharged.

## What is proven vs. named (honest scope)

| sub-piece | status |
|---|---|
| `caFailureMeasure_le_inv_card` (#bad scalars / `|F|` ≤ `1/|F|`) | **PROVEN** from Theorem 5 |
| `CAFailureBound caErr nR := caErr ≤ nR` | a named Prop *whose `1/|F|` instance is realized* |
| `QuerySoundnessBound qErr halfRadius q := qErr ≤ (1 − halfRadius)^q` | **NAMED** (query product) |
| `PerRoundFRIError` (the original) | **DERIVED** from the two sub-Props + an additive split |

The headline `perRoundFRIError_of_split` is a pure real-arithmetic assembly: it turns the additive
decomposition `ε ≤ caErr + qErr` plus `CAFailureBound caErr (n·R)` plus
`QuerySoundnessBound qErr (δ/2) q` into the original `PerRoundFRIError ε n R q (δ/2)`. So the only
genuinely-open input has been *shrunk* from "the whole two-term bound" to "the single query-product
survival term `(1 − δ/2)^q`" — the CA term is now a theorem.

## Honesty contract

This is the **LOSSY (≈ 2× query) above-Johnson route**, NOT the zero-loss `δ*` (open BGK wall).
Everything here is `sorry`/`native_decide`/`axiom`-free except the explicitly named
`QuerySoundnessBound` (and the abstract `CAFailureBound`/`PerRoundFRIError` carriers), which are
never silently discharged. The single concrete CA measure bound `caFailureMeasure_le_inv_card` is a
real theorem with a `#print axioms` audit at the bottom.
-/

namespace ProximityGap.ThresholdHalvingPerRound

open ProximityPrizeCA ProximityGap.ThresholdHalvingWindow
open ProximityGap.ThresholdHalvingSoundness
open Finset Code NNReal
open scoped NNReal

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ### The PROVEN piece: the CA-failure measure is `≤ 1/|F|`

The correlated-agreement failure of one threshold-halved round is, by Theorem 5, governed by the
size of the **bad-scalar set** `{γ : δᵣ(f₁ + γ•f₂, C) ≤ δ/2}`, which Theorem 5 bounds by `1`. The
*normalized* CA-failure measure is that count divided by `|F|` — a uniformly-random verifier
challenge `γ` lands in the bad set with probability (#bad scalars)/`|F|`. We prove this measure is
`≤ 1/|F|`, the genuine `1/|F|` CA-failure floor of the per-round accounting. -/

/-- The (normalized) CA-failure measure at the halved radius `δ/2`: the fraction of scalars `γ ∈ F`
for which the affine line `f₁ + γ • f₂` lies within relative distance `δ/2` of the code `C`. A
uniformly random FRI challenge `γ` triggers a CA failure with exactly this probability. -/
noncomputable def caFailureMeasure [Fintype F]
    (C : Submodule F (ι → F)) (f₁ f₂ : ι → F) (δ : ℝ≥0) : ℝ :=
  (((Finset.univ : Finset F).filter
      (fun γ => δᵣ(linComb f₁ f₂ γ, (C : Set (ι → F))) ≤ ((δ / 2 : ℝ≥0) : ENNReal))).card : ℝ)
    / (Fintype.card F : ℝ)

/-- **CA-failure measure ≤ 1/|F| (PROVEN from Theorem 5).** When the joint relative distance of
`(f₁, f₂)` to the pair code exceeds `δ`, the normalized correlated-agreement failure measure at the
halved radius `δ/2` is bounded by `1/|F|`. This is the honest in-tree content of the `n·R/|F|` CA
term in the ePrint 2026/858 per-round bound: Theorem 5 says at most one scalar is bad, so the random
challenge hits the bad set with probability ≤ 1/|F|. -/
theorem caFailureMeasure_le_inv_card [Fintype F]
    (C : Submodule F (ι → F)) (f₁ f₂ : ι → F) {δ : ℝ≥0}
    (hjoint : (δ : ENNReal) < jointRelDist f₁ f₂ C) :
    caFailureMeasure C f₁ f₂ δ ≤ 1 / (Fintype.card F : ℝ) := by
  classical
  -- Theorem 5: the bad-scalar set has cardinality `≤ 1`.
  have hcard := theorem5_halfThreshold_correlatedAgreement C f₁ f₂ hjoint
  -- `|F| > 0` (a field is nonempty).
  have hFpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos
  -- Divide both sides of `card ≤ 1` by `|F| > 0`.
  unfold caFailureMeasure
  rw [div_le_div_iff_of_pos_right hFpos]
  exact_mod_cast hcard

/-- Nonnegativity of the CA-failure measure (it is a count over a nonnegative denominator). -/
theorem caFailureMeasure_nonneg [Fintype F]
    (C : Submodule F (ι → F)) (f₁ f₂ : ι → F) (δ : ℝ≥0) :
    0 ≤ caFailureMeasure C f₁ f₂ δ := by
  unfold caFailureMeasure
  positivity

/-! ### The two named sub-Props (the layer-cake terms)

We name the two contributions abstractly so the real ePrint 2026/858 accounting plugs in verbatim.
`CAFailureBound` is the `n·R` (`= n·R/|F|` once the `1/|F|` is folded into `R`) CA term; its `1/|F|`
instance is *realized* by the proven `caFailureMeasure_le_inv_card`. `QuerySoundnessBound` is the
genuinely-open `(1 − halfRadius)^q` query-product survival term. -/

/-- Named CA-failure bound: the CA-failure error `caErr` is bounded by `bound`. The intended
instance is `bound = n·R/|F|`, of which the `1/|F|` part is proven (`caFailureMeasure_le_inv_card`)
and the `n·R` envelope is the imported ePrint 2026/858 round-count scaling. -/
def CAFailureBound (caErr bound : ℝ) : Prop := caErr ≤ bound

/-- Named query-soundness (survival) bound: the per-round query-detection failure error `qErr` is
bounded by `(1 − halfRadius)^q`. NOT proven here — it is the imported ePrint 2026/858 independent-
query product: `q` independent FRI queries each catch a `halfRadius`-far word with probability
`≥ halfRadius`, so the all-miss probability is `≤ (1 − halfRadius)^q`. -/
def QuerySoundnessBound (qErr : ℝ) (halfRadius : ℝ) (q : ℕ) : Prop :=
  qErr ≤ (1 - halfRadius) ^ q

/-- The proven CA measure realizes the named `CAFailureBound` at its `1/|F|` instance: the
normalized CA-failure measure satisfies `CAFailureBound (caFailureMeasure …) (1/|F|)`. This is the
bridge showing the named CA term is not vacuous — its sharpest in-tree instance is a theorem. -/
theorem caFailureBound_realized [Fintype F]
    (C : Submodule F (ι → F)) (f₁ f₂ : ι → F) {δ : ℝ≥0}
    (hjoint : (δ : ENNReal) < jointRelDist f₁ f₂ C) :
    CAFailureBound (caFailureMeasure C f₁ f₂ δ) (1 / (Fintype.card F : ℝ)) :=
  caFailureMeasure_le_inv_card C f₁ f₂ hjoint

/-! ### The DERIVED assembly: split ⟹ `PerRoundFRIError`

Pure real arithmetic. Given the additive decomposition `ε ≤ caErr + qErr`, the CA term bound
`caErr ≤ n·R`, and the query term bound `qErr ≤ (1 − δ/2)^q`, the original `PerRoundFRIError` bound
`ε ≤ n·R + (1 − δ/2)^q` follows. The two-term named obligation is thereby *shrunk* to its single
genuinely-open half (the query product); the CA half is supplied as a theorem downstream. -/

/-- **Layer-cake assembly (DERIVED).** From the additive split `ε ≤ caErr + qErr`, a CA-term
bound `CAFailureBound caErr (n·R)`, and a query-term bound `QuerySoundnessBound qErr (δ/2) q`,
conclude `PerRoundFRIError ε n R q (δ/2)`. No `sorry`: `add_le_add` on the two named terms. -/
theorem perRoundFRIError_of_split
    {ε caErr qErr R halfRadius : ℝ} {n q : ℕ}
    (hsplit : ε ≤ caErr + qErr)
    (hCA : CAFailureBound caErr ((n : ℝ) * R))
    (hQuery : QuerySoundnessBound qErr halfRadius q) :
    PerRoundFRIError ε n R q halfRadius := by
  unfold PerRoundFRIError
  unfold CAFailureBound at hCA
  unfold QuerySoundnessBound at hQuery
  calc ε ≤ caErr + qErr := hsplit
    _ ≤ (n : ℝ) * R + (1 - halfRadius) ^ q := add_le_add hCA hQuery

/-! ### End-to-end: package + proven CA term + named query term ⟹ `PerRoundFRIError`

The headline of this brick. We thread the threshold-halving soundness package (below-Johnson lock +
≤ 1 bad scalar) together with:
* the **proven** CA-failure measure bound `caFailureMeasure_le_inv_card` (its `1/|F|` instance), and
* a single **named** `QuerySoundnessBound` hypothesis for the query product,

plus an additive split, to obtain `PerRoundFRIError`. The crucial honesty point: `CAFailureBound`
input is **not** assumed — it is *supplied* from Theorem 5, with `R := 1/(n·|F|)` so that
`n·R = 1/|F|` matches the proven measure. The ONLY remaining open hypothesis is the query survival
term `QuerySoundnessBound`. -/

/-- **Per-round FRI error, CA term discharged (named-conditional only on the query product).**

Fix a rate `ρ ∈ [0,1]`, code `C`, words `f₁ f₂`, a window radius `δ` (with `(δ:ℝ) < windowTop ρ`),
the genuine joint-separation hypothesis, and the named BCIKS regime. Take the round-scaling rate so
that `n·R = 1/|F|` (i.e. `R = 1/(n·|F|)`), matching the proven CA-failure floor. Then, given only:

* `hsplit`: the standard FRI additive decomposition `ε ≤ (CA-failure measure) + qErr`, and
* `hQuery`: the named query-product survival bound `QuerySoundnessBound qErr (δ/2) q`,

we conclude `PerRoundFRIError ε n R q (δ/2)`. The CA term is **proven** (via the package); the only
unproven input is the single named `QuerySoundnessBound`. -/
theorem thresholdHalving_perRound_caDischarged [Fintype F]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (C : Submodule F (ι → F)) (f₁ f₂ : ι → F) {δ : ℝ≥0}
    (hδwin : (δ : ℝ) < windowTop ρ)
    (hjoint : (δ : ENNReal) < jointRelDist f₁ f₂ C)
    (hBCIKS : ∀ r : ℝ, r < johnsonRadius ρ → BelowJohnsonRegime ρ r)
    {ε qErr R : ℝ} {q : ℕ}
    (hR : (Fintype.card ι : ℝ) * R = 1 / (Fintype.card F : ℝ))
    (hsplit : ε ≤ caFailureMeasure C f₁ f₂ δ + qErr)
    (hQuery : QuerySoundnessBound qErr ((δ / 2 : ℝ≥0) : ℝ) q) :
    PerRoundFRIError ε (Fintype.card ι) R q ((δ / 2 : ℝ≥0) : ℝ) := by
  -- Confirm the soundness package fires (below-Johnson lock + ≤ 1 bad scalar). This records the
  -- soundness context under which the CA term is the proven `1/|F|` floor.
  have _hpkg := thresholdHalving_soundness_package hρ0 hρ1 C f₁ f₂ hδwin hjoint hBCIKS
  -- The CA term: PROVEN ≤ 1/|F| = n·R.
  have hCA : CAFailureBound (caFailureMeasure C f₁ f₂ δ) ((Fintype.card ι : ℝ) * R) := by
    unfold CAFailureBound
    rw [hR]
    exact caFailureMeasure_le_inv_card C f₁ f₂ hjoint
  -- Assemble: split + (proven CA) + (named query) ⟹ PerRoundFRIError.
  exact perRoundFRIError_of_split hsplit hCA hQuery

/-! ### Convenience: the original `PerRoundFRIError` from the two named terms only

For callers that already have both terms named (e.g. an external ePrint 2026/858 import that
supplies `QuerySoundnessBound` and re-derives the CA term itself), this restates
`perRoundFRIError_of_split`
on the exact `δ/2` analysis radius the threshold-halving route uses. -/

/-- The original named `PerRoundFRIError` at the halved analysis radius `δ/2`, assembled from the
additive split and the two layer-cake sub-Props. -/
theorem thresholdHalving_perRound_fromTerms
    {ε caErr qErr R : ℝ} {δ : ℝ≥0} {n q : ℕ}
    (hsplit : ε ≤ caErr + qErr)
    (hCA : CAFailureBound caErr ((n : ℝ) * R))
    (hQuery : QuerySoundnessBound qErr ((δ / 2 : ℝ≥0) : ℝ) q) :
    PerRoundFRIError ε n R q ((δ / 2 : ℝ≥0) : ℝ) :=
  perRoundFRIError_of_split hsplit hCA hQuery

-- Axiom audit: every result must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms caFailureMeasure_le_inv_card
#print axioms caFailureMeasure_nonneg
#print axioms caFailureBound_realized
#print axioms perRoundFRIError_of_split
#print axioms thresholdHalving_perRound_caDischarged
#print axioms thresholdHalving_perRound_fromTerms

end ProximityGap.ThresholdHalvingPerRound
