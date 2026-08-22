/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
# Multi-Round FRI Soundness Composition — #444 frontier (ePrint 2026/858 route)

**Target (BRICK L1c).** The multi-round composition brick of the threshold-halving FRI
soundness route (Chai–Fan, ePrint 2026/858, the LOSSY ≈ 2×-query above-Johnson route).

The single-round analysis (`HalfThresholdCA.theorem5_halfThreshold_correlatedAgreement` and the
packaged `_ThresholdHalvingSoundness.thresholdHalving_perRound_soundness`) certifies a *per-round*
FRI soundness error `εᵢ` for round `i`. A full FRI instance runs `r` such rounds; a cheating
prover succeeds against the whole protocol only if it succeeds against *some* round, so by the
**union bound** the overall soundness error is at most the sum of the per-round errors:

  `ε_total ≤ ∑ᵢ εᵢ`.

When every round uses the *same* threshold-halving package, each `εᵢ` is the constant per-round
error `ε`, and the sum collapses to the familiar

  `ε_total ≤ r · ε`.

This file proves the **pure arithmetic core** of that composition — the sum bound and its
constant-round specialization — abstractly over a `Finset` (or `Fin r`) of rounds with per-round
error bounds, using `Finset.sum_le_sum` / `Finset.sum_le_card_nsmul`. The genuinely
*probabilistic* step (that the multi-round soundness error is actually dominated by the union of
the per-round failure events) is **not** a real-arithmetic fact: it is the measure-theoretic union
bound over the protocol's failure events, whose FRI-specific instantiation is not in this tree. We
therefore carry it as one explicit named `Prop` (`UnionBoundOverRounds`), never a hidden `sorry`,
and show that **given** it the total-error bounds follow by the proven sum arithmetic.

## What is proven vs. named

* PROVEN (pure, `sorry`/`axiom`-free, real arithmetic):
  - `sum_per_round_le_sum_bounds`  : `∑ εᵢ ≤ ∑ Bᵢ` from `εᵢ ≤ Bᵢ` (monotone sums).
  - `sum_const_round_error`        : `∑_{i∈univ} ε = r · ε` over `Fin r` (constant rounds).
  - `sum_per_round_le_card_nsmul`  : `∑ εᵢ ≤ #rounds · B` from a uniform per-round bound `B`.
  - `total_error_le_sum`           : chains `UnionBoundOverRounds` with the sum (the headline).
  - `total_error_le_card_mul`      : `ε_total ≤ #rounds · B` (uniform per-round bound).
  - `total_error_le_rounds_mul`    : `ε_total ≤ r · ε` over `Fin r` (constant per-round error).

* NAMED (the imported probabilistic union bound, NOT proven here):
  - `UnionBoundOverRounds εTot rounds ε` : `εTot ≤ ∑_{i∈rounds} ε i`.

## Honesty / scope

This is the **LOSSY** above-Johnson composition, NOT the grand zero-loss `δ*` (the open BGK wall).
The per-round error `εᵢ` is supplied by the threshold-halving package, whose own analysis radius is
`δ/2` (≈ 2× query penalty). Composition here only does the union-bound bookkeeping across rounds;
it neither sharpens the per-round error nor escapes the Johnson barrier. Everything is
`sorry`/`axiom`-free except the single explicitly named `UnionBoundOverRounds` hypothesis, which is
never silently discharged.
-/

namespace ProximityGap.ThresholdHalvingCompose

open Finset

/-! ### Pure sum arithmetic (fully proven)

The union-bound bookkeeping is, once the probabilistic step is granted, pure ordered-field
arithmetic on `Finset` sums. We isolate the three facts we need. -/

/-- **Monotone round-sum.** If each round's soundness error `ε i` is bounded by `B i`, the total
(summed) error is bounded by the summed bounds. Pure `Finset.sum_le_sum`. -/
theorem sum_per_round_le_sum_bounds {ι : Type*} (rounds : Finset ι) (ε B : ι → ℝ)
    (h : ∀ i ∈ rounds, ε i ≤ B i) :
    ∑ i ∈ rounds, ε i ≤ ∑ i ∈ rounds, B i :=
  Finset.sum_le_sum h

/-- **Uniform-bound round-sum.** If every round's soundness error is at most the *same* bound `B`,
the total error is at most `#rounds · B`. This is the constant-per-round union-bound collapse
stated over an arbitrary index `Finset`. -/
theorem sum_per_round_le_card_nsmul {ι : Type*} (rounds : Finset ι) (ε : ι → ℝ) {B : ℝ}
    (h : ∀ i ∈ rounds, ε i ≤ B) :
    ∑ i ∈ rounds, ε i ≤ rounds.card • B :=
  Finset.sum_le_card_nsmul rounds ε B h

/-- **Constant round-sum over `Fin r`.** The sum of a constant per-round error `ε` over the `r`
rounds `Fin r` is exactly `r · ε`. This is the `∑ = r·ε` step of the threshold-halving
composition, where each round shares the single package error `ε`. -/
theorem sum_const_round_error (r : ℕ) (ε : ℝ) :
    ∑ _i : Fin r, ε = (r : ℝ) * ε := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The named probabilistic union bound (NOT proven here)

The genuinely measure-theoretic step: across the `r` FRI rounds, a cheating prover succeeds against
the composed protocol only if it succeeds against some single round, so the overall soundness error
`εTot` is dominated by the union of the per-round failure events, hence by `∑ εᵢ`. The FRI-specific
event structure that justifies this is not in this tree; we carry the conclusion as an explicit
named predicate so any real soundness substrate plugs in verbatim. -/

/-- Named multi-round union-bound predicate (NOT proven here — it is the imported probabilistic
soundness composition). `UnionBoundOverRounds εTot rounds ε` is meant to hold exactly when the
composed-protocol soundness error `εTot` is dominated by the sum of the per-round errors `ε i` over
`rounds`. We keep it abstract so any real FRI soundness accounting plugs in. -/
def UnionBoundOverRounds {ι : Type*} (εTot : ℝ) (rounds : Finset ι) (ε : ι → ℝ) : Prop :=
  εTot ≤ ∑ i ∈ rounds, ε i

/-! ### The composition theorems (named-conditional headlines)

Each chains the single named `UnionBoundOverRounds` hypothesis with the proven sum arithmetic. The
union bound supplies `εTot ≤ ∑ εᵢ`; the arithmetic upgrades the right side to a clean closed form
(`∑ Bᵢ`, `#rounds · B`, or `r · ε`). The probabilistic content lives entirely in the named
hypothesis; everything else is `sorry`-free real arithmetic. -/

/-- **Composition (general per-round bounds).** Given the named union bound and a per-round bound
`ε i ≤ B i`, the total soundness error is at most the summed bounds `∑ Bᵢ`. -/
theorem total_error_le_sum {ι : Type*} {εTot : ℝ} (rounds : Finset ι) {ε B : ι → ℝ}
    (hUnion : UnionBoundOverRounds εTot rounds ε)
    (hbound : ∀ i ∈ rounds, ε i ≤ B i) :
    εTot ≤ ∑ i ∈ rounds, B i :=
  le_trans hUnion (sum_per_round_le_sum_bounds rounds ε B hbound)

/-- **Composition (uniform per-round bound).** Given the named union bound and a *uniform*
per-round bound `ε i ≤ B`, the total soundness error is at most `#rounds · B`. -/
theorem total_error_le_card_mul {ι : Type*} {εTot : ℝ} (rounds : Finset ι) {ε : ι → ℝ} {B : ℝ}
    (hUnion : UnionBoundOverRounds εTot rounds ε)
    (hbound : ∀ i ∈ rounds, ε i ≤ B) :
    εTot ≤ rounds.card • B :=
  le_trans hUnion (sum_per_round_le_card_nsmul rounds ε hbound)

/-- **Composition (constant per-round error over `r` rounds).** This is the headline
threshold-halving composition: if the FRI protocol runs `r` rounds, each with the *same* package
soundness error `ε`, and the named union bound holds, the total soundness error is at most `r · ε`.

The constant-`ε` round function is `fun _ : Fin r => ε`; `UnionBoundOverRounds εTot univ (fun _ => ε)`
is the union bound over all `r` rounds, and the sum collapses to `r · ε` by `sum_const_round_error`.
-/
theorem total_error_le_rounds_mul {εTot : ℝ} (r : ℕ) (ε : ℝ)
    (hUnion : UnionBoundOverRounds εTot (Finset.univ : Finset (Fin r)) (fun _ => ε)) :
    εTot ≤ (r : ℝ) * ε := by
  have hsum : εTot ≤ ∑ _i : Fin r, ε := hUnion
  rwa [sum_const_round_error r ε] at hsum

/-! ### Sanity: nonnegativity is preserved (the bounds stay valid errors)

A composed soundness error built from nonnegative per-round errors is itself bounded by a
nonnegative quantity, so the bounds above are genuine (nonnegative) soundness errors and not
vacuously satisfied by a negative right-hand side. These are pure facts about sums of nonnegatives.
-/

/-- The summed per-round bound is nonnegative when each bound is, so `total_error_le_sum` produces a
genuine (nonnegative) soundness bound. -/
theorem sum_bounds_nonneg {ι : Type*} (rounds : Finset ι) {B : ι → ℝ}
    (hB : ∀ i ∈ rounds, 0 ≤ B i) :
    0 ≤ ∑ i ∈ rounds, B i :=
  Finset.sum_nonneg hB

/-- The constant-round bound `r · ε` is nonnegative for a nonnegative per-round error `ε`. -/
theorem rounds_mul_nonneg (r : ℕ) {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ (r : ℝ) * ε :=
  mul_nonneg (Nat.cast_nonneg r) hε

-- Axiom audit: every result must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms sum_per_round_le_sum_bounds
#print axioms sum_per_round_le_card_nsmul
#print axioms sum_const_round_error
#print axioms total_error_le_sum
#print axioms total_error_le_card_mul
#print axioms total_error_le_rounds_mul
#print axioms sum_bounds_nonneg
#print axioms rounds_mul_nonneg

end ProximityGap.ThresholdHalvingCompose
