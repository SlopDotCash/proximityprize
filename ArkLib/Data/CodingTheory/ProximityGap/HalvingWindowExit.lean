/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Refutation of hypothesis N3 (#357): the halving map exits the window in one step

Hypothesis N3 of the #357 campaign slate proposed iterating the threshold-halving map
`T : δ ↦ δ/2` (the 2026/858 move, in-tree as
`ArkLib.ProximityGap.ProofLoop42.threshold_halving_into_unique_decoding`) and extracting
a fixpoint-band structure on the open window `(1−√ρ, 1−ρ)` that would force `δ*` to a
band edge.

**The kill-check kills it.**  For every rate `ρ ∈ [0, 1)` and every `δ` below capacity
(`δ < 1−ρ` — in particular everywhere in the window), the halved threshold already lies
*strictly below the Johnson radius*:

    δ/2 < (1−ρ)/2 ≤ 1−√ρ,

the second inequality being `(1−√ρ)² ≥ 0` in disguise.  So the very first iterate exits
the window; the orbit of every window point is `window → below-Johnson → … → 0`; the
unique fixpoint of `T` is `δ = 0`; and the "fixpoint bands" partition of the window is
the trivial one.  There is no renormalization structure to exploit *for this map*: any
fixpoint analysis of the window requires a map that re-enters it, which halving never
does.  (This is also exactly *why* 2026/858 works as a protocol trick — one halving
suffices to land in unique decoding — and why it cannot say anything about `ε_mca`
inside the window.)

Verdict for the campaign ledger: **N3 REFUTED at kill-check** — recorded here as the
constraint lemma `halving_exits_window`, per the standing disprove-then-keep-the-lemma
discipline (`DISPROOF_LOG.md`).
-/

namespace ProximityGap.Issue357

/-- The Johnson radius dominates half the capacity: `(1−ρ)/2 ≤ 1−√ρ` for `ρ ∈ [0,1]`.
Equivalent to `(1−√ρ)² ≥ 0` after expanding with `(√ρ)² = ρ`. -/
theorem half_capacity_le_johnson {ρ : ℝ} (h0 : 0 ≤ ρ) :
    (1 - ρ) / 2 ≤ 1 - Real.sqrt ρ := by
  have hs : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt h0
  nlinarith [sq_nonneg (Real.sqrt ρ - 1)]

/-- **The halving map exits the window in one step.**  For any rate `ρ ∈ [0,1]` and any
threshold `δ` strictly below capacity (`δ < 1−ρ`) — in particular for every `δ` in the
open window `(1−√ρ, 1−ρ)` — the halved threshold `δ/2` lies strictly below the Johnson
radius `1−√ρ`.  Hence the iteration `δ ↦ δ/2` never revisits the window, its unique
fixpoint is `0`, and no interior fixpoint-band structure exists. -/
theorem halving_exits_window {ρ δ : ℝ} (h0 : 0 ≤ ρ) (hδ : δ < 1 - ρ) :
    δ / 2 < 1 - Real.sqrt ρ :=
  lt_of_lt_of_le (by linarith) (half_capacity_le_johnson h0)

/-- Strict version inside the window: the first iterate is *strictly* below the window's
lower edge, so the orbit of a window point leaves the window permanently (halving only
decreases, and the window sits above `1−√ρ > δ/2 > δ/4 > …`). -/
theorem halving_orbit_never_returns {ρ δ : ℝ} (h0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ)
    (hδcap : δ < 1 - ρ) {m : ℕ} (hm : 1 ≤ m) : δ / 2 ^ m < 1 - Real.sqrt ρ := by
  have h1 : δ / 2 < 1 - Real.sqrt ρ := halving_exits_window h0 hδcap
  have hmono : δ / 2 ^ m ≤ δ / 2 := by
    have h2m : (2 : ℝ) ≤ 2 ^ m := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m := by
        apply pow_le_pow_right₀ (by norm_num) hm
    exact div_le_div_of_nonneg_left hδ0 (by norm_num) h2m
  exact lt_of_le_of_lt hmono h1

end ProximityGap.Issue357

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Issue357.halving_exits_window
#print axioms ProximityGap.Issue357.halving_orbit_never_returns
