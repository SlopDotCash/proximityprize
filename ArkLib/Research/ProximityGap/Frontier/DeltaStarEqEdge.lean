/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# The exact δ* pin from its two directions — floor + ceiling (#407)

This file completes the **logical skeleton** of the "existence-form floor closes the prize" argument
(#407 comment 4701290960): it proves the clean exact-pin characterization the ledger was missing —

> **`mcaDeltaStar_eq_of_good_above_bad`** — if a radius `edge ≤ 1` is **good**
> (`epsMCA C edge ≤ ε*`, the FLOOR) and **every** radius strictly above it is **bad**
> (`ε* < epsMCA C δ` for `δ > edge`, the CEILING), then `δ*(C, ε*) = edge` exactly.

This makes machine-precise that pinning `δ*` decomposes into exactly two obligations:

* **CEILING** (`habove`) — provided in the prize regime by the Kambiré bad-line family
  (`KKH26BadLineConstruction` / `kkh26_mcaDeltaStar_le_of_TZ`): correlated agreement provably
  *fails* above the window edge.  This direction is **proven** (it needs only the existence of one
  bad family at one good prime — the same existence the ceiling already uses).

* **FLOOR** (`hgood`) — that the edge radius is good, i.e. the worst-case bad-scalar count at the
  edge stays within budget `ε*`.  At a prime avoiding the spurious `e₂ = 0` resultants (a good prime,
  whose existence is the elementary pigeonhole `kkh26_good_prime_of_TZ`: the finitely many bad
  resultants, each of bounded height `≤ (n²+n)^{n/2}` by `e2_extra_solution_threshold`, are vastly
  outnumbered by the window primes), the bad count collapses to the char-`0` value.  The **sole**
  remaining content is that this `e₂`-locus is the *binding* worst-case family at the edge — a
  combinatorial extremality statement (#407 residual R1), **independent of the BGK / deep-moment
  wall** (no √-cancellation, no high moments).

So this theorem is the honest assembly point: the proven ceiling + the (off-wall, combinatorial)
floor hypothesis ⟹ the exact pin, with the open content named explicitly as `hgood`.  No `sorry`,
no fabricated axiom; **axiom-clean** (`propext, Classical.choice, Quot.sound`).
-/

open scoped NNReal ENNReal

namespace ProximityGap.MCAThresholdLedger

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- **Exact δ* pin from floor + ceiling.**  If `edge ≤ 1` is a good radius (the FLOOR
`epsMCA C edge ≤ ε*`) and every radius strictly above `edge` is bad (the CEILING), then
`mcaDeltaStar C ε* = edge`.  The two hypotheses are exactly the two directions of the prize:
the ceiling is the proven Kambiré/`kkh26` bad-family existence; the floor is the off-wall
(combinatorial, non-BGK) good-prime statement. -/
theorem mcaDeltaStar_eq_of_good_above_bad (C : Set (ι → A)) (εstar : ℝ≥0∞) {edge : ℝ≥0}
    (hedge : edge ≤ 1)
    (hgood : epsMCA (F := F) (A := A) C edge ≤ εstar)
    (habove : ∀ δ : ℝ≥0, edge < δ → εstar < epsMCA (F := F) (A := A) C δ) :
    mcaDeltaStar (F := F) (A := A) C εstar = edge := by
  refine le_antisymm ?_ (le_mcaDeltaStar_of_good (F := F) (A := A) C εstar hedge hgood)
  -- every good radius lies ≤ edge: a radius above edge is bad, contradicting goodness
  refine csSup_le' (show edge ∈ upperBounds (mcaGoodRadii (F := F) (A := A) C εstar) from ?_)
  intro δ hδ
  by_contra hlt
  rw [not_le] at hlt
  exact absurd hδ.2 (not_le.mpr (habove δ hlt))

end ProximityGap.MCAThresholdLedger
