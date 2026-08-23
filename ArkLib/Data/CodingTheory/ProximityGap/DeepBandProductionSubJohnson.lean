/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubJohnsonListDischarge

/-!
# The production band is strictly sub-Johnson (#389: the open gate is unavoidable)

The in-tree above-Johnson discharge `subJohnsonListBound_aboveJohnson`
(`SubJohnsonListDischarge.lean`) proves the open core of #389 **whenever its
hypothesis** `hJohnson : n·(k−1) < (k+m+1)²` holds — i.e. when the band threshold
`k+m+1` sits at/above the Johnson radius `√(n·(k−1))`.  Its docstring records that
the genuinely-open part is therefore *strictly sub-Johnson* (`(k+m+1)² ≤ n·(k−1)`),
but the project only argued *in prose* that the deployed (production) parameters
land there.  This file turns that prose into a machine-checked statement: it pins
exactly where the wall bites.

What is proven here (pure arithmetic, axiom-clean):

* `subJohnson_iff_sqrt` — the sub-Johnson criterion in closed `Nat.sqrt` form:
  `(k+m+1)² ≤ n·(k−1) ↔ k+m+1 ≤ Nat.sqrt (n·(k−1))`.
* `johnson_dichotomy` — every band is *either* above-Johnson (discharged in-tree)
  *or* strictly sub-Johnson (the open core); the two are exclusive
  (`aboveJohnson_hyp_false_of_subJohnson`).
* `firstBand_subJohnson` — the first deep band (`m = 0`) at rate `≤ 1/2`
  (`5 ≤ k`, `2k ≤ n`) is strictly sub-Johnson.
* `firstBand_aboveJohnson_vacuous` — *the punchline*: at those parameters the
  hypothesis of `subJohnsonListBound_aboveJohnson` is **false**, so the in-tree
  above-Johnson route provably cannot discharge the core; #389 there reduces to
  the strictly sub-Johnson list bound (the recognized 25-year
  explicit-RS-beyond-Johnson problem).  A concrete production instance
  `(n,k,m) = (2²⁰, 2¹⁸, 0)` (rate `1/4`) is exhibited.

This pins the boundary precisely: it does **not** close the open core (the
sub-Johnson list bound is a recognized open problem; no closure is fabricated) — it
proves the in-tree above-Johnson discharge is provably inapplicable in the deployed
regime, so that one remaining obligation is genuinely unavoidable there.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

namespace ProximityGap.Ownership

/-- **The sub-Johnson criterion in closed form.**  The band threshold `k+m+1` is
at/below the Johnson radius `√(n·(k−1))` iff `(k+m+1)² ≤ n·(k−1)`.  This is the
exact boundary separating the in-tree above-Johnson discharge from the open core. -/
theorem subJohnson_iff_sqrt (n k m : ℕ) :
    (k + m + 1) ^ 2 ≤ n * (k - 1) ↔ k + m + 1 ≤ Nat.sqrt (n * (k - 1)) :=
  Nat.le_sqrt'.symm

/-- **The Johnson dichotomy.**  Every deep band is either *above* the Johnson radius
(`n·(k−1) < (k+m+1)²`, where the in-tree second-moment discharge applies) or
*strictly sub-Johnson* (`(k+m+1)² ≤ n·(k−1)`, the open core of #389). -/
theorem johnson_dichotomy (n k m : ℕ) :
    n * (k - 1) < (k + m + 1) ^ 2 ∨ (k + m + 1) ^ 2 ≤ n * (k - 1) :=
  Nat.lt_or_ge _ _

/-- **The two sides are exclusive.**  In the strictly sub-Johnson band the
hypothesis required by `subJohnsonListBound_aboveJohnson` is false. -/
theorem aboveJohnson_hyp_false_of_subJohnson {n k m : ℕ}
    (hsub : (k + m + 1) ^ 2 ≤ n * (k - 1)) :
    ¬ n * (k - 1) < (k + m + 1) ^ 2 :=
  Nat.not_lt.mpr hsub

/-- **The first deep band (`m = 0`) at rate `≤ 1/2` is strictly sub-Johnson.**
For `5 ≤ k` and `2k ≤ n` (rate `ρ = k/n ≤ 1/2`), the threshold `k+1` lies strictly
below the Johnson radius: `(k+1)² ≤ n·(k−1)`.  Proof: `(k+1)² ≤ 2k(k−1) ≤ n(k−1)`. -/
theorem firstBand_subJohnson {n k : ℕ} (hk : 5 ≤ k) (hn : 2 * k ≤ n) :
    (k + 0 + 1) ^ 2 ≤ n * (k - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  have hd : 4 ≤ d := by omega
  have hnd : 2 * d + 2 ≤ n := by omega
  have hk1 : d + 1 - 1 = d := by omega
  rw [hk1]
  have key : (d + 1 + 0 + 1) ^ 2 ≤ (2 * d + 2) * d := by nlinarith [hd]
  calc (d + 1 + 0 + 1) ^ 2 ≤ (2 * d + 2) * d := key
    _ ≤ n * d := by gcongr

/-- **The punchline: the above-Johnson discharge is vacuous in the production band.**
For the first deep band (`m = 0`) at rate `≤ 1/2`, the hypothesis of the in-tree
`subJohnsonListBound_aboveJohnson` is **false**.  Hence the above-Johnson
second-moment route provably cannot discharge the open core of #389 in the deployed
regime; the count there genuinely reduces to the strictly sub-Johnson list bound
(the recognized open problem).  No closure is fabricated — this pins the gate. -/
theorem firstBand_aboveJohnson_vacuous {n k : ℕ} (hk : 5 ≤ k) (hn : 2 * k ≤ n) :
    ¬ n * (k - 1) < (k + 0 + 1) ^ 2 := by
  have h := firstBand_subJohnson hk hn
  exact aboveJohnson_hyp_false_of_subJohnson (n := n) (k := k) (m := 0) h

/-- Concrete production instance `(n, k, m) = (2²⁰, 2¹⁸, 0)` (rate `1/4`): the
in-tree above-Johnson discharge cannot be invoked — its Johnson hypothesis is
false, so #389's open sub-Johnson list bound is the only remaining gate here. -/
example : ¬ (1048576 : ℕ) * (262144 - 1) < (262144 + 0 + 1) ^ 2 :=
  firstBand_aboveJohnson_vacuous (by norm_num) (by norm_num)

end ProximityGap.Ownership
