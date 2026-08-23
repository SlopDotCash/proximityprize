/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TowerBaseRungDegenerate

/-!
# The off-BGK antipodal-tower residual floor is `mu_2`, not `mu_1` (#444 / #407)

`_TowerBaseRungDegenerate` proved the full-depth (`s = mu`) descent lands on the singleton
`mu_1 = {1}`, where the saving condition `rootCount(Q, mu_1) < natDegree Q` is INFORMATIONLESS
(implied by `natDegree Q >= 2` unconditionally). It concluded that the off-BGK route must STOP SHORT
of `mu_1` and that its true residual is the smallest rung with `>= 2` evaluation points.

This file lands that rung: it is `mu_2 = {1, -1}` (over any field of characteristic `!= 2`, i.e. the
prize regime where `p` is a large odd prime). UNLIKE `mu_1`, the `mu_2` saving condition is GENUINE
(`Q`-dependent, NOT degree-forced): there is a base polynomial whose root count on `mu_2` SATURATES
the trivial bound, so a degree-`2` base can fail to save.

* `card_nthRootsFinset_two` : `(nthRootsFinset 2 (1 : F)).card = 2` for `CharP F p`, `p != 2` (the
  base group `mu_2 = {1, -1}` has exactly two elements).
* `baseRung_two_rootCount_le_two` : `rootCount(Q, mu_2) <= 2` for any `Q` (two-element evaluation
  set).
* `baseRung_two_saturated` : the witness `X^2 - 1` has root count `EXACTLY 2` on `mu_2` -- it
  saturates the trivial bound. Since `natDegree (X^2 - 1) = 2`, this is `rootCount = natDegree`: NO
  saving, and it is NOT degree-forced (a different degree-`2` base, e.g. `X^2 + 1`, would save). So
  the `mu_2` saving condition carries REAL list information, the exact contrast with `mu_1`.

## The completed dichotomy (the point of the two bricks)

* At `mu_1` (full depth `s = mu`): `rootCount <= 1`, so `< natDegree Q` for ALL `natDegree Q >= 2`
  -- the saving condition is VACUOUS (`_TowerBaseRungDegenerate.baseRung_saving_vacuous`).
* At `mu_2` (depth `s = mu - 1`): `rootCount <= 2` and the bound is ATTAINED by `X^2 - 1`
  (`baseRung_two_saturated`) -- the saving condition is GENUINE, `Q`-dependent, not degree-forced.

So `mu_2` is precisely the residual FLOOR of the off-BGK route: the first base rung where the
descent's saving condition stops being a content-free degree fact and becomes a real (finite,
`p`-independent) decision about the base agreement polynomial's root pattern on the fixed
`2`-element cyclotomic group `{1, -1}`. This pins the off-BGK route's open residual to a concrete,
`n`-independent, `p`-independent object.

## Honest scope (rules 1, 3, 4, 6)

A refinement EXTENDING `_TowerBaseRungDegenerate`: it identifies the genuine residual rung and
proves the saving bound there is attainable (so the residual is non-degenerate, unlike `mu_1`).
NON-moment,
char-free combinatorics about a fixed `2`-element group; `mu_2 = {1, -1}` is `n`-independent and
`p`-independent. NOT a CORE closure; NOT thinness-essential. The actual base-rung list UPPER bound
on `mu_2` (i.e. whether the off-BGK route's residual list is small) remains the open content -- this
file only pins WHERE that residual lives and proves it is non-degenerate. CORE
`M(mu_n) <= C * sqrt(n * log(p/n))` stays OPEN.

Probe `scripts/probes/probe_mu2_residual.py`: on `mu_2 = {1, -1}`, `X^2 - 1` saturates
(`rootCount = 2 = natDegree`, no saving) while `X^2 + 1` / `X^2 - 4` give saving
(`rootCount = 0 < 2`) -- the `mu_2` condition is `Q`-dependent, confirming it is the genuine
information-carrying residual floor.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issues #444, #407.
-/

open Polynomial

namespace ProximityGap.Frontier.TowerResidualFloorMuTwo

variable {F : Type*} [Field F]

/-- **The first non-degenerate base group has two elements.** Over a field of characteristic `!= 2`
(the prize regime, `p` a large odd prime) the base group `mu_2 = nthRootsFinset 2 1 = {1, -1}` has
exactly two elements (via `IsPrimitiveRoot.neg_one`). -/
theorem card_nthRootsFinset_two {p : ℕ} [CharP F p] (hp : p ≠ 2) :
    (nthRootsFinset 2 (1 : F)).card = 2 := by
  simpa using IsPrimitiveRoot.card_nthRootsFinset (IsPrimitiveRoot.neg_one (R := F) p hp)

open Classical in
/-- **The base-rung-`2` root count is at most two.** On the two-element base group `mu_2` any
polynomial has at most two roots -- the trivial bound is `2`. -/
theorem baseRung_two_rootCount_le_two {p : ℕ} [CharP F p] (hp : p ≠ 2) (Q : F[X]) :
    ((nthRootsFinset 2 (1 : F)).filter (fun β => Q.IsRoot β)).card ≤ 2 := by
  calc ((nthRootsFinset 2 (1 : F)).filter (fun β => Q.IsRoot β)).card
      ≤ (nthRootsFinset 2 (1 : F)).card := Finset.card_filter_le _ _
    _ = 2 := card_nthRootsFinset_two hp

open Classical in
/-- **The base-rung-`2` bound is SATURATED (so the saving condition is genuine).** The witness
`X^2 - 1` has root count EXACTLY `2` on `mu_2 = {1, -1}` (both elements are roots). Since
`natDegree (X^2 - 1) = 2`, this is `rootCount = natDegree`: NO saving, and -- unlike `mu_1` where
the count `<= 1` forced saving for every `natDegree >= 2` -- the `mu_2` condition is NOT
degree-forced
(a different degree-`2` base, e.g. `X^2 + 1`, saves). So `mu_2` carries real list information: it is
the genuine residual floor of the off-BGK route. -/
theorem baseRung_two_saturated {p : ℕ} [CharP F p] (hp : p ≠ 2) :
    ((nthRootsFinset 2 (1 : F)).filter (fun β => (X ^ 2 - 1 : F[X]).IsRoot β)).card = 2 := by
  have hall : (nthRootsFinset 2 (1 : F)).filter (fun β => (X ^ 2 - 1 : F[X]).IsRoot β)
      = nthRootsFinset 2 (1 : F) := by
    apply Finset.filter_true_of_mem
    intro β hβ
    rw [mem_nthRootsFinset (by norm_num)] at hβ
    simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_one]
    rw [hβ]; ring
  rw [hall]
  exact card_nthRootsFinset_two hp

end ProximityGap.Frontier.TowerResidualFloorMuTwo

#print axioms ProximityGap.Frontier.TowerResidualFloorMuTwo.card_nthRootsFinset_two
#print axioms ProximityGap.Frontier.TowerResidualFloorMuTwo.baseRung_two_rootCount_le_two
#print axioms ProximityGap.Frontier.TowerResidualFloorMuTwo.baseRung_two_saturated
