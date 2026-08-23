/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TowerDescentNoSaving

/-!
# The full-depth antipodal-tower base rung is INFORMATIONLESS (#444 / #407)

`_TowerDescentNoSaving.towerDescent_saving_iff` proved the single-octave dichotomy: a thin-group
list saving on `mu_{2^mu}` is *equivalent* to a base-rung saving
`rootCount(Q, mu_{2^{mu-s}}) < natDegree Q`. `_TowerDescentTelescope` telescopes this across octaves
and states that the FULL descent `s = mu` "lands on the one-element base group `mu_{2^0} = mu_1 =
{1}`", localizing the off-BGK route's open content "to the list on this fixed finite object" -- but
it never computes what that base-rung condition becomes at the bottom.

This file lands the missing computation: at the full depth `s = mu` the base group is the SINGLETON
`mu_1 = {1}`, on which `rootCount(Q, {1}) <= 1` unconditionally, so the saving condition
`rootCount(Q, mu_1) < natDegree Q` is IMPLIED BY `natDegree Q >= 2` -- trivially, with NO list
information.

* `card_nthRootsFinset_one` : `(nthRootsFinset 1 (1 : F)).card = 1` (the base group is a singleton).
* `baseRung_rootCount_le_one` : `rootCount(Q, mu_1) <= 1` for any `Q` (a one-element evaluation set
  carries at most one root).
* `baseRung_saving_vacuous` : for `natDegree Q >= 2`, the base-rung saving condition
  `rootCount(Q, mu_1) < natDegree Q` holds UNCONDITIONALLY. The full-depth dichotomy's RHS is
  degenerate.
* `fullDepth_baseRung_vacuous` : at the full depth `s = mu` the base group is
  `mu_{2^{mu-mu}} = mu_1`, so the dichotomy's base-rung side
  `rootCount(Q, mu_{2^{mu-mu}}) < natDegree Q` is, for `natDegree Q >= 2`, the UNCONDITIONAL degree
  fact -- it equates the descent's bottom condition to no list information at all.

## The sharpening (why this matters)

`_TowerDescentTelescope` localizes the off-BGK route's residual to `mu_1`. This file shows `mu_1` is
INFORMATIONLESS: any "saving" the full-depth descent reports at the bottom is the degenerate degree
fact, not a real list saving. So the full descent OVER-AMPLIFIES -- it must STOP SHORT (`s < mu`) to
retain list content. The true open residual of the off-BGK route is therefore an INTERMEDIATE rung
`mu_{2^j}` with `j >= 1` (at least two evaluation points), not the singleton `mu_1`. This refines
the telescope's "lands on `mu_1`" into "`mu_1` is content-free; the real residual is the smallest
rung with `>= 2` evaluation points."

## Honest scope (rules 1, 3, 4, 6)

This is a **refinement of a refutation-with-mechanism** (rule 4 win): it sharpens the off-BGK
no-saving localization by proving the bottom rung carries no information, so the descent's residual
is NOT the singleton it nominally lands on. EXTENDS the in-tree `towerDescent_saving_iff` (no new
probe content beyond the singleton degeneracy, which is char-free polynomial/finset arithmetic). It
does NOT close CORE; NOT thinness-essential (the singleton degeneracy holds over any domain). The
general non-symmetric worst case (the open BGK core) is untouched. CORE
`M(mu_n) <= C * sqrt(n * log(p/n))` stays OPEN.

Probe `scripts/probes/probe_baserung_list.py`: the odd antipodal worst word `x^3 + x` descended
octave-by-octave on PROPER `mu_n` (complex `2^a`-th roots), rootcount `= 2` down to `mu_4`, then `0`
at `mu_2`/`mu_1`; confirms `rootCount(Q, mu_1) in {0,1}` so the saving condition is degree-implied.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issues #444, #407.
-/

open Polynomial

namespace ProximityGap.Frontier.TowerBaseRungDegenerate

variable {F : Type*} [Field F]

/-- **The full-depth base group is a singleton.** `mu_1 = nthRootsFinset 1 1 = {1}` has exactly one
element (over any domain, via `IsPrimitiveRoot.one`). -/
theorem card_nthRootsFinset_one : (nthRootsFinset 1 (1 : F)).card = 1 := by
  simpa using IsPrimitiveRoot.card_nthRootsFinset (IsPrimitiveRoot.one (M := F))

open Classical in
/-- **The base-rung root count is at most one.** On the one-element base group `mu_1` any polynomial
has at most one root -- the trivial bound is `1`, INDEPENDENT of `natDegree Q`. -/
theorem baseRung_rootCount_le_one (Q : F[X]) :
    ((nthRootsFinset 1 (1 : F)).filter (fun β => Q.IsRoot β)).card ≤ 1 := by
  calc ((nthRootsFinset 1 (1 : F)).filter (fun β => Q.IsRoot β)).card
      ≤ (nthRootsFinset 1 (1 : F)).card := Finset.card_filter_le _ _
    _ = 1 := card_nthRootsFinset_one

open Classical in
/-- **The base-rung saving condition is vacuous for degree `>= 2`.** The full-depth dichotomy's RHS
`rootCount(Q, mu_1) < natDegree Q` is IMPLIED unconditionally by `natDegree Q >= 2`: the LHS is
`<= 1` regardless of `Q`, so it carries NO list information. -/
theorem baseRung_saving_vacuous {Q : F[X]} (hQ : 2 ≤ Q.natDegree) :
    ((nthRootsFinset 1 (1 : F)).filter (fun β => Q.IsRoot β)).card < Q.natDegree := by
  calc ((nthRootsFinset 1 (1 : F)).filter (fun β => Q.IsRoot β)).card
      ≤ 1 := baseRung_rootCount_le_one Q
    _ < Q.natDegree := by omega

open Classical in
/-- **The full-depth descent's base condition is degree-content-free.** At `s = mu` the base group
is `mu_{2^{mu-mu}} = mu_{2^0} = mu_1 = {1}`. So the dichotomy's base-rung side
`rootCount(Q, mu_{2^{mu-mu}}) < natDegree Q` is, for `natDegree Q >= 2`, the UNCONDITIONAL degree
fact -- it equates the descent's bottom condition to no list information at all. This is why the
descent must stop short of `mu_1` to retain list content. -/
theorem fullDepth_baseRung_vacuous {μ : ℕ} {Q : F[X]} (hQ : 2 ≤ Q.natDegree) :
    ((nthRootsFinset (2 ^ (μ - μ)) (1 : F)).filter (fun β => Q.IsRoot β)).card < Q.natDegree := by
  simpa using baseRung_saving_vacuous (F := F) hQ

end ProximityGap.Frontier.TowerBaseRungDegenerate

#print axioms ProximityGap.Frontier.TowerBaseRungDegenerate.card_nthRootsFinset_one
#print axioms ProximityGap.Frontier.TowerBaseRungDegenerate.baseRung_rootCount_le_one
#print axioms ProximityGap.Frontier.TowerBaseRungDegenerate.baseRung_saving_vacuous
#print axioms ProximityGap.Frontier.TowerBaseRungDegenerate.fullDepth_baseRung_vacuous
