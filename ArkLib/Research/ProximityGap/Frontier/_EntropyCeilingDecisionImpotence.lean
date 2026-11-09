/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Basic

/-!
# The entropy ceiling is decision-IMPOTENT for the plateau dichotomy (#444, finding #2)

This file discharges @lalalune's growth-law **finding #2** ("the one open question, attacked
from 8 angles", #444, 2026-06-16 04:57Z) into an axiom-clean theorem. The finding was recorded
as *adversarially verified but never a theorem*:

> **entropy-ceiling** | decider? | **provably CANNOT decide** -- ceiling bounds `m*` from
> *below*; deciding needs an *upper* bound (logically independent). Confirmed clean negative.

## The setup

The proven entropy ceiling (`PrizeEntropyDeltaStar.prizeDeltaStar_ceiling`) is an
**unconditional upper bound on `delta*`**: `delta* <= prizeDeltaStar`. Since a larger binding
plateau depth `m*` means a *smaller* proximity radius `delta*`, an upper bound on `delta*`
is exactly a **lower bound on `m*`** -- a FLOOR `a <= m*` (direction: BELOW).

The plateau dichotomy that decides the prize is the additive-vs-multiplicative question:
is `m*` bounded ABOVE by an `O(log n)` additive horn (`m* <= g`, prize HOLDS), or does it grow
to the linear multiplicative horn (`m* > g`, prize FAILS)? Deciding the **additive** horn
requires an UPPER bound on `m*` -- a CEILING (direction: ABOVE).

## The theorem (a clean structural NEGATIVE / constraint lemma)

A floor `a <= m*` and a ceiling `m* <= g` are **logically independent**: from `a <= m*` alone
one can derive neither `m* <= g` nor `g < m*`. We prove this in the strongest honest form --
the predicate `(a <= ·)` is realised by witnesses on *both* sides of every threshold `g >= a`
(`a` itself is `<= g`; `g + 1` is `> g`), so it *cannot* imply either side.

Consequence: the proven ceiling-side floor on `m*` is **the wrong inequality direction** to
settle the additive horn. The one already-proven tool that might have decided the dichotomy
provably cannot, confirming finding #2.

## Scope / honesty

This is a **constraint lemma** (the honesty contract, rule 4): it forbids using the
ceiling-side floor to decide the dichotomy. It does NOT decide the dichotomy (that is the
plateau-rate question = BCHKS Conj 1.12 = the BGK/Paley wall, OPEN), does NOT bound `m*` from
above, and makes NO capacity / beyond-Johnson / sub-linear / growth-law claim (the cliff-at-
`n/2` is untouched). The statements are field-universal order arithmetic over `Nat`; thinness
enters only via *which* `m*` the 2-power tower binds. The probe
`scripts/probes/probe_entropy_ceiling_decision_impotence.py` validates the independence on the
prize tower (the tree's own `cStarFull` from rho4.out, never `n = q - 1`) with 0 fails.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `axiom`.
-/

namespace ProximityGap.Frontier.EntropyCeilingDecisionImpotence

/-- A floor witness below a threshold: if `a <= g` then `a` itself satisfies the floor
`a <= a` and lies at-or-below the ceiling `a <= g`. This is the additive-consistent witness
(a value clearing the proven floor while obeying the additive horn). -/
theorem floor_witness_below {a g : ℕ} (hag : a ≤ g) : a ≤ a ∧ a ≤ g :=
  ⟨le_refl a, hag⟩

/-- A floor witness above a threshold: `g + 1` satisfies the floor `a <= g + 1` (since
`a <= g < g + 1`) yet strictly exceeds the ceiling `g < g + 1`. This is the
multiplicative-consistent witness (a value clearing the proven floor while violating the
additive horn). -/
theorem floor_witness_above {a g : ℕ} (hag : a ≤ g) : a ≤ g + 1 ∧ g < g + 1 :=
  ⟨le_trans hag (Nat.le_succ g), Nat.lt_succ_self g⟩

/-- **The floor does not imply the additive ceiling.** Knowing only the floor `a <= ·`, the
additive horn `· <= g` cannot be derived: the value `g + 1` clears the floor (`a <= g + 1`)
yet violates the ceiling (`g + 1 <= g` is false). Hence `(a <= ·) -> (· <= g)` is NOT valid
for any threshold `g >= a`. -/
theorem floor_not_imp_ceiling {a g : ℕ} (hag : a ≤ g) :
    ∃ v : ℕ, a ≤ v ∧ ¬ v ≤ g := by
  refine ⟨g + 1, le_trans hag (Nat.le_succ g), ?_⟩
  exact Nat.not_le.mpr (Nat.lt_succ_self g)

/-- **The floor does not imply the multiplicative horn either.** Symmetrically, knowing only
the floor `a <= ·`, the multiplicative reading `g < ·` cannot be derived: the value `g`
clears the floor (`a <= g`) yet does not exceed `g` (`g < g` is false). Hence `(a <= ·) ->
(g < ·)` is NOT valid. -/
theorem floor_not_imp_strict_gt {a g : ℕ} (hag : a ≤ g) :
    ∃ v : ℕ, a ≤ v ∧ ¬ g < v := by
  exact ⟨g, hag, Nat.not_lt.mpr (le_refl g)⟩

/-- **The floor straddles every threshold (the independence engine).** For every threshold
`g >= a` there exist two values both clearing the floor `a <= ·`, one at-or-below `g`
(additive) and one strictly above `g` (multiplicative). The floor therefore cannot separate
the two horns. -/
theorem floor_straddles {a g : ℕ} (hag : a ≤ g) :
    ∃ vlo vhi : ℕ, (a ≤ vlo ∧ vlo ≤ g) ∧ (a ≤ vhi ∧ g < vhi) :=
  ⟨a, g + 1, ⟨le_refl a, hag⟩, ⟨le_trans hag (Nat.le_succ g), Nat.lt_succ_self g⟩⟩

/-- **HEADLINE: the ceiling-side floor is decision-impotent for the additive horn.** Package
the negative: a proven floor `a <= m*` on the binding plateau depth supplies NEITHER the
additive horn `m* <= g` NOR the multiplicative horn `g < m*` for any threshold `g >= a`. Both
implications fail (witnessed by `g + 1` and `g` respectively), so the entropy ceiling -- which
gives only this floor -- cannot decide the dichotomy. This is the wrong inequality direction
(lalalune finding #2). -/
theorem ceiling_floor_cannot_decide {a g : ℕ} (hag : a ≤ g) :
    (∃ v : ℕ, a ≤ v ∧ ¬ v ≤ g) ∧ (∃ v : ℕ, a ≤ v ∧ ¬ g < v) :=
  ⟨floor_not_imp_ceiling hag, floor_not_imp_strict_gt hag⟩

/-- **The general logical form** (any floor predicate vs any threshold predicate). For ANY
floor value `a` and ANY threshold `g >= a`, the predicate `P := (a <= ·)` is satisfied by a
value violating `Q := (· <= g)` AND by a value satisfying `Q`. So `P` neither implies `Q` nor
implies `¬ Q`: a floor is logically independent of a ceiling. This is the abstract obstruction
underlying the entropy-ceiling impotence. -/
theorem floor_predicate_independent_of_ceiling {a g : ℕ} (hag : a ≤ g) :
    (∃ v : ℕ, (a ≤ v) ∧ ¬ (v ≤ g)) ∧ (∃ v : ℕ, (a ≤ v) ∧ (v ≤ g)) :=
  ⟨floor_not_imp_ceiling hag, ⟨a, le_refl a, hag⟩⟩

/-- **Tower instance (non-vacuity, the prize 2-power tower).** At the binding tower level
`n = 32` the tree's authoritative measured plateau depth is `m* = 5` (`cStarFull 32`, rho4.out,
thin `mu_n`, never `n = q - 1`). With the proven unconditional floor `a = 1` and the additive
threshold `g = 10 = 2 log2 32`, the floor straddles `g`: the value `1` clears the floor and is
`<= 10` (additive), while `11` clears the floor and is `> 10` (multiplicative). The measured
`m* = 5` itself clears the floor and sits below the additive threshold, but the floor alone
cannot certify that -- exactly the impotence. -/
theorem tower_instance_n32 :
    (∃ vlo vhi : ℕ, (1 ≤ vlo ∧ vlo ≤ 10) ∧ (1 ≤ vhi ∧ 10 < vhi)) ∧ (1 ≤ 5 ∧ 5 ≤ 10) := by
  refine ⟨floor_straddles (by decide : (1 : ℕ) ≤ 10), ?_⟩
  exact ⟨by decide, by decide⟩

end ProximityGap.Frontier.EntropyCeilingDecisionImpotence

open ProximityGap.Frontier.EntropyCeilingDecisionImpotence in
#print axioms ceiling_floor_cannot_decide
open ProximityGap.Frontier.EntropyCeilingDecisionImpotence in
#print axioms floor_predicate_independent_of_ceiling
open ProximityGap.Frontier.EntropyCeilingDecisionImpotence in
#print axioms tower_instance_n32
open ProximityGap.Frontier.EntropyCeilingDecisionImpotence in
#print axioms floor_straddles
