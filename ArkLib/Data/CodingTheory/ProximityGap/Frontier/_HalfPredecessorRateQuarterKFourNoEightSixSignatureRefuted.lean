/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Rate-quarter `k = 4`: the source-six cardinal signature cap is false

In the saturated source-six stratum, every outsider has a root triple in the
six-coordinate source core and a missed four-set in the ten-coordinate
complement.  The global core cap seven gives the pair condition

```text
  3 + |T_i inter T_j| <= |E_i union E_j|.
```

This condition alone does not bound the outsider population by thirteen.
Take two disjoint root triples.  Over each root triple, use the twelve lines
of the affine plane of order three, with one common tenth point adjoined to
every line.  Within a copy, two missed four-sets meet in at most two points;
between copies, the root triples are disjoint.  Thus all 24 signatures obey
the pair condition.

This is an exact finite countermodel to a cardinal-only closure, not a
Reed--Solomon realization.  In particular, it deliberately omits the cubic
locator/affine-row equation proved in the source-root support module.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSixSignatureRefuted

/-- The abstract cardinal statement suggested by the saturated source-six
root/missed-set split and the global core cap seven. -/
def AbstractNoEightSixSignatureCap : Prop :=
  forall (J : Type) [Fintype J] [DecidableEq J]
      (root : J -> Finset (Fin 6)) (missed : J -> Finset (Fin 10)),
    (forall j, (root j).card = 3) ->
    (forall j, (missed j).card = 4) ->
    (forall i j, i ≠ j ->
      3 + ((root i) ∩ (root j)).card <= ((missed i) ∪ (missed j)).card) ->
    Fintype.card J <= 13

/-- The twelve affine-plane lines on the first nine points, each enlarged by
the common tenth point. -/
def affinePlaneFourSet : Fin 12 -> Finset (Fin 10) := ![
  {0, 3, 6, 9}, {1, 4, 7, 9}, {2, 5, 8, 9},
  {0, 1, 2, 9}, {3, 4, 5, 9}, {6, 7, 8, 9},
  {0, 4, 8, 9}, {1, 5, 6, 9}, {2, 3, 7, 9},
  {0, 5, 7, 9}, {1, 3, 8, 9}, {2, 4, 6, 9}
]

/-- Two disjoint source-root triples, one for each twelve-signature copy. -/
def rootSignature (i : Fin 24) : Finset (Fin 6) :=
  if i.1 < 12 then {0, 1, 2} else {3, 4, 5}

/-- Both copies use the same catalogue of missed four-sets. -/
def missedSignature (i : Fin 24) : Finset (Fin 10) :=
  affinePlaneFourSet ⟨i.1 % 12, Nat.mod_lt _ (by norm_num)⟩

theorem rootSignature_card : forall i, (rootSignature i).card = 3 := by
  decide

theorem missedSignature_card : forall i, (missedSignature i).card = 4 := by
  decide

/-- All 24 signatures satisfy the exact pair inequality inherited from the
global core cap seven. -/
theorem signature_pair_condition : forall i j, i ≠ j ->
    3 + ((rootSignature i) ∩ (rootSignature j)).card <=
      ((missedSignature i) ∪ (missedSignature j)).card := by
  decide

/-- **Countermodel.**  The abstract source-six signature cap thirteen is
false. -/
theorem abstractNoEightSixSignatureCap_REFUTED :
    Not AbstractNoEightSixSignatureCap := by
  intro hcap
  have hle := hcap (Fin 24) rootSignature missedSignature
    rootSignature_card missedSignature_card signature_pair_condition
  norm_num at hle

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSixSignatureRefuted

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSixSignatureRefuted
#print axioms rootSignature_card
#print axioms missedSignature_card
#print axioms signature_pair_condition
#print axioms abstractNoEightSixSignatureCap_REFUTED
