/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Source-six signatures: the three-balanced-witness pigeonhole is false

The size-six branch of the no-eight residual
(`_HalfPredecessorRateQuarterKFourNoEightSixRootSupport.lean`,
`_HalfPredecessorRateQuarterKFourNoEightSixLongStratum.lean`) forces at
least fourteen source outsiders.  Saturated outsiders carry a root triple
`T` in the six-coordinate source core and a missed four-set `E` in the
ten-coordinate complement, subject to the proven all-outsider pair law

```text
  3 + |T_i inter T_j| <= |E_i union E_j|
```

(`three_add_root_inter_le_sourceMissed_union_of_noEight_source_six`).  A
ternary balance `|E_i u E_j u E_k| <= 6 + |T_i n T_j n T_k|` forces the
three polynomial points onto one relevant line
(`third_outside_mem_pointsOn_secant_of_sourceSix_root_missed_balance`), and
three balanced witnesses on one pair give five collinear points, which is
impossible (`false_of_five_sourceSix_outsiders_root_missed_balance`).

This file shows the pigeonhole cannot fire: fourteen saturated signatures
can satisfy the pair law while every pair carries at most **two** balanced
witnesses.  The model was found by exact constraint search
(`scripts/probes/probe_w6_kfour_sourcesix_cpsat.py`).  Together with the
source-seven countermodel in `_W6KFourClosureSharpWitnessRefuted.lean`,
this closes off cardinal balanced-witness counting as a route to either
branch of the no-eight residual.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open Finset

namespace ArkLib.ProximityGap.Frontier.W6KFourClosureSourceSixWitnessRefuted

/-- The source-root triples of the source-six countermodel, inside the
six-coordinate source core. -/
def rootSignature : Fin 14 -> Finset (Fin 6) := ![
  {0, 1, 2}, {0, 4, 5}, {1, 3, 4}, {1, 2, 5}, {0, 4, 5},
  {1, 3, 5}, {3, 4, 5}, {1, 2, 5}, {0, 2, 3}, {2, 3, 4},
  {1, 3, 5}, {0, 2, 5}, {0, 1, 4}, {1, 2, 4}
]

/-- The missed four-sets of the same model, inside the ten-coordinate
source complement. -/
def missedSignature : Fin 14 -> Finset (Fin 10) := ![
  {0, 1, 2, 3}, {0, 3, 4, 5}, {2, 3, 4, 5}, {0, 1, 4, 6}, {1, 2, 6, 8},
  {3, 5, 6, 8}, {1, 3, 7, 8}, {2, 4, 7, 8}, {4, 5, 6, 9}, {0, 1, 7, 9},
  {0, 3, 7, 9}, {2, 5, 7, 9}, {4, 6, 7, 9}, {1, 5, 8, 9}
]

/-- The source-six ternary balance predicate which forces polynomial
collinearity. -/
def BalancedTriple
    {J : Type}
    (root : J -> Finset (Fin 6)) (missed : J -> Finset (Fin 10))
    (a b c : J) : Bool :=
  decide (4 + (((missed a ∪ missed b) ∪ missed c).card) <=
    10 + (((root a ∩ root b) ∩ root c).card))

/-- Balanced third signatures on the pair `(a,b)`. -/
def balancedWitnesses
    {J : Type} [Fintype J] [DecidableEq J]
    (root : J -> Finset (Fin 6)) (missed : J -> Finset (Fin 10))
    (a b : J) : Finset J :=
  Finset.univ.filter fun c => decide
    (c ≠ a ∧ c ≠ b ∧ BalancedTriple root missed a b c = true)

/-- The finite hypotheses of the saturated source-six stratum. -/
def SaturatedSignatureConstraints
    {J : Type} [Fintype J] [DecidableEq J]
    (root : J -> Finset (Fin 6)) (missed : J -> Finset (Fin 10)) : Prop :=
  (forall j, (root j).card = 3) ∧
  (forall j, (missed j).card = 4) ∧
  (forall i j, i ≠ j ->
    3 + ((root i) ∩ (root j)).card <= ((missed i) ∪ (missed j)).card)

/-- **The source-six pigeonhole assertion**: fourteen saturated signatures
force three balanced witnesses on some pair (hence five collinear points
and the packing contradiction). -/
def FourteenSaturatedSignaturesForceThreeBalancedWitnesses : Prop :=
  forall (root : Fin 14 -> Finset (Fin 6))
      (missed : Fin 14 -> Finset (Fin 10)),
    SaturatedSignatureConstraints root missed ->
    exists a b : Fin 14, a ≠ b ∧
      3 <= (balancedWitnesses root missed a b).card

theorem rootSignature_card : forall i, (rootSignature i).card = 3 := by
  decide

theorem missedSignature_card : forall i, (missedSignature i).card = 4 := by
  decide

theorem signature_pair_law : forall i j, i ≠ j ->
    3 + ((rootSignature i) ∩ (rootSignature j)).card <=
      ((missedSignature i) ∪ (missedSignature j)).card := by
  decide

theorem model_constraints :
    SaturatedSignatureConstraints rootSignature missedSignature :=
  ⟨rootSignature_card, missedSignature_card, signature_pair_law⟩

/-- Every pair in the source-six countermodel has at most **two** balanced
witnesses. -/
theorem balancedWitnesses_card_le_two : forall a b : Fin 14,
    a ≠ b ->
      (balancedWitnesses rootSignature missedSignature a b).card <= 2 := by
  decide

/-- **Countermodel.**  Fourteen saturated source-six signatures satisfying
the pair law need not put three balanced witnesses on any pair.  The
five-point relevant-line contradiction is unreachable from the saturated
cardinal hypotheses alone in the source-six branch as well. -/
theorem fourteenSaturatedSignaturesForceThreeBalancedWitnesses_REFUTED :
    Not FourteenSaturatedSignaturesForceThreeBalancedWitnesses := by
  intro hforce
  obtain ⟨a, b, hab, hthree⟩ :=
    hforce rootSignature missedSignature model_constraints
  have htwo := balancedWitnesses_card_le_two a b hab
  omega

end ArkLib.ProximityGap.Frontier.W6KFourClosureSourceSixWitnessRefuted

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.W6KFourClosureSourceSixWitnessRefuted
#print axioms signature_pair_law
#print axioms balancedWitnesses_card_le_two
#print axioms fourteenSaturatedSignaturesForceThreeBalancedWitnesses_REFUTED
