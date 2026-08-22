/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Source-seven signatures: the sharp three-balanced-witness assertion is false

`_HalfPredecessorRateQuarterKFourNoEightSevenMultiplicityRefuted.lean` refuted
the four-balanced-witness strengthening for thirteen regular signatures and
recorded the remaining "sharp assertion" as still-conjectural: that thirteen
regular signatures satisfying the pair law and the fixed-root fiber cap must
place *three* balanced witnesses on some pair.  Three witnesses would give
five collinear points on one relevant line, hence a core of size at least
eight at the length-sixteen, threshold-nine endpoint, closing the
regular-saturated no-eight branch.

This file refutes that sharp assertion.  The explicit thirteen-signature
model below satisfies the pair law

```text
  2 + |T_i inter T_j| <= |E_i union E_j|,
```

and uses thirteen pairwise-distinct root triples (fiber multiplicity one,
far below the cap three), yet every pair carries at most **two** balanced
witnesses.  Consequently no counting argument based only on the pair law,
the fiber cap, and the ternary balance predicate can force the five-point
line: the balanced-witness funnel stops at four collinear points, which the
global core cap seven still tolerates.

The model was found by exact constraint search
(`scripts/probes/probe_w6_kfour_witness_cpsat.py`); the same search proves
that thirteen such signatures always carry at least one balanced triple, so
the surviving route must exploit the geometry of the forced four-point
lines (or the long stratum), not balanced-triple cardinality alone.

Definitions are copied verbatim from
`_HalfPredecessorRateQuarterKFourNoEightSevenMultiplicityRefuted.lean`
(no compiled interface is available for that module at the time of writing;
the copies are definitionally identical for later reconciliation).
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open Finset

namespace ArkLib.ProximityGap.Frontier.W6KFourClosureSharpWitnessRefuted

/-- The source-root triples of the countermodel.  All thirteen are pairwise
distinct, so every root fiber has multiplicity one. -/
def rootSignature : Fin 13 -> Finset (Fin 7) := ![
  {0, 1, 2}, {2, 4, 5}, {2, 4, 6}, {0, 1, 6}, {1, 3, 5},
  {3, 4, 5}, {0, 1, 4}, {2, 5, 6}, {0, 3, 6}, {1, 5, 6},
  {0, 3, 4}, {0, 3, 5}, {1, 2, 4}
]

/-- The missed complement triples of the countermodel. -/
def missedSignature : Fin 13 -> Finset (Fin 9) := ![
  {0, 1, 2}, {0, 2, 4}, {1, 3, 4}, {2, 4, 5}, {1, 3, 6},
  {2, 5, 6}, {1, 5, 7}, {3, 5, 7}, {0, 6, 7}, {0, 3, 8},
  {2, 3, 8}, {4, 7, 8}, {6, 7, 8}
]

/-- The ternary root/fresh balance predicate which forces polynomial
collinearity.  Copied verbatim from the multiplicity-refuted module. -/
def BalancedTriple
    {J : Type}
    (root : J -> Finset (Fin 7)) (missed : J -> Finset (Fin 9))
    (a b c : J) : Bool :=
  decide (4 + (((missed a ∪ missed b) ∪ missed c).card) <=
    9 + (((root a ∩ root b) ∩ root c).card))

/-- Balanced third signatures on the pair `(a,b)`.  Copied verbatim from
the multiplicity-refuted module. -/
def balancedWitnesses
    {J : Type} [Fintype J] [DecidableEq J]
  (root : J -> Finset (Fin 7)) (missed : J -> Finset (Fin 9))
    (a b : J) : Finset J :=
  Finset.univ.filter fun c => decide
    (c ≠ a ∧ c ≠ b ∧ BalancedTriple root missed a b c = true)

/-- The finite hypotheses retained by the regular-signature search.  Copied
verbatim from the multiplicity-refuted module. -/
def RegularSignatureConstraints
    {J : Type} [Fintype J] [DecidableEq J]
    (root : J -> Finset (Fin 7)) (missed : J -> Finset (Fin 9)) : Prop :=
  (forall j, (root j).card = 3) ∧
  (forall j, (missed j).card = 3) ∧
  (forall i j, i ≠ j ->
    2 + ((root i) ∩ (root j)).card <= ((missed i) ∪ (missed j)).card) ∧
  (forall T : Finset (Fin 7),
    (Finset.univ.filter fun j => root j = T).card <= 3)

/-- **The sharp assertion** left conjectural by the multiplicity-refuted
module: thirteen regular signatures force three balanced witnesses on some
pair (hence five collinear points and the packing contradiction). -/
def ThirteenRegularSignaturesForceThreeBalancedWitnesses : Prop :=
  forall (root : Fin 13 -> Finset (Fin 7))
      (missed : Fin 13 -> Finset (Fin 9)),
    RegularSignatureConstraints root missed ->
    exists a b : Fin 13, a ≠ b ∧
      3 <= (balancedWitnesses root missed a b).card

theorem rootSignature_card : forall i, (rootSignature i).card = 3 := by
  decide

theorem missedSignature_card : forall i, (missedSignature i).card = 3 := by
  decide

theorem signature_pair_law : forall i j, i ≠ j ->
    2 + ((rootSignature i) ∩ (rootSignature j)).card <=
      ((missedSignature i) ∪ (missedSignature j)).card := by
  decide

/-- All thirteen root triples are pairwise distinct, so every fiber is a
singleton. -/
theorem root_fiber_card_le_three : forall T : Finset (Fin 7),
    (Finset.univ.filter fun j => rootSignature j = T).card <= 3 := by
  decide

theorem model_constraints :
    RegularSignatureConstraints rootSignature missedSignature :=
  ⟨rootSignature_card, missedSignature_card,
    signature_pair_law, root_fiber_card_le_three⟩

/-- Every pair in the countermodel has at most **two** balanced witnesses. -/
theorem balancedWitnesses_card_le_two : forall a b : Fin 13,
    a ≠ b ->
      (balancedWitnesses rootSignature missedSignature a b).card <= 2 := by
  decide

/-- **Countermodel.**  Thirteen regular signatures satisfying the pair law
and the fiber cap need not put three balanced witnesses on any pair.  The
five-point relevant-line contradiction is therefore unreachable from these
cardinal hypotheses alone. -/
theorem thirteenRegularSignaturesForceThreeBalancedWitnesses_REFUTED :
    Not ThirteenRegularSignaturesForceThreeBalancedWitnesses := by
  intro hforce
  obtain ⟨a, b, hab, hthree⟩ :=
    hforce rootSignature missedSignature model_constraints
  have htwo := balancedWitnesses_card_le_two a b hab
  omega

end ArkLib.ProximityGap.Frontier.W6KFourClosureSharpWitnessRefuted

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.W6KFourClosureSharpWitnessRefuted
#print axioms signature_pair_law
#print axioms root_fiber_card_le_three
#print axioms balancedWitnesses_card_le_two
#print axioms thirteenRegularSignaturesForceThreeBalancedWitnesses_REFUTED
