/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Source-seven signatures: four balanced witnesses are not forced

For regular source-seven outsiders, write `T` for the three source-core
roots and `E` for the three missed complement coordinates.  The pair law is

```text
  2 + |T_i inter T_j| <= |E_i union E_j|,
```

and a triple is balanced when

```text
  4 + |E_i union E_j union E_k|
    <= 9 + |T_i inter T_j inter T_k|.
```

A balanced third signature is forced onto the secant through the first two
polynomial points.  It is therefore tempting to seek four balanced witnesses
on one pair.  The explicit thirteen-signature model below refutes that
strengthening even after imposing the fixed-root-fiber cap three: every pair
has at most three balanced witnesses, and some pair has exactly three.

Consequently the strongest possible multiplicity statement at population
thirteen is the still-conjectural sharp assertion that some pair has *three*
balanced witnesses.  Such a pair would give exactly five collinear points,
enough for the relevant-line packing contradiction.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open Finset

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenMultiplicityRefuted

/-- The source-root triples in the sharp thirteen-signature model. -/
def rootSignature : Fin 13 -> Finset (Fin 7) := ![
  {1, 3, 4}, {0, 1, 3}, {0, 5, 6}, {0, 3, 6}, {1, 2, 4},
  {0, 4, 5}, {2, 3, 6}, {2, 5, 6}, {3, 4, 6}, {4, 5, 6},
  {0, 1, 6}, {1, 2, 4}, {0, 1, 2}
]

/-- The missed complement triples in the same model. -/
def missedSignature : Fin 13 -> Finset (Fin 9) := ![
  {1, 2, 3}, {1, 5, 6}, {2, 3, 5}, {0, 1, 8}, {0, 4, 5},
  {0, 3, 6}, {3, 6, 7}, {1, 3, 4}, {2, 4, 8}, {1, 5, 7},
  {0, 4, 7}, {3, 7, 8}, {2, 6, 8}
]

/-- The ternary root/fresh balance predicate which forces polynomial
collinearity. -/
def BalancedTriple
    {J : Type}
    (root : J -> Finset (Fin 7)) (missed : J -> Finset (Fin 9))
    (a b c : J) : Bool :=
  decide (4 + (((missed a ∪ missed b) ∪ missed c).card) <=
    9 + (((root a ∩ root b) ∩ root c).card))

/-- Balanced third signatures on the pair `(a,b)`. -/
def balancedWitnesses
    {J : Type} [Fintype J] [DecidableEq J]
  (root : J -> Finset (Fin 7)) (missed : J -> Finset (Fin 9))
    (a b : J) : Finset J :=
  Finset.univ.filter fun c => decide
    (c ≠ a ∧ c ≠ b ∧ BalancedTriple root missed a b c = true)

/-- The finite hypotheses retained by the regular-signature search. -/
def RegularSignatureConstraints
    {J : Type} [Fintype J] [DecidableEq J]
    (root : J -> Finset (Fin 7)) (missed : J -> Finset (Fin 9)) : Prop :=
  (forall j, (root j).card = 3) ∧
  (forall j, (missed j).card = 3) ∧
  (forall i j, i ≠ j ->
    2 + ((root i) ∩ (root j)).card <= ((missed i) ∪ (missed j)).card) ∧
  (forall T : Finset (Fin 7),
    (Finset.univ.filter fun j => root j = T).card <= 3)

/-- The invalid strengthening tested by the countermodel. -/
def ThirteenRegularSignaturesForceFourBalancedWitnesses : Prop :=
  forall (root : Fin 13 -> Finset (Fin 7))
      (missed : Fin 13 -> Finset (Fin 9)),
    RegularSignatureConstraints root missed ->
    exists a b : Fin 13, a ≠ b ∧
      4 <= (balancedWitnesses root missed a b).card

theorem rootSignature_card : forall i, (rootSignature i).card = 3 := by
  decide

theorem missedSignature_card : forall i, (missedSignature i).card = 3 := by
  decide

theorem signature_pair_law : forall i j, i ≠ j ->
    2 + ((rootSignature i) ∩ (rootSignature j)).card <=
      ((missedSignature i) ∪ (missedSignature j)).card := by
  decide

theorem root_fiber_card_le_three : forall T : Finset (Fin 7),
    (Finset.univ.filter fun j => rootSignature j = T).card <= 3 := by
  decide

theorem model_constraints :
    RegularSignatureConstraints rootSignature missedSignature := by
  exact ⟨rootSignature_card, missedSignature_card,
    signature_pair_law, root_fiber_card_le_three⟩

/-- Every pair in the model has balanced codegree at most three. -/
theorem balancedWitnesses_card_le_three : forall a b,
    a ≠ b ->
      (balancedWitnesses rootSignature missedSignature a b).card <= 3 := by
  decide

/-- The upper bound is attained, so codegree three is the sharp boundary. -/
theorem exists_balancedWitnesses_card_eq_three : exists a b : Fin 13,
    a ≠ b ∧
      (balancedWitnesses rootSignature missedSignature a b).card = 3 := by
  decide

/-- **Countermodel.**  Thirteen regular signatures need not put four
balanced third signatures on one pair. -/
theorem thirteenRegularSignaturesForceFourBalancedWitnesses_REFUTED :
    Not ThirteenRegularSignaturesForceFourBalancedWitnesses := by
  intro hforce
  obtain ⟨a, b, hab, hfour⟩ :=
    hforce rootSignature missedSignature model_constraints
  have hthree := balancedWitnesses_card_le_three a b hab
  omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenMultiplicityRefuted

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenMultiplicityRefuted
#print axioms signature_pair_law
#print axioms root_fiber_card_le_three
#print axioms balancedWitnesses_card_le_three
#print axioms exists_balancedWitnesses_card_eq_three
#print axioms thirteenRegularSignaturesForceFourBalancedWitnesses_REFUTED
