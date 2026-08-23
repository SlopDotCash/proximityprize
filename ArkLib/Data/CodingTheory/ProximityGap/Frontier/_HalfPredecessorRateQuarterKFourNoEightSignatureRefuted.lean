/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourGlobalCoreSynthesis

/-!
# Rate-quarter `k = 4`: the abstract no-eight-core signature cap is false

For a size-seven source core, an exact-nine outsider with three source-core
agreements has a three-element missed set in the nine-coordinate complement.
The global core cap seven only gives the pair condition

```text
2 + |T_i inter T_j| <= |E_i union E_j|,
```

where `T_i` is the source-root triple and `E_i` is the missed triple.

This condition does not bound the outsider population by twelve.  Take two
disjoint root triples and, over each one, the twelve three-point lines of the
affine plane of order three.  Lines within one copy meet in at most one point,
and the two root triples are disjoint, so all 24 signatures satisfy the pair
condition.

This is an exact finite countermodel to a cardinal-only closure, not an RS
realization.  Any proof of the no-eight-core residual must retain a polynomial
relation between the root and missed blocks.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSignatureRefuted

/-- The abstract cardinal statement suggested by the size-seven exact-nine
signature split. -/
def AbstractNoEightSignatureCap : Prop :=
  forall (J : Type) [Fintype J] [DecidableEq J]
      (root : J -> Finset (Fin 7)) (missed : J -> Finset (Fin 9)),
    (forall j, (root j).card = 3) ->
    (forall j, (missed j).card = 3) ->
    (forall i j, i ≠ j ->
      2 + ((root i) ∩ (root j)).card <= ((missed i) ∪ (missed j)).card) ->
    Fintype.card J <= 12

/-- The twelve lines of the affine plane on nine points, written as an
explicit resolvable Steiner triple system. -/
def affinePlaneLine : Fin 12 -> Finset (Fin 9) := ![
  {0, 3, 6}, {1, 4, 7}, {2, 5, 8},
  {0, 1, 2}, {3, 4, 5}, {6, 7, 8},
  {0, 4, 8}, {1, 5, 6}, {2, 3, 7},
  {0, 5, 7}, {1, 3, 8}, {2, 4, 6}
]

/-- Two disjoint source-root triples, one for each copy of the affine plane. -/
def rootSignature (i : Fin 24) : Finset (Fin 7) :=
  if i.1 < 12 then {0, 1, 2} else {3, 4, 5}

/-- Both twelve-element halves use the same affine-plane line catalogue. -/
def missedSignature (i : Fin 24) : Finset (Fin 9) :=
  affinePlaneLine ⟨i.1 % 12, Nat.mod_lt _ (by norm_num)⟩

theorem rootSignature_card : forall i, (rootSignature i).card = 3 := by
  decide

theorem missedSignature_card : forall i, (missedSignature i).card = 3 := by
  decide

/-- All 24 signatures satisfy the exact pair inequality inherited from the
global core cap seven. -/
theorem signature_pair_condition : forall i j, i ≠ j ->
    2 + ((rootSignature i) ∩ (rootSignature j)).card <=
      ((missedSignature i) ∪ (missedSignature j)).card := by
  decide

/-- **Countermodel.**  The abstract signature cap twelve is false. -/
theorem abstractNoEightSignatureCap_REFUTED : Not AbstractNoEightSignatureCap := by
  intro hcap
  have hle := hcap (Fin 24) rootSignature missedSignature
    rootSignature_card missedSignature_card signature_pair_condition
  norm_num at hle

#print axioms rootSignature_card
#print axioms missedSignature_card
#print axioms signature_pair_condition
#print axioms abstractNoEightSignatureCap_REFUTED

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSignatureRefuted
