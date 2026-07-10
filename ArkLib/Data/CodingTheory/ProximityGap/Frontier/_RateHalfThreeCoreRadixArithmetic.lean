/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapeRateHalfBracket
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FiniteFunctionalRatioAvoidance
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorCoreFreshDecode

/-!
# Rate-half three-core radix counterexample: exact arithmetic connector

The three-core base certificate has `93` projective external-defect directions.
At the prize lift `m=2^24`, this gives `93m` candidate labels, while the block
length is only `64m=2^30`.  This file checks the exact arithmetic and packages
the final finite-set injection needed to refute an all-stack `n`-scalar cap.

The geometric construction of the injected labels is deliberately a separate
obligation.  The executable certificate and derivation are in
`scripts/probes/probe_rate_half_three_core_radix_counterexample.py` and the
matching KB note.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial Code
open _root_.ProximityGap
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.RateHalfThreeCoreRadixArithmetic

attribute [local instance] Classical.propDecidable

/-- Number of points in each fiber of `X -> X^(2^24)`. -/
abbrev fiberSize : Nat := 2 ^ 24

/-- The prize block length, written in its 64-fiber form. -/
abbrev prizeLength : Nat := 64 * fiberSize

/-- Number of projective directions supplied by three 33-fiber cores. -/
abbrev liftedDirectionCount : Nat := 93 * fiberSize

theorem prizeLength_eq_two_pow_30 : prizeLength = 2 ^ 30 := by norm_num

theorem liftedDirectionCount_eq : liftedDirectionCount = 1560281088 := by norm_num

theorem excess_eq : liftedDirectionCount - prizeLength = 486539264 := by norm_num

theorem prizeLength_lt_liftedDirectionCount : prizeLength < liftedDirectionCount := by
  norm_num

theorem liftedDirectionCount_lt_firstPrime :
    liftedDirectionCount < ArkLib.ProximityGap.PrizeShapePrimeP30.P := by
  norm_num [ArkLib.ProximityGap.PrizeShapePrimeP30.P]

/-- The second hyperplane-avoidance union also fits strictly inside the field. -/
theorem directionPairs_lt_firstPrime :
    Nat.choose liftedDirectionCount 2 < ArkLib.ProximityGap.PrizeShapePrimeP30.P := by
  rw [Nat.choose_two_right]
  norm_num [liftedDirectionCount, fiberSize, ArkLib.ProximityGap.PrizeShapePrimeP30.P]

/-- The ordered-pair budget used by `exists_ratio_injective` also fits. -/
theorem directionSquare_lt_firstPrime :
    liftedDirectionCount * liftedDirectionCount <
      ArkLib.ProximityGap.PrizeShapePrimeP30.P := by
  norm_num [liftedDirectionCount, fiberSize, ArkLib.ProximityGap.PrizeShapePrimeP30.P]

theorem offDiagDirections_lt_firstPrime :
    Fintype.card
        (FiniteFunctionalRatioAvoidance.OffDiag (Fin liftedDirectionCount)) <
      ArkLib.ProximityGap.PrizeShapePrimeP30.P := by
  calc
    Fintype.card
        (FiniteFunctionalRatioAvoidance.OffDiag (Fin liftedDirectionCount))
        ≤ Fintype.card (Fin liftedDirectionCount × Fin liftedDirectionCount) :=
      Fintype.card_subtype_le _
    _ = liftedDirectionCount * liftedDirectionCount := by simp
    _ < ArkLib.ProximityGap.PrizeShapePrimeP30.P := directionSquare_lt_firstPrime

/-- **Operational counterexample connector.**  An injection of all `93m`
directions into genuine bad scalars forces strictly more than `n=64m` bad
scalars.  This is the exact final counting step needed by the three-core radix
construction. -/
theorem badCount_gt_length_of_injected_directions
    {F A iota : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (C : Set (iota -> A)) (delta : NNReal) (u0 u1 : iota -> A)
    (gamma : Fin liftedDirectionCount ↪ F)
    (hbad : forall j, mcaEvent C delta u0 u1 (gamma j)) :
    prizeLength <
      (Finset.univ.filter fun zeta : F => mcaEvent C delta u0 u1 zeta).card := by
  classical
  let labels : Finset F := Finset.univ.map gamma
  have hlabelsCard : labels.card = liftedDirectionCount := by
    simp [labels]
  have hlabelsSub : labels ⊆
      Finset.univ.filter fun zeta : F => mcaEvent C delta u0 u1 zeta := by
    intro zeta hzeta
    simp only [labels, Finset.mem_map] at hzeta
    obtain ⟨j, _, rfl⟩ := hzeta
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad j⟩
  have hcard := Finset.card_le_card hlabelsSub
  rw [hlabelsCard] at hcard
  exact prizeLength_lt_liftedDirectionCount.trans_le hcard

/-- **Core-plus-fresh assembly.**  Pointwise polynomial certificates for all
`93m` injected labels compose directly into a strict `n`-budget violation.
This packages the exact interface between the radix/projective construction
and the literal MCA event. -/
theorem reedSolomon_badCount_gt_length_of_coreFresh_family
    {F I : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [Nonempty I] [DecidableEq I]
    (domain : I ↪ F) (k : Nat) (delta : NNReal)
    (u : WordStack F (Fin 2) I)
    (gamma : Fin liftedDirectionCount ↪ F)
    (D : Fin liftedDirectionCount -> Finset I)
    (e : Fin liftedDirectionCount -> I)
    (a r : Fin liftedDirectionCount -> F[X])
    (he : forall j, e j ∉ D j)
    (ha : forall j, (a j).degree < (k : Nat))
    (hr : forall j, (r j).degree < (k : Nat))
    (hq : forall j, (a j + Polynomial.C (gamma j) * r j).degree < (k : Nat))
    (hcoreCard : forall j, k ≤ (D j).card)
    (hsize : forall j, (((D j).card + 1 : Nat) : NNReal) ≥
      (1 - delta) * (Fintype.card I : NNReal))
    (hcore : forall j i, i ∈ D j ->
      (a j).eval (domain i) = u 0 i ∧ (r j).eval (domain i) = u 1 i)
    (hfresh : forall j,
      (a j + Polynomial.C (gamma j) * r j).eval (domain (e j)) =
        u 0 (e j) + gamma j * u 1 (e j))
    (hmismatch : forall j,
      ((a j).eval (domain (e j)), (r j).eval (domain (e j))) ≠
        (u 0 (e j), u 1 (e j))) :
    prizeLength <
      (Finset.univ.filter fun zeta : F =>
        mcaEvent
          ((ReedSolomon.code domain k : Submodule F (I -> F)) : Set (I -> F))
          delta (u 0) (u 1) zeta).card := by
  apply badCount_gt_length_of_injected_directions
    (((ReedSolomon.code domain k : Submodule F (I -> F)) : Set (I -> F)))
    delta (u 0) (u 1) gamma
  intro j
  exact HalfPredecessorCoreFreshDecode.mcaEvent_of_affine_core_fresh
    domain k delta u (gamma j) (D j) (e j) (a j) (r j)
    (he j) (ha j) (hr j) (hq j) (hcoreCard j) (hsize j)
    (hcore j) (hfresh j) (hmismatch j)

end ArkLib.ProximityGap.Frontier.RateHalfThreeCoreRadixArithmetic

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateHalfThreeCoreRadixArithmetic
#print axioms badCount_gt_length_of_injected_directions
#print axioms reedSolomon_badCount_gt_length_of_coreFresh_family
