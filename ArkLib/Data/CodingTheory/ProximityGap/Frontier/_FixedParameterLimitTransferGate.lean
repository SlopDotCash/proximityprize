/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Fixed-parameter limits do not transfer to the prize diagonal without an effective threshold

Vertical Sato--Tate / Katz / Untrau-style inputs often have the logical shape:

* for every fixed order `n`, the desired property holds for all sufficiently large fields `p`.

The #464 prize needs a different statement:

* the desired property holds at the finite diagonal field size `p = scale n`
  (for example `scale n = n^beta`, or the split prime-field representative near that scale).

This file records the exact abstract transfer contract.  A fixed-parameter eventual theorem
transfers to the diagonal only after choosing effective thresholds `P0 n` and proving
`P0 n <= scale n` for every prize `n`.  Without that quantitative threshold, the two limits can
miss each other: the property may be eventually true above `scale n + 1` for every fixed `n`, while
being false at the prize point `p = scale n`.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.FixedParameterLimitTransferGate

/-- Pointwise eventual truth: for every fixed `n`, the property holds for all sufficiently large
field sizes `p`.  This is the qualitative fixed-parameter limit shape. -/
def PointwiseEventuallyGood (Good : Nat -> Nat -> Prop) : Prop :=
  forall n, exists P0, forall p, P0 <= p -> Good n p

/-- Eventual truth with an explicit threshold function `P0 n`. -/
def EventualWithThreshold (Good : Nat -> Nat -> Prop) (P0 : Nat -> Nat) : Prop :=
  forall n p, P0 n <= p -> Good n p

/-- The prize-facing diagonal statement at the designated scale `p = scale n`. -/
def PrizeDiagonalGood (Good : Nat -> Nat -> Prop) (scale : Nat -> Nat) : Prop :=
  forall n, Good n (scale n)

/-- The quantitative condition that every fixed-parameter threshold is reached before the prize
diagonal field size. -/
def ThresholdBelowScale (P0 scale : Nat -> Nat) : Prop :=
  forall n, P0 n <= scale n

/-- Sufficient transfer contract: an explicit eventual theorem transfers to the prize diagonal
when all thresholds are below the diagonal scale. -/
theorem prizeDiagonalGood_of_eventualWithThreshold
    {Good : Nat -> Nat -> Prop} {P0 scale : Nat -> Nat}
    (hEventually : EventualWithThreshold Good P0)
    (hBelow : ThresholdBelowScale P0 scale) :
    PrizeDiagonalGood Good scale := by
  intro n
  exact hEventually n (scale n) (hBelow n)

/-- Necessity of the same threshold condition for any universal transfer principle.  Test the
principle on the property `Good n p := P0 n <= p`. -/
theorem thresholdBelowScale_of_universal_transfer
    {P0 scale : Nat -> Nat}
    (hTransfer :
      forall Good : Nat -> Nat -> Prop,
        EventualWithThreshold Good P0 -> PrizeDiagonalGood Good scale) :
    ThresholdBelowScale P0 scale := by
  intro n
  let Good : Nat -> Nat -> Prop := fun n p => P0 n <= p
  have hEventually : EventualWithThreshold Good P0 := by
    intro n p hp
    exact hp
  exact hTransfer Good hEventually n

/-- The exact contract for transferring an explicit fixed-parameter eventual theorem to a diagonal:
the universal transfer principle is equivalent to `P0 n <= scale n` for every `n`. -/
theorem universal_transfer_iff_thresholdBelowScale (P0 scale : Nat -> Nat) :
    (forall Good : Nat -> Nat -> Prop,
        EventualWithThreshold Good P0 -> PrizeDiagonalGood Good scale)
      <-> ThresholdBelowScale P0 scale := by
  constructor
  · intro hTransfer
    exact thresholdBelowScale_of_universal_transfer (P0 := P0) (scale := scale) hTransfer
  · intro hBelow Good hEventually
    exact prizeDiagonalGood_of_eventualWithThreshold
      (Good := Good) (P0 := P0) (scale := scale) hEventually hBelow

/-- Countermodel property: true strictly after the diagonal scale, false on the diagonal. -/
def afterScaleGood (scale : Nat -> Nat) : Nat -> Nat -> Prop :=
  fun n p => scale n < p

/-- For each fixed `n`, the countermodel property is eventually true: take threshold
`scale n + 1`. -/
theorem afterScaleGood_pointwiseEventually (scale : Nat -> Nat) :
    PointwiseEventuallyGood (afterScaleGood scale) := by
  intro n
  refine ⟨scale n + 1, ?_⟩
  intro p hp
  exact Nat.lt_of_succ_le hp

/-- The same property fails at every diagonal point, in particular at `n = 0`. -/
theorem afterScaleGood_not_prizeDiagonal (scale : Nat -> Nat) :
    ¬ PrizeDiagonalGood (afterScaleGood scale) scale := by
  intro hDiagonal
  exact (Nat.lt_irrefl (scale 0)) (hDiagonal 0)

/-- A qualitative fixed-parameter eventual theorem alone does not imply any fixed diagonal
statement, for any chosen scale. -/
theorem pointwiseEventually_not_enough_for_any_scale (scale : Nat -> Nat) :
    ¬ (forall Good : Nat -> Nat -> Prop,
        PointwiseEventuallyGood Good -> PrizeDiagonalGood Good scale) := by
  intro hTransfer
  exact afterScaleGood_not_prizeDiagonal scale
    (hTransfer (afterScaleGood scale) (afterScaleGood_pointwiseEventually scale))

/-- The countermodel's explicit threshold is just beyond the diagonal scale.  It satisfies the
eventual theorem but violates the threshold-below-scale contract. -/
theorem afterScaleGood_threshold_contract_sharp (scale : Nat -> Nat) :
    EventualWithThreshold (afterScaleGood scale) (fun n => scale n + 1) ∧
      ¬ ThresholdBelowScale (fun n => scale n + 1) scale := by
  constructor
  · intro n p hp
    exact Nat.lt_of_succ_le hp
  · intro hBelow
    have hbad : scale 0 + 1 <= scale 0 := hBelow 0
    omega

end ArkLib.ProximityGap.Frontier.FixedParameterLimitTransferGate

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.FixedParameterLimitTransferGate.prizeDiagonalGood_of_eventualWithThreshold
#print axioms ArkLib.ProximityGap.Frontier.FixedParameterLimitTransferGate.thresholdBelowScale_of_universal_transfer
#print axioms ArkLib.ProximityGap.Frontier.FixedParameterLimitTransferGate.universal_transfer_iff_thresholdBelowScale
#print axioms ArkLib.ProximityGap.Frontier.FixedParameterLimitTransferGate.afterScaleGood_pointwiseEventually
#print axioms ArkLib.ProximityGap.Frontier.FixedParameterLimitTransferGate.afterScaleGood_not_prizeDiagonal
#print axioms ArkLib.ProximityGap.Frontier.FixedParameterLimitTransferGate.pointwiseEventually_not_enough_for_any_scale
#print axioms ArkLib.ProximityGap.Frontier.FixedParameterLimitTransferGate.afterScaleGood_threshold_contract_sharp
