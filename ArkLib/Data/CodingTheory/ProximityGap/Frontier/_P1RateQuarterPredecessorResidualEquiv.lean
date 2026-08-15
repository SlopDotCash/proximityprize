/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterAdjacentExactPin
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterFourPencilExactPin

/-!
# Equivalence of the P1 predecessor residual interfaces

The generic predecessor split and the guarded four-pencil reduction expose
different proof interfaces for the same canonical bad-count target.  This file
normalizes both interfaces to the literal statement that every two-row stack
has at most `N` bad scalars at the immediate predecessor.

The local proposition `FavorableFourTwoFreshPencilExtraction` imposes a
formally weaker requirement than saturated favorable extraction: its source
cores need only leave two fresh coordinates, with no positive lower bound on
their sizes.  Strict separation of those two local propositions has not been
proved.

Globally, however, `CanonicalLargeBadFourPencilExtraction` is guarded by the
hypothesis that the bad count exceeds `N`.  Since a favorable two-fresh cover
itself forces the count back below `N`, the guarded proposition is logically
equivalent to the uniform bad-count target.  Its reverse implication from a
uniform bound is vacuous: it eliminates the impossible large-count hypothesis
and does not construct a geometric cover for any realizable stack.

The structured-floor residual is also equivalent to the uniform target.  Its
near-direction branch is the residual itself, while the complementary far
branch is already closed by the decoupled-Johnson argument.  Consequently the
two global residuals below are equivalent, but this equivalence must not be
read as a geometric extraction theorem in either direction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterPredecessorResidualEquiv

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.MCAFloorFactorization
open P1RateQuarterScaleArithmetic
open P1RateQuarterCanonicalCodeBridge
open P1RateQuarterPredecessorGenericSplit
open P1RateQuarterFourPencilExactPin

local instance localInstance_P1RateQuarterPredecessorResidualEquiv_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterPredecessorResidualEquiv_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

local notation "deltaPredecessor" =>
  RateQuarterPredecessorFourPencilReduction.P1.predecessorDelta

/-- The shared canonical target: every two-row stack has at most `N` bad
scalars at the immediate predecessor radius. -/
abbrev CanonicalUniformPredecessorBadCount : Prop :=
  ∀ u : WordStack F (Fin 2) (Fin N),
    mcaBadCount (F := F) canonicalCode deltaPredecessor (u 0) (u 1) ≤ N

/-- The generic structured-floor residual is exactly the canonical uniform
predecessor bad-count target.  The forward implication uses the already-proved
far branch; the reverse implication merely restricts a uniform bound to the
near-direction branch. -/
theorem predecessorStructuredFloorResidual_iff_uniform_badCount :
    PredecessorStructuredFloorResidual canonicalDomain ↔
      CanonicalUniformPredecessorBadCount := by
  constructor
  · intro hstructured u
    have hcount := badCount_le_N_of_structuredFloor
      canonicalDomain (u 0) (u 1) hstructured
    simpa only [mcaBadCount, badCount] using hcount
  · intro huniform
    unfold PredecessorStructuredFloorResidual StructuredFloorBound
    intro u0 u1 _hnear
    let u : WordStack F (Fin 2) (Fin N) :=
      fun i => if i = 0 then u0 else u1
    have hcount := huniform u
    simpa [mcaBadCount, badCount, u] using hcount

/-- The guarded favorable two-fresh extraction interface is exactly the same
uniform bad-count target.  In the reverse direction the large-count guard is
false, so this equivalence supplies no geometric cover for a realizable
within-budget stack. -/
theorem largeBadFourPencilExtraction_iff_uniform_badCount :
    CanonicalLargeBadFourPencilExtraction ↔
      CanonicalUniformPredecessorBadCount := by
  simpa only [CanonicalUniformPredecessorBadCount] using
    canonicalLargeBadFourPencilExtraction_iff_uniform_badCount

/-- The two named predecessor residual interfaces are logically equivalent
through their common uniform bad-count target.  This is not a geometric
construction in either direction. -/
theorem predecessorStructuredFloorResidual_iff_largeBadFourPencilExtraction :
    PredecessorStructuredFloorResidual canonicalDomain ↔
      CanonicalLargeBadFourPencilExtraction := by
  calc
    PredecessorStructuredFloorResidual canonicalDomain ↔
        CanonicalUniformPredecessorBadCount :=
      predecessorStructuredFloorResidual_iff_uniform_badCount
    _ ↔ CanonicalLargeBadFourPencilExtraction :=
      largeBadFourPencilExtraction_iff_uniform_badCount.symm

/-- A structured-floor bound implies guarded large-bad extraction only
logically: the structured/far split first proves the uniform count, making the
large-count antecedent impossible.  No pencil cover is constructed. -/
theorem largeBadFourPencilExtraction_of_structuredFloor
    (hstructured : PredecessorStructuredFloorResidual canonicalDomain) :
    CanonicalLargeBadFourPencilExtraction :=
  predecessorStructuredFloorResidual_iff_largeBadFourPencilExtraction.mp
    hstructured

/-- Guarded large-bad extraction implies the structured-floor residual by
first ruling out every over-budget stack and then restricting the resulting
uniform count to near directions.  It does not extract geometry for an
arbitrary structured stack. -/
theorem structuredFloor_of_largeBadFourPencilExtraction
    (hextract : CanonicalLargeBadFourPencilExtraction) :
    PredecessorStructuredFloorResidual canonicalDomain :=
  predecessorStructuredFloorResidual_iff_largeBadFourPencilExtraction.mpr
    hextract

end ArkLib.ProximityGap.Frontier.P1RateQuarterPredecessorResidualEquiv

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterPredecessorResidualEquiv
#print axioms predecessorStructuredFloorResidual_iff_uniform_badCount
#print axioms largeBadFourPencilExtraction_iff_uniform_badCount
#print axioms predecessorStructuredFloorResidual_iff_largeBadFourPencilExtraction
#print axioms largeBadFourPencilExtraction_of_structuredFloor
#print axioms structuredFloor_of_largeBadFourPencilExtraction
