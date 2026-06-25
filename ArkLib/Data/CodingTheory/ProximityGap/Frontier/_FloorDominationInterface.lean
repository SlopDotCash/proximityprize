/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Floor localization needs a domination theorem to become a prize proof

The off-BGK floor/localization lane studies a distinguished far-line family.  The delta-star lower
pin, however, consumes `OpenCoreConditionalPin.WorstCaseIncidenceBounded`, a bound over *every*
word stack.  This file records the exact missing bridge in the real API:

* `StackBadCount C delta u` is the actual bad-scalar count used by
  `WorstCaseIncidenceBounded`;
* `StackDominates C delta uStar` says the distinguished stack `uStar` has count at least every
  other stack's count;
* `worstCaseIncidenceBounded_of_stackDomination` proves that domination plus a bound on `uStar`
  is sufficient for the prize's open-core incidence hypothesis.

The important point is negative: floor localization by itself can at most bound a proposed
`uStar`.  To prove the prize floor through this lane, one must also prove `StackDominates` (or an
equivalent sparse/worst-direction domination theorem).  That domination theorem is the real
load-bearing content and is expected to be BGK/Paley-hard.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.FloorDominationInterface

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The actual bad-scalar count appearing in `WorstCaseIncidenceBounded`. -/
noncomputable def StackBadCount (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) : ℕ := by
  classical
  exact (Finset.univ.filter (fun γ : K => mcaEvent (F := K) C δ (u 0) (u 1) γ)).card

/-- A one-stack incidence budget for the actual MCA bad-scalar count. -/
def StackBounded (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (u : WordStack A (Fin 2) ι) (B : ℕ) : Prop :=
  StackBadCount K C δ u ≤ B

/-- The missing domination theorem: one distinguished stack is at least as bad as every stack. -/
def StackDominates (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (uStar : WordStack A (Fin 2) ι) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    StackBadCount K C δ u ≤ StackBadCount K C δ uStar

/-- Worst-case incidence is exactly the all-stack budget phrased through `StackBadCount`. -/
theorem worstCaseIncidenceBounded_iff_all_stackBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) (B : ℕ) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B
      ↔ ∀ u : WordStack A (Fin 2) ι, StackBounded F C δ u B := by
  rfl

/-- A worst-case incidence budget automatically bounds every distinguished stack. -/
theorem stackBounded_of_worstCaseIncidenceBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    (hI : ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B)
    (uStar : WordStack A (Fin 2) ι) :
    StackBounded F C δ uStar B :=
  hI uStar

/-- **Sufficient bridge.** If the distinguished stack dominates all stacks and that stack is
within budget, then the actual open-core hypothesis `WorstCaseIncidenceBounded` holds. -/
theorem worstCaseIncidenceBounded_of_stackDomination
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {uStar : WordStack A (Fin 2) ι}
    (hdom : StackDominates F C δ uStar)
    (hstar : StackBounded F C δ uStar B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro u
  exact le_trans (hdom u) hstar

/-- **Delta-star consumer.** Domination plus a budgeted distinguished stack is exactly enough to
feed the existing conditional pin.  This is the honest shape of any floor-localization proof:
localization supplies `hstar`; the genuinely hard new theorem is `hdom`. -/
theorem deltaStar_pin_of_stackDomination
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {uStar : WordStack A (Fin 2) ι}
    (hdom : StackDominates F C δ uStar)
    (hstar : StackBounded F C δ uStar B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_stackDomination
      C δ hdom hstar)
    hbudget

end ArkLib.ProximityGap.Frontier.FloorDominationInterface

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.worstCaseIncidenceBounded_iff_all_stackBounded
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.stackBounded_of_worstCaseIncidenceBounded
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.worstCaseIncidenceBounded_of_stackDomination
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.deltaStar_pin_of_stackDomination
