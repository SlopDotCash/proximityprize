/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

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
* the negative lemmas record the exact scanner obligations: a proposed dominator fails precisely
  when some stack has strictly larger bad-scalar count, and under a true dominator the universal
  incidence budget fails precisely when the distinguished stack is above budget.

The important point is negative: floor localization by itself can at most bound a proposed
`uStar`.  To prove the prize floor through this lane, one must also prove `StackDominates` (or an
equivalent sparse/worst-direction domination theorem).  That domination theorem is the real
load-bearing content and is expected to be BGK/Paley-hard.
-/

set_option autoImplicit false
set_option linter.style.longLine false


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

/-- Failure of a one-stack budget is exactly a strict budget violation. -/
theorem not_stackBounded_iff_budget_lt_stackBadCount
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (u : WordStack A (Fin 2) ι) (B : ℕ) :
    (¬ StackBounded F C δ u B) ↔ B < StackBadCount F C δ u := by
  constructor
  · intro hnot
    exact lt_of_not_ge hnot
  · intro hgt hbounded
    exact (not_lt_of_ge hbounded) hgt

/-- The missing domination theorem: one distinguished stack is at least as bad as every stack. -/
def StackDominates (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (uStar : WordStack A (Fin 2) ι) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    StackBadCount K C δ u ≤ StackBadCount K C δ uStar

/-- A candidate stack fails to dominate exactly when some stack has strictly larger bad-scalar
count. -/
theorem not_stackDominates_iff_exists_strictly_larger
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (uStar : WordStack A (Fin 2) ι) :
    (¬ StackDominates F C δ uStar)
      ↔ ∃ u : WordStack A (Fin 2) ι,
        StackBadCount F C δ uStar < StackBadCount F C δ u := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u
    exact le_of_not_gt (fun hgt => hnone ⟨u, hgt⟩)
  · rintro ⟨u, hgt⟩ hdom
    exact (not_lt_of_ge (hdom u)) hgt

/-- Failure of the single-stack floor certificate is exactly a strictly worse stack or a budget
violation by the proposed dominator itself. -/
theorem not_singleStackDominationCertificate_iff_exists_larger_or_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (uStar : WordStack A (Fin 2) ι) (B : ℕ) :
    (¬ (StackDominates F C δ uStar ∧ StackBounded F C δ uStar B)) ↔
      (∃ u : WordStack A (Fin 2) ι,
        StackBadCount F C δ uStar < StackBadCount F C δ u) ∨
        B < StackBadCount F C δ uStar := by
  rw [not_and_or]
  constructor
  · rintro (hdom | hbounded)
    · exact Or.inl ((not_stackDominates_iff_exists_strictly_larger C δ uStar).mp hdom)
    · exact Or.inr ((not_stackBounded_iff_budget_lt_stackBadCount C δ uStar B).mp hbounded)
  · rintro (hlarger | hbudget)
    · exact Or.inl ((not_stackDominates_iff_exists_strictly_larger C δ uStar).mpr hlarger)
    · exact Or.inr ((not_stackBounded_iff_budget_lt_stackBadCount C δ uStar B).mpr hbudget)

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

/-- The bundled one-stack floor certificate directly supplies the full worst-case incidence
hypothesis. -/
theorem worstCaseIncidenceBounded_of_singleStackDominationCertificate
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {uStar : WordStack A (Fin 2) ι}
    (hcert : StackDominates F C δ uStar ∧ StackBounded F C δ uStar B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_stackDomination C δ hcert.1 hcert.2

/-- For a dominating stack, the universal open-core budget is equivalent to the one-stack budget
on that distinguished stack. -/
theorem worstCaseIncidenceBounded_iff_stackBounded_of_stackDomination
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {uStar : WordStack A (Fin 2) ι}
    (hdom : StackDominates F C δ uStar) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B
      ↔ StackBounded F C δ uStar B :=
  ⟨fun hI => stackBounded_of_worstCaseIncidenceBounded C δ hI uStar,
    fun hstar => worstCaseIncidenceBounded_of_stackDomination C δ hdom hstar⟩

/-- A single stack above budget refutes the full worst-case incidence hypothesis. -/
theorem not_worstCaseIncidenceBounded_of_budget_lt_stackBadCount
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {uWitness : WordStack A (Fin 2) ι}
    (hgt : B < StackBadCount F C δ uWitness) :
    ¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro hI
  exact (not_lt_of_ge (hI uWitness)) hgt

/-- Exact negative form of the open-core incidence budget: it fails precisely when some stack is
above budget. -/
theorem not_worstCaseIncidenceBounded_iff_exists_budget_lt_stackBadCount
    (C : Set (ι -> A)) (δ : ℝ≥0) (B : ℕ) :
    (¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B)
      ↔ ∃ u : WordStack A (Fin 2) ι, B < StackBadCount F C δ u := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u
    exact le_of_not_gt (fun hgt => hnone ⟨u, hgt⟩)
  · rintro ⟨u, hgt⟩
    exact not_worstCaseIncidenceBounded_of_budget_lt_stackBadCount C δ hgt

/-- Under a true domination theorem, failure of the universal open-core budget is exactly failure of
the distinguished stack budget. -/
theorem not_worstCaseIncidenceBounded_iff_budget_lt_stackBadCount_of_stackDomination
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {uStar : WordStack A (Fin 2) ι}
    (hdom : StackDominates F C δ uStar) :
    (¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B)
      ↔ B < StackBadCount F C δ uStar := by
  rw [worstCaseIncidenceBounded_iff_stackBounded_of_stackDomination C δ hdom]
  exact not_stackBounded_iff_budget_lt_stackBadCount C δ uStar B

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

/-- Delta-star consumer for the bundled one-stack floor certificate. -/
theorem deltaStar_pin_of_singleStackDominationCertificate
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {uStar : WordStack A (Fin 2) ι}
    (hcert : StackDominates F C δ uStar ∧ StackBounded F C δ uStar B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_stackDomination C εstar hδ hcert.1 hcert.2 hbudget

end ArkLib.ProximityGap.Frontier.FloorDominationInterface

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.not_stackBounded_iff_budget_lt_stackBadCount
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.not_stackDominates_iff_exists_strictly_larger
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.not_singleStackDominationCertificate_iff_exists_larger_or_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.worstCaseIncidenceBounded_iff_all_stackBounded
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.stackBounded_of_worstCaseIncidenceBounded
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.worstCaseIncidenceBounded_of_stackDomination
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.worstCaseIncidenceBounded_of_singleStackDominationCertificate
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.worstCaseIncidenceBounded_iff_stackBounded_of_stackDomination
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.not_worstCaseIncidenceBounded_of_budget_lt_stackBadCount
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.not_worstCaseIncidenceBounded_iff_exists_budget_lt_stackBadCount
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.not_worstCaseIncidenceBounded_iff_budget_lt_stackBadCount_of_stackDomination
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.deltaStar_pin_of_stackDomination
#print axioms ArkLib.ProximityGap.Frontier.FloorDominationInterface.deltaStar_pin_of_singleStackDominationCertificate
