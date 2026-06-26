/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# The off-BGK floor is necessary, not sufficient

The bad-prime localization lane controls one distinguished far-line family.  The prize floor,
however, consumes a worst-case bound over every word stack / far direction.  This file records the
bare logical shape as an axiom-clean guardrail:

* a worst-case bound over all directions implies the distinguished-family bound;
* a distinguished-family bound does not imply the worst-case bound;
* a lower bound from one summand of a supremum cannot upper-bound the supremum.

The statements are intentionally abstract.  They are meant to prevent future proof attempts from
using the binder-family floor localization (`epsMCA_ge_far_incidence`, a one-family lower-bound
surface) as if it were the `WorstCaseIncidenceBounded` input required by the delta-star lower pin.
Closing the binder family removes an obstruction; it does not by itself prove the prize floor.
-/

namespace ArkLib.ProximityGap.Frontier.FloorNecessaryNotSufficient

/-- A worst-case incidence budget: every direction has at most `B` bad scalars. -/
def AllDirectionsBounded {ι γ : Type*} (bad : ι -> Finset γ) (B : Nat) : Prop :=
  forall i : ι, Finset.card (bad i) <= B

/-- A one-family incidence budget: one distinguished direction has at most `B` bad scalars. -/
def OneDirectionBounded {ι γ : Type*} (bad : ι -> Finset γ) (i0 : ι) (B : Nat) : Prop :=
  Finset.card (bad i0) <= B

/-- Worst-case control implies control of any chosen family.  This is the only automatic direction. -/
theorem allDirectionsBounded_implies_one {ι γ : Type*} {bad : ι -> Finset γ} {B : Nat}
    (h : AllDirectionsBounded bad B) (i0 : ι) :
    OneDirectionBounded bad i0 B :=
  h i0

/-- A distinguished direction is a true global maximizer for the bad-scalar count.  This is the
missing bridge that would make a singleton binder/floor family sufficient for a worst-case bound. -/
def OneDirectionMaximizes {ι γ : Type*} (bad : ι -> Finset γ) (i0 : ι) : Prop :=
  forall i : ι, Finset.card (bad i) <= Finset.card (bad i0)

/-- The singleton-maximizer condition is exactly the all-directions bound at the singleton's own
count. -/
theorem oneDirectionMaximizes_iff_allDirectionsBounded_at_own_card
    {ι γ : Type*} {bad : ι -> Finset γ} {i0 : ι} :
    OneDirectionMaximizes bad i0 ↔ AllDirectionsBounded bad (Finset.card (bad i0)) := by
  rfl

/-- A one-direction budget becomes a worst-case budget only after a global-maximizer proof. -/
theorem allDirectionsBounded_of_oneDirectionBounded_and_maximizes
    {ι γ : Type*} {bad : ι -> Finset γ} {i0 : ι} {B : Nat}
    (hone : OneDirectionBounded bad i0 B)
    (hmax : OneDirectionMaximizes bad i0) :
    AllDirectionsBounded bad B := by
  intro i
  exact le_trans (hmax i) hone

/-- Scanner-facing failure form: a proposed singleton floor representative is not a global maximizer
precisely when some other direction has a strictly larger bad-scalar count. -/
theorem not_oneDirectionMaximizes_iff_exists_larger
    {ι γ : Type*} {bad : ι -> Finset γ} {i0 : ι} :
    (¬ OneDirectionMaximizes bad i0) ↔
      ∃ i : ι, Finset.card (bad i0) < Finset.card (bad i) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro i
    exact le_of_not_gt (fun hgt => hnone ⟨i, hgt⟩)
  · rintro ⟨i, hgt⟩ hmax
    exact (not_lt_of_ge (hmax i)) hgt

/-- Toy counterexample: the distinguished family is empty, while another family has one bad scalar. -/
def toyBad : Bool -> Finset Unit
  | false => ∅
  | true => {()}

/-- In the toy model, the distinguished family satisfies budget `0`. -/
theorem toy_oneDirectionBounded : OneDirectionBounded toyBad false 0 := by
  simp [OneDirectionBounded, toyBad]

/-- In the same toy model, the worst-case budget `0` fails. -/
theorem toy_not_allDirectionsBounded : Not (AllDirectionsBounded toyBad 0) := by
  intro h
  have htrue := h true
  simp [toyBad] at htrue

/-- Therefore a one-family bound is not a theorem-level substitute for a worst-case bound. -/
theorem oneDirectionBounded_not_sufficient :
    ∃ bad : Bool -> Finset Unit,
      OneDirectionBounded bad false 0 /\ Not (AllDirectionsBounded bad 0) := by
  exact ⟨toyBad, toy_oneDirectionBounded, toy_not_allDirectionsBounded⟩

/-- `single <= global` models a lower bound on a supremal/global quantity from one family. -/
def LowerBoundOnly (single global : Nat) : Prop :=
  single <= global

/-- A budget assertion for a natural-valued count. -/
def WithinBudget (value budget : Nat) : Prop :=
  value <= budget

/-- A one-family lower bound plus a one-family budget cannot upper-bound the global quantity. -/
theorem lowerBoundOnly_not_upperBound :
    ∃ global single budget : Nat,
      LowerBoundOnly single global /\ WithinBudget single budget /\
        Not (WithinBudget global budget) := by
  refine ⟨1, 0, 0, ?_, ?_, ?_⟩
  · unfold LowerBoundOnly
    decide
  · unfold WithinBudget
    decide
  · unfold WithinBudget
    decide

/-! ## Axiom audit -/

#print axioms allDirectionsBounded_implies_one
#print axioms oneDirectionMaximizes_iff_allDirectionsBounded_at_own_card
#print axioms allDirectionsBounded_of_oneDirectionBounded_and_maximizes
#print axioms not_oneDirectionMaximizes_iff_exists_larger
#print axioms toy_oneDirectionBounded
#print axioms toy_not_allDirectionsBounded
#print axioms oneDirectionBounded_not_sufficient
#print axioms lowerBoundOnly_not_upperBound

end ArkLib.ProximityGap.Frontier.FloorNecessaryNotSufficient
