/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Slackened profile-fiber dominance

The exact profile-fiber-max route asks for a representative that dominates every stack in its
profile fiber.  That is the right final certificate, but it can be too brittle for analytic
experiments: a coarse profile might only support a stability theorem saying every stack in the
fiber is within a controlled slack of a chosen representative.

This file packages that approximate route.  A profile scheme supplies

* a representative `rep p` for each profile label;
* a nonnegative integer slack `slack p`;
* a fiber-slack domination theorem saying every stack is at most
  `StackBadCount (rep (profile u)) + slack (profile u)`;
* a budget theorem saying every used representative plus its slack is at most `B`.

Those two claims are exactly enough for the open-core incidence hypothesis and therefore for the
delta-star lower pin.  The negative lemmas give scanners the matching finite failure surface: either
some stack exceeds its representative-plus-slack allowance, or some used profile's allowance is
above the target budget.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance

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

/-- A profile value is used when at least one stack has that profile. -/
def UsedProfile {P : Type}
    (profile : WordStack A (Fin 2) ι -> P) (p : P) : Prop :=
  ∃ u : WordStack A (Fin 2) ι, profile u = p

/-- Approximate fiber domination: every stack is bounded by the representative of its profile plus
the profile's slack allowance. -/
def ProfileFiberSlackDominates (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    StackBadCount K C δ u ≤ StackBadCount K C δ (rep (profile u)) + slack (profile u)

/-- Every used profile's representative-plus-slack allowance is within the target budget. -/
def ProfileFiberSlackBudgeted (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) (B : ℕ) : Prop :=
  ∀ p : P, UsedProfile profile p -> StackBadCount K C δ (rep p) + slack p ≤ B

/-- The bundled slack-profile certificate. -/
def ProfileFiberSlackCertificate (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) (B : ℕ) : Prop :=
  ProfileFiberSlackDominates K C δ profile rep slack ∧
    ProfileFiberSlackBudgeted K C δ profile rep slack B

/-- Failure of slack domination is exactly a stack above its representative-plus-slack allowance. -/
theorem not_profileFiberSlackDominates_iff_exists_stack_exceeds_slack
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) :
    (¬ ProfileFiberSlackDominates F C δ profile rep slack) ↔
      ∃ u : WordStack A (Fin 2) ι,
        StackBadCount F C δ (rep (profile u)) + slack (profile u) <
          StackBadCount F C δ u := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u
    exact le_of_not_gt (fun hgt => hnone ⟨u, hgt⟩)
  · rintro ⟨u, hgt⟩ hdom
    exact (not_lt_of_ge (hdom u)) hgt

/-- Positive scanner form for slack domination. -/
theorem profileFiberSlackDominates_iff_no_stack_exceeds_slack
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) :
    ProfileFiberSlackDominates F C δ profile rep slack ↔
      ¬ ∃ u : WordStack A (Fin 2) ι,
        StackBadCount F C δ (rep (profile u)) + slack (profile u) <
          StackBadCount F C δ u := by
  constructor
  · intro hdom hbad
    exact (not_profileFiberSlackDominates_iff_exists_stack_exceeds_slack
      C δ profile rep slack).mpr hbad hdom
  · intro hno
    by_contra hnot
    exact hno
      ((not_profileFiberSlackDominates_iff_exists_stack_exceeds_slack
        C δ profile rep slack).mp hnot)

/-- Failure of the slack budget is exactly a used profile whose representative-plus-slack allowance
is above budget. -/
theorem not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) (B : ℕ) :
    (¬ ProfileFiberSlackBudgeted F C δ profile rep slack B) ↔
      ∃ p : P, UsedProfile profile p ∧
        B < StackBadCount F C δ (rep p) + slack p := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro p hp
    exact le_of_not_gt (fun hgt => hnone ⟨p, hp, hgt⟩)
  · rintro ⟨p, hp, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget p hp)) hgt

/-- Positive scanner form for the slack budget. -/
theorem profileFiberSlackBudgeted_iff_no_usedProfile_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) (B : ℕ) :
    ProfileFiberSlackBudgeted F C δ profile rep slack B ↔
      ¬ ∃ p : P, UsedProfile profile p ∧
        B < StackBadCount F C δ (rep p) + slack p := by
  constructor
  · intro hbudget hbad
    exact (not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
      C δ profile rep slack B).mpr hbad hbudget
  · intro hno
    by_contra hnot
    exact hno
      ((not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
        C δ profile rep slack B).mp hnot)

/-- The slack-profile certificate gives the actual open-core incidence hypothesis. -/
theorem worstCaseIncidenceBounded_of_profileFiberSlack
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hdom : ProfileFiberSlackDominates F C δ profile rep slack)
    (hbudget : ProfileFiberSlackBudgeted F C δ profile rep slack B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro u
  exact le_trans (hdom u) (hbudget (profile u) ⟨u, rfl⟩)

/-- Bundled-certificate form of the slack-profile incidence consumer. -/
theorem worstCaseIncidenceBounded_of_profileFiberSlackCertificate
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hcert : ProfileFiberSlackCertificate F C δ profile rep slack B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_profileFiberSlack C δ hcert.1 hcert.2

/-- Failure of the bundled slack-profile certificate is exactly a stack above its allowance or a
used profile whose allowance is above budget. -/
theorem not_profileFiberSlackCertificate_iff_exists_stack_exceeds_slack_or_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) (B : ℕ) :
    (¬ ProfileFiberSlackCertificate F C δ profile rep slack B) ↔
      (∃ u : WordStack A (Fin 2) ι,
        StackBadCount F C δ (rep (profile u)) + slack (profile u) <
          StackBadCount F C δ u) ∨
        ∃ p : P, UsedProfile profile p ∧
          B < StackBadCount F C δ (rep p) + slack p := by
  change
    (¬ (ProfileFiberSlackDominates F C δ profile rep slack ∧
      ProfileFiberSlackBudgeted F C δ profile rep slack B)) ↔ _
  rw [not_and_or]
  constructor
  · rintro (hdom | hbudget)
    · exact Or.inl
        ((not_profileFiberSlackDominates_iff_exists_stack_exceeds_slack
          C δ profile rep slack).mp hdom)
    · exact Or.inr
        ((not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
          C δ profile rep slack B).mp hbudget)
  · rintro (hstack | hbudget)
    · exact Or.inl
        ((not_profileFiberSlackDominates_iff_exists_stack_exceeds_slack
          C δ profile rep slack).mpr hstack)
    · exact Or.inr
        ((not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
          C δ profile rep slack B).mpr hbudget)

/-- Delta-star consumer for profile-fiber slack domination. -/
theorem deltaStar_pin_of_profileFiberSlack
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hdom : ProfileFiberSlackDominates F C δ profile rep slack)
    (hbudgeted : ProfileFiberSlackBudgeted F C δ profile rep slack B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_profileFiberSlack C δ hdom hbudgeted)
    hbudget

/-- Delta-star consumer for the bundled slack-profile certificate. -/
theorem deltaStar_pin_of_profileFiberSlackCertificate
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hcert : ProfileFiberSlackCertificate F C δ profile rep slack B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_profileFiberSlack C εstar hδ hcert.1 hcert.2 hbudget

end ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberSlackDominates_iff_exists_stack_exceeds_slack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackDominates_iff_no_stack_exceeds_slack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackBudgeted_iff_no_usedProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.worstCaseIncidenceBounded_of_profileFiberSlack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.worstCaseIncidenceBounded_of_profileFiberSlackCertificate
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberSlackCertificate_iff_exists_stack_exceeds_slack_or_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.deltaStar_pin_of_profileFiberSlack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.deltaStar_pin_of_profileFiberSlackCertificate
