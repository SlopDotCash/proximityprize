/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._StackProfileDominationInterface

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

There is also a slightly more structured input route: prove that representatives really lie in
their used profile fibers, and prove a one-sided same-profile oscillation estimate.  That route
implies the slack-domination certificate while exposing a more diagnostic refutation surface:
the representative missed its fiber, a same-profile pair has too much bad-count oscillation, or a
used representative-plus-slack allowance is above budget.
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

/-! ## Same-profile oscillation route -/

/-- The representative selected for a used profile actually lies in that profile fiber. -/
def ProfileRepresentativeInFiber
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) : Prop :=
  ∀ p : P, UsedProfile profile p -> profile (rep p) = p

/-- One-sided bad-count oscillation inside every profile fiber, with profile-indexed slack. -/
def ProfileFiberOscillationBounded (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (profile : WordStack A (Fin 2) ι -> P) (slack : P -> ℕ) : Prop :=
  ∀ u v : WordStack A (Fin 2) ι, profile u = profile v ->
    StackBadCount K C δ u ≤ StackBadCount K C δ v + slack (profile u)

/-- A structured certificate for the slack route: used representatives are in their fibers,
same-profile bad counts have bounded one-sided oscillation, and representatives plus slack are
budgeted. -/
def ProfileFiberOscillationCertificate
    (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) (B : ℕ) : Prop :=
  ProfileRepresentativeInFiber profile rep ∧
    ProfileFiberOscillationBounded K C δ profile slack ∧
      ProfileFiberSlackBudgeted K C δ profile rep slack B

/-- A representative-in-fiber theorem plus same-profile oscillation gives the slack domination
condition used by the incidence consumer. -/
theorem profileFiberSlackDominates_of_fiberOscillation
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hosc : ProfileFiberOscillationBounded F C δ profile slack)
    (hrep : ProfileRepresentativeInFiber profile rep) :
    ProfileFiberSlackDominates F C δ profile rep slack := by
  intro u
  exact hosc u (rep (profile u)) (hrep (profile u) ⟨u, rfl⟩).symm

/-- The structured oscillation certificate is a bundled slack-profile certificate. -/
theorem profileFiberSlackCertificate_of_profileFiberOscillationCertificate
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hcert : ProfileFiberOscillationCertificate F C δ profile rep slack B) :
    ProfileFiberSlackCertificate F C δ profile rep slack B :=
  ⟨profileFiberSlackDominates_of_fiberOscillation C δ hcert.2.1 hcert.1, hcert.2.2⟩

/-! ## Endpoint sanity checks for coarse profiles -/

/-- If the profile map is constant, every used profile's representative automatically lies in its
fiber.  This is not useful compression: all stacks occupy the same fiber. -/
theorem profileRepresentativeInFiber_of_constant
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {p₀ : P}
    (hconst : ∀ u : WordStack A (Fin 2) ι, profile u = p₀) :
    ProfileRepresentativeInFiber profile rep := by
  intro p hp
  rcases hp with ⟨u, hu⟩
  have hp₀p : p₀ = p := (hconst u).symm.trans hu
  exact (hconst (rep p)).trans hp₀p

/-- For a constant profile, slack domination is exactly the global bound by the selected
representative plus the single slack allowance.  The coarsest profile therefore recreates the
one-stack/global-dominator problem. -/
theorem profileFiberSlackDominates_constant_iff_forall_le_rep_add_slack
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ} {p₀ : P}
    (hconst : ∀ u : WordStack A (Fin 2) ι, profile u = p₀) :
    ProfileFiberSlackDominates F C δ profile rep slack ↔
      ∀ u : WordStack A (Fin 2) ι,
        StackBadCount F C δ u ≤ StackBadCount F C δ (rep p₀) + slack p₀ := by
  constructor
  · intro hdom u
    simpa [hconst u] using hdom u
  · intro hglobal u
    simpa [hconst u] using hglobal u

/-- For a constant profile, one-sided fiber oscillation is exactly a global pairwise bad-count
diameter bound.  This is the no-free-compression endpoint for the oscillation route. -/
theorem profileFiberOscillationBounded_constant_iff_global_pairwise_bound
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {slack : P -> ℕ} {p₀ : P}
    (hconst : ∀ u : WordStack A (Fin 2) ι, profile u = p₀) :
    ProfileFiberOscillationBounded F C δ profile slack ↔
      ∀ u v : WordStack A (Fin 2) ι,
        StackBadCount F C δ u ≤ StackBadCount F C δ v + slack p₀ := by
  constructor
  · intro hosc u v
    have hsame : profile u = profile v := by rw [hconst u, hconst v]
    simpa [hconst u] using hosc u v hsame
  · intro hglobal u v _hsame
    simpa [hconst u] using hglobal u v

/-- Constant-profile oscillation fails exactly when two arbitrary stacks have a bad-count gap above
the single slack allowance. -/
theorem not_profileFiberOscillationBounded_constant_iff_exists_global_pair_exceeds_slack
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {slack : P -> ℕ} {p₀ : P}
    (hconst : ∀ u : WordStack A (Fin 2) ι, profile u = p₀) :
    (¬ ProfileFiberOscillationBounded F C δ profile slack) ↔
      ∃ u v : WordStack A (Fin 2) ι,
        StackBadCount F C δ v + slack p₀ < StackBadCount F C δ u := by
  rw [profileFiberOscillationBounded_constant_iff_global_pairwise_bound C δ hconst]
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u v
    exact le_of_not_gt (fun hgt => hnone ⟨u, v, hgt⟩)
  · rintro ⟨u, v, hgt⟩ hglobal
    exact (not_lt_of_ge (hglobal u v)) hgt

/-! ## Relation to the profile/cap interface -/

/-- The profile cap induced by a slack representative scheme:
`cap p = badCount(rep p) + slack p`. -/
noncomputable def slackCap
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) (p : P) : ℕ :=
  StackBadCount F C δ (rep p) + slack p

/-- A profile cap only needs to be budgeted on profiles that are actually used by some stack. -/
def UsedProfileBudgeted
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (cap : P -> ℕ) (B : ℕ) : Prop :=
  ∀ p : P, UsedProfile profile p -> cap p ≤ B

/-- Slack domination is exactly the old profile-cap condition for the induced cap
`bad(rep p) + slack p`.  The slack route therefore adds no hidden mathematical strength; it chooses
a particular cap function and asks for the usual pointwise profile cap theorem. -/
theorem profileCaps_slackCap_iff_profileFiberSlackDominates
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ} :
    StackProfileDominationInterface.ProfileCaps F C δ profile
        (slackCap (F := F) C δ rep slack) ↔
      ProfileFiberSlackDominates F C δ profile rep slack := by
  constructor
  · intro hcap u
    simpa [slackCap, StackProfileDominationInterface.StackBadCount, StackBadCount]
      using hcap u
  · intro hdom u
    simpa [slackCap, StackProfileDominationInterface.StackBadCount, StackBadCount]
      using hdom u

/-- Slack budgeting is exactly used-profile budgeting for the induced cap
`bad(rep p) + slack p`. -/
theorem usedProfileBudgeted_slackCap_iff_profileFiberSlackBudgeted
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ} {B : ℕ} :
    UsedProfileBudgeted profile (slackCap (F := F) C δ rep slack) B ↔
      ProfileFiberSlackBudgeted F C δ profile rep slack B := by
  constructor
  · intro hbudget p hp
    simpa [slackCap, StackProfileDominationInterface.StackBadCount, StackBadCount]
      using hbudget p hp
  · intro hbudget p hp
    simpa [slackCap, StackProfileDominationInterface.StackBadCount, StackBadCount]
      using hbudget p hp

/-- The bundled slack-profile certificate is exactly a profile-cap theorem plus a used-profile
budget theorem for the induced slack cap. -/
theorem profileFiberSlackCertificate_iff_slackCap_profileCaps_usedBudgeted
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ} {B : ℕ} :
    ProfileFiberSlackCertificate F C δ profile rep slack B ↔
      StackProfileDominationInterface.ProfileCaps F C δ profile
          (slackCap (F := F) C δ rep slack) ∧
        UsedProfileBudgeted profile (slackCap (F := F) C δ rep slack) B := by
  constructor
  · rintro ⟨hdom, hbudget⟩
    exact ⟨(profileCaps_slackCap_iff_profileFiberSlackDominates C δ).mpr hdom,
      (usedProfileBudgeted_slackCap_iff_profileFiberSlackBudgeted C δ).mpr hbudget⟩
  · rintro ⟨hcap, hbudget⟩
    exact ⟨(profileCaps_slackCap_iff_profileFiberSlackDominates C δ).mp hcap,
      (usedProfileBudgeted_slackCap_iff_profileFiberSlackBudgeted C δ).mp hbudget⟩

/-- If every label in the profile type is used, then slack budgeting is literally the old
all-profile budget condition for the induced cap. -/
theorem profileBudgeted_slackCap_iff_profileFiberSlackBudgeted_of_all_used
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ} {B : ℕ}
    (hall : ∀ p : P, UsedProfile profile p) :
    StackProfileDominationInterface.ProfileBudgeted
        (slackCap (F := F) C δ rep slack) B ↔
      ProfileFiberSlackBudgeted F C δ profile rep slack B := by
  constructor
  · intro hbudget p _hp
    simpa [slackCap, StackProfileDominationInterface.StackBadCount, StackBadCount]
      using hbudget p
  · intro hbudget p
    simpa [slackCap, StackProfileDominationInterface.StackBadCount, StackBadCount]
      using hbudget p (hall p)

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

/-! ## Oscillation scanner forms -/

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [AddCommGroup A] in
/-- Failure of the representative-in-fiber condition is exactly a used profile whose representative
misses that profile label. -/
theorem not_profileRepresentativeInFiber_iff_exists_usedProfile_rep_misses
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) :
    (¬ ProfileRepresentativeInFiber profile rep) ↔
      ∃ p : P, UsedProfile profile p ∧ profile (rep p) ≠ p := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro p hp
    by_contra hmiss
    exact hnone ⟨p, hp, hmiss⟩
  · rintro ⟨p, hp, hmiss⟩ hrep
    exact hmiss (hrep p hp)

/-- Failure of one-sided same-profile oscillation is exactly a same-profile pair whose bad-count
gap is larger than the advertised slack. -/
theorem not_profileFiberOscillationBounded_iff_exists_sameProfile_exceeds_slack
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P) (slack : P -> ℕ) :
    (¬ ProfileFiberOscillationBounded F C δ profile slack) ↔
      ∃ u v : WordStack A (Fin 2) ι, profile u = profile v ∧
        StackBadCount F C δ v + slack (profile u) < StackBadCount F C δ u := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u v hsame
    exact le_of_not_gt (fun hgt => hnone ⟨u, v, hsame, hgt⟩)
  · rintro ⟨u, v, hsame, hgt⟩ hosc
    exact (not_lt_of_ge (hosc u v hsame)) hgt

/-- Positive scanner form for same-profile oscillation. -/
theorem profileFiberOscillationBounded_iff_no_sameProfile_exceeds_slack
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P) (slack : P -> ℕ) :
    ProfileFiberOscillationBounded F C δ profile slack ↔
      ¬ ∃ u v : WordStack A (Fin 2) ι, profile u = profile v ∧
        StackBadCount F C δ v + slack (profile u) < StackBadCount F C δ u := by
  constructor
  · intro hosc hbad
    exact (not_profileFiberOscillationBounded_iff_exists_sameProfile_exceeds_slack
      C δ profile slack).mpr hbad hosc
  · intro hno
    by_contra hnot
    exact hno
      ((not_profileFiberOscillationBounded_iff_exists_sameProfile_exceeds_slack
        C δ profile slack).mp hnot)

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

/-- Structured oscillation-certificate form of the open-core incidence consumer. -/
theorem worstCaseIncidenceBounded_of_profileFiberOscillationCertificate
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hcert : ProfileFiberOscillationCertificate F C δ profile rep slack B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_profileFiberSlackCertificate C δ
    (profileFiberSlackCertificate_of_profileFiberOscillationCertificate C δ hcert)

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

/-- Failure of the structured oscillation certificate is exactly one of the three scanner-visible
faults: a used representative misses its fiber, a same-profile pair exceeds the slack, or a used
profile's allowance is above budget. -/
theorem not_profileFiberOscillationCertificate_iff_exists_rep_misses_or_sameProfile_exceeds_or_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) (B : ℕ) :
    (¬ ProfileFiberOscillationCertificate F C δ profile rep slack B) ↔
      (∃ p : P, UsedProfile profile p ∧ profile (rep p) ≠ p) ∨
        (∃ u v : WordStack A (Fin 2) ι, profile u = profile v ∧
          StackBadCount F C δ v + slack (profile u) < StackBadCount F C δ u) ∨
          ∃ p : P, UsedProfile profile p ∧
            B < StackBadCount F C δ (rep p) + slack p := by
  change
    (¬ (ProfileRepresentativeInFiber profile rep ∧
      ProfileFiberOscillationBounded F C δ profile slack ∧
        ProfileFiberSlackBudgeted F C δ profile rep slack B)) ↔ _
  rw [not_and_or]
  constructor
  · rintro (hrep | hrest)
    · exact Or.inl
        ((not_profileRepresentativeInFiber_iff_exists_usedProfile_rep_misses
          profile rep).mp hrep)
    · rw [not_and_or] at hrest
      rcases hrest with hosc | hbudget
      · exact Or.inr <| Or.inl
          ((not_profileFiberOscillationBounded_iff_exists_sameProfile_exceeds_slack
            C δ profile slack).mp hosc)
      · exact Or.inr <| Or.inr
          ((not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
            C δ profile rep slack B).mp hbudget)
  · rintro (hrep | hosc | hbudget)
    · exact Or.inl
        ((not_profileRepresentativeInFiber_iff_exists_usedProfile_rep_misses
          profile rep).mpr hrep)
    · exact Or.inr
        (by
          intro hpair
          exact ((not_profileFiberOscillationBounded_iff_exists_sameProfile_exceeds_slack
            C δ profile slack).mpr hosc) hpair.1)
    · exact Or.inr
        (by
          intro hpair
          exact ((not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
            C δ profile rep slack B).mpr hbudget) hpair.2)

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

/-- Delta-star consumer for the structured same-profile oscillation certificate. -/
theorem deltaStar_pin_of_profileFiberOscillationCertificate
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hcert : ProfileFiberOscillationCertificate F C δ profile rep slack B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_profileFiberSlackCertificate C εstar hδ
    (profileFiberSlackCertificate_of_profileFiberOscillationCertificate C δ hcert) hbudget

end ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackDominates_of_fiberOscillation
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackCertificate_of_profileFiberOscillationCertificate
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileRepresentativeInFiber_of_constant
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackDominates_constant_iff_forall_le_rep_add_slack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberOscillationBounded_constant_iff_global_pairwise_bound
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberOscillationBounded_constant_iff_exists_global_pair_exceeds_slack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileCaps_slackCap_iff_profileFiberSlackDominates
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.usedProfileBudgeted_slackCap_iff_profileFiberSlackBudgeted
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackCertificate_iff_slackCap_profileCaps_usedBudgeted
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileBudgeted_slackCap_iff_profileFiberSlackBudgeted_of_all_used
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberSlackDominates_iff_exists_stack_exceeds_slack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackDominates_iff_no_stack_exceeds_slack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackBudgeted_iff_no_usedProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileRepresentativeInFiber_iff_exists_usedProfile_rep_misses
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberOscillationBounded_iff_exists_sameProfile_exceeds_slack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberOscillationBounded_iff_no_sameProfile_exceeds_slack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.worstCaseIncidenceBounded_of_profileFiberSlack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.worstCaseIncidenceBounded_of_profileFiberSlackCertificate
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.worstCaseIncidenceBounded_of_profileFiberOscillationCertificate
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberSlackCertificate_iff_exists_stack_exceeds_slack_or_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberOscillationCertificate_iff_exists_rep_misses_or_sameProfile_exceeds_or_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.deltaStar_pin_of_profileFiberSlack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.deltaStar_pin_of_profileFiberSlackCertificate
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.deltaStar_pin_of_profileFiberOscillationCertificate
