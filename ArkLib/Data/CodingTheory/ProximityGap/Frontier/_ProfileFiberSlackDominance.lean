/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._StackProfileDominationInterface

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

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.longFile 1800


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

/-! ## Zero-slack factorization route -/

/-- The bad-scalar count factors through the chosen representative of the profile.  This is the
exact zero-slack object a compressed profile would have to prove: every stack has the same bad-count
as its selected profile representative. -/
def ProfileBadCountRepresented (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    StackBadCount K C δ u = StackBadCount K C δ (rep (profile u))

/-- The representative-free zero-slack profile condition: bad-scalar counts are constant on every
profile fiber.  This is the actual invariant a compressed zero-slack profile must satisfy. -/
def ProfileBadCountFiberConstant (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (profile : WordStack A (Fin 2) ι -> P) : Prop :=
  ∀ u v : WordStack A (Fin 2) ι, profile u = profile v ->
    StackBadCount K C δ u = StackBadCount K C δ v

/-- Zero one-sided oscillation is exactly fiberwise constancy of the bad-scalar count. -/
theorem profileBadCountFiberConstant_of_zero_oscillation
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    (hosc : ProfileFiberOscillationBounded F C δ profile (fun _ => 0)) :
    ProfileBadCountFiberConstant F C δ profile := by
  intro u v hsame
  apply le_antisymm
  · simpa using hosc u v hsame
  · simpa using hosc v u hsame.symm

/-- Fiberwise bad-count constancy gives zero one-sided oscillation. -/
theorem profileFiberOscillationBounded_zero_of_profileBadCountFiberConstant
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    (hconst : ProfileBadCountFiberConstant F C δ profile) :
    ProfileFiberOscillationBounded F C δ profile (fun _ => 0) := by
  intro u v hsame
  have hcount : StackBadCount F C δ u = StackBadCount F C δ v := hconst u v hsame
  simp [hcount]

/-- Representative-free normal form for zero slack: zero oscillation is equivalent to bad-count
constancy on profile fibers. -/
theorem profileFiberOscillationBounded_zero_iff_profileBadCountFiberConstant
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P} :
    ProfileFiberOscillationBounded F C δ profile (fun _ => 0) ↔
      ProfileBadCountFiberConstant F C δ profile := by
  constructor
  · exact profileBadCountFiberConstant_of_zero_oscillation C δ
  · exact profileFiberOscillationBounded_zero_of_profileBadCountFiberConstant C δ

/-- If bad counts are constant on fibers and representatives are in used fibers, then bad counts
factor through the chosen representatives. -/
theorem profileBadCountRepresented_of_profileBadCountFiberConstant
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hconst : ProfileBadCountFiberConstant F C δ profile)
    (hrep : ProfileRepresentativeInFiber profile rep) :
    ProfileBadCountRepresented F C δ profile rep := by
  intro u
  exact hconst u (rep (profile u)) (hrep (profile u) ⟨u, rfl⟩).symm

/-- Representative factorization implies fiberwise bad-count constancy, regardless of whether the
representatives lie in their fibers. -/
theorem profileBadCountFiberConstant_of_profileBadCountRepresented
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hfactor : ProfileBadCountRepresented F C δ profile rep) :
    ProfileBadCountFiberConstant F C δ profile := by
  intro u v hsame
  have hrepEq : rep (profile u) = rep (profile v) := congrArg rep hsame
  calc
    StackBadCount F C δ u = StackBadCount F C δ (rep (profile u)) := hfactor u
    _ = StackBadCount F C δ (rep (profile v)) := by rw [hrepEq]
    _ = StackBadCount F C δ v := (hfactor v).symm

/-- With in-fiber representatives, representative bad-count factorization is exactly fiberwise
bad-count constancy. -/
theorem profileBadCountRepresented_iff_profileBadCountFiberConstant_of_repInFiber
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hrep : ProfileRepresentativeInFiber profile rep) :
    ProfileBadCountRepresented F C δ profile rep ↔
      ProfileBadCountFiberConstant F C δ profile := by
  constructor
  · exact profileBadCountFiberConstant_of_profileBadCountRepresented C δ
  · intro hconst
    exact profileBadCountRepresented_of_profileBadCountFiberConstant C δ hconst hrep

/-- Zero same-profile oscillation plus in-fiber representatives forces the bad-count to factor
through the representative of each profile. -/
theorem profileBadCountRepresented_of_zero_oscillation
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hosc : ProfileFiberOscillationBounded F C δ profile (fun _ => 0))
    (hrep : ProfileRepresentativeInFiber profile rep) :
    ProfileBadCountRepresented F C δ profile rep := by
  exact profileBadCountRepresented_of_profileBadCountFiberConstant C δ
    (profileBadCountFiberConstant_of_zero_oscillation C δ hosc) hrep

/-- If bad-counts factor through profile representatives, then zero same-profile oscillation holds:
same-profile stacks have equal represented counts. -/
theorem profileFiberOscillationBounded_zero_of_profileBadCountRepresented
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hfactor : ProfileBadCountRepresented F C δ profile rep) :
    ProfileFiberOscillationBounded F C δ profile (fun _ => 0) := by
  exact profileFiberOscillationBounded_zero_of_profileBadCountFiberConstant C δ
    (profileBadCountFiberConstant_of_profileBadCountRepresented C δ hfactor)

/-- Failure of fiberwise bad-count constancy is exactly a same-profile pair with unequal counts. -/
theorem not_profileBadCountFiberConstant_iff_exists_sameProfile_count_ne
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P) :
    (¬ ProfileBadCountFiberConstant F C δ profile) ↔
      ∃ u v : WordStack A (Fin 2) ι, profile u = profile v ∧
        StackBadCount F C δ u ≠ StackBadCount F C δ v := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u v hsame
    by_contra hne
    exact hnone ⟨u, v, hsame, hne⟩
  · rintro ⟨u, v, hsame, hne⟩ hconst
    exact hne (hconst u v hsame)

/-- With in-fiber representatives, zero same-profile oscillation is exactly representative
bad-count factorization.  This is the zero-slack middle-case target for a compressed profile. -/
theorem profileFiberOscillationBounded_zero_iff_profileBadCountRepresented_of_repInFiber
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hrep : ProfileRepresentativeInFiber profile rep) :
    ProfileFiberOscillationBounded F C δ profile (fun _ => 0) ↔
      ProfileBadCountRepresented F C δ profile rep := by
  constructor
  · intro hosc
    exact profileBadCountRepresented_of_zero_oscillation C δ hosc hrep
  · intro hfactor
    exact profileFiberOscillationBounded_zero_of_profileBadCountRepresented C δ hfactor

/-- Representative factorization plus used-profile budget gives the actual open-core incidence
hypothesis. -/
theorem worstCaseIncidenceBounded_of_profileBadCountRepresented_budget
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hfactor : ProfileBadCountRepresented F C δ profile rep)
    (hbudget : ProfileFiberSlackBudgeted F C δ profile rep (fun _ => 0) B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro u
  have hrepBudget : StackBadCount F C δ (rep (profile u)) ≤ B := by
    simpa using hbudget (profile u) ⟨u, rfl⟩
  calc
    StackBadCount F C δ u = StackBadCount F C δ (rep (profile u)) := hfactor u
    _ ≤ B := hrepBudget

/-- Delta-star consumer for the representative-factorization route. -/
theorem deltaStar_pin_of_profileBadCountRepresented_budget
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hfactor : ProfileBadCountRepresented F C δ profile rep)
    (hbudgeted : ProfileFiberSlackBudgeted F C δ profile rep (fun _ => 0) B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_profileBadCountRepresented_budget C δ hfactor hbudgeted)
    hbudget

/-- Representative-free zero-slack consumer: fiberwise bad-count constancy, an in-fiber
representative section, and a used-representative budget imply the open-core incidence bound. -/
theorem worstCaseIncidenceBounded_of_profileBadCountFiberConstant_budget
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hconst : ProfileBadCountFiberConstant F C δ profile)
    (hrep : ProfileRepresentativeInFiber profile rep)
    (hbudget : ProfileFiberSlackBudgeted F C δ profile rep (fun _ => 0) B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_profileBadCountRepresented_budget C δ
    (profileBadCountRepresented_of_profileBadCountFiberConstant C δ hconst hrep) hbudget

/-- Delta-star consumer for the representative-free zero-slack fiber-constancy route. -/
theorem deltaStar_pin_of_profileBadCountFiberConstant_budget
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hconst : ProfileBadCountFiberConstant F C δ profile)
    (hrep : ProfileRepresentativeInFiber profile rep)
    (hbudgeted : ProfileFiberSlackBudgeted F C δ profile rep (fun _ => 0) B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_profileBadCountRepresented_budget C εstar hδ
    (profileBadCountRepresented_of_profileBadCountFiberConstant C δ hconst hrep)
    hbudgeted hbudget

/-- With in-fiber representatives, the zero-slack oscillation certificate is exactly bad-count
factorization plus the used-representative budget. -/
theorem profileFiberOscillationCertificate_zero_iff_profileBadCountRepresented_and_budget
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hrep : ProfileRepresentativeInFiber profile rep) :
    ProfileFiberOscillationCertificate F C δ profile rep (fun _ => 0) B ↔
      ProfileBadCountRepresented F C δ profile rep ∧
        ProfileFiberSlackBudgeted F C δ profile rep (fun _ => 0) B := by
  constructor
  · intro hcert
    exact ⟨(profileFiberOscillationBounded_zero_iff_profileBadCountRepresented_of_repInFiber
      C δ hcert.1).mp hcert.2.1, hcert.2.2⟩
  · rintro ⟨hfactor, hbudget⟩
    exact ⟨hrep,
      (profileFiberOscillationBounded_zero_iff_profileBadCountRepresented_of_repInFiber
        C δ hrep).mpr hfactor, hbudget⟩

/-- Failure of representative bad-count factorization is exactly a stack whose bad count differs
from that of its selected profile representative. -/
theorem not_profileBadCountRepresented_iff_exists_stack_count_ne
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) :
    (¬ ProfileBadCountRepresented F C δ profile rep) ↔
      ∃ u : WordStack A (Fin 2) ι,
        StackBadCount F C δ u ≠ StackBadCount F C δ (rep (profile u)) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u
    by_contra hne
    exact hnone ⟨u, hne⟩
  · rintro ⟨u, hne⟩ hfactor
    exact hne (hfactor u)

/-- Exact failure surface for the zero-slack factorization-plus-budget certificate. -/
theorem not_profileBadCountRepresented_and_zeroBudgeted_iff_exists_factor_miss_or_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (B : ℕ) :
    (¬ (ProfileBadCountRepresented F C δ profile rep ∧
        ProfileFiberSlackBudgeted F C δ profile rep (fun _ => 0) B)) ↔
      (∃ u : WordStack A (Fin 2) ι,
        StackBadCount F C δ u ≠ StackBadCount F C δ (rep (profile u))) ∨
        ∃ p : P, UsedProfile profile p ∧ B < StackBadCount F C δ (rep p) := by
  rw [not_and_or]
  constructor
  · rintro (hfactor | hbudget)
    · exact Or.inl
        ((not_profileBadCountRepresented_iff_exists_stack_count_ne C δ profile rep).mp
          hfactor)
    · by_contra hnone
      apply hbudget
      intro p hused
      exact le_of_not_gt (fun hgt => hnone (Or.inr ⟨p, hused, hgt⟩))
  · rintro (hfactor | hbudget)
    · exact Or.inl
        ((not_profileBadCountRepresented_iff_exists_stack_count_ne C δ profile rep).mpr
          hfactor)
    · rcases hbudget with ⟨p, hused, hgt⟩
      exact Or.inr (fun hbudgeted =>
        (not_lt_of_ge (by simpa using hbudgeted p hused)) hgt)

/-! ## Zero-slack profile cardinality pressure -/

/-- A finite scanner family has pairwise distinct bad-scalar counts. -/
def BadCountInjectiveOn (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (U : Finset (WordStack A (Fin 2) ι)) : Prop :=
  Set.InjOn (fun u : WordStack A (Fin 2) ι => StackBadCount K C δ u) (↑U : Set _)

/-- If bad counts are constant on profile fibers, then the profile is injective on any finite
scanner family whose bad counts are pairwise distinct.  Otherwise two distinct-count stacks would
land in one fiber, contradicting fiberwise constancy. -/
theorem profile_injOn_of_profileBadCountFiberConstant_of_badCountInjectiveOn
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {U : Finset (WordStack A (Fin 2) ι)}
    (hconst : ProfileBadCountFiberConstant F C δ profile)
    (hsep : BadCountInjectiveOn F C δ U) :
    Set.InjOn profile (↑U : Set (WordStack A (Fin 2) ι)) := by
  intro u hu v hv hprofile
  exact hsep hu hv (hconst u v hprofile)

/-- Zero-slack fiber constancy forces enough profile labels to separate every finite scanner family
with pairwise distinct bad-scalar counts.  A compressed profile with fewer labels than such a family
cannot be a zero-slack invariant. -/
theorem card_le_profileCard_of_profileBadCountFiberConstant_badCountInjectiveOn
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    (U : Finset (WordStack A (Fin 2) ι))
    (hconst : ProfileBadCountFiberConstant F C δ profile)
    (hsep : BadCountInjectiveOn F C δ U) :
    U.card ≤ Fintype.card P := by
  classical
  have hinj : Set.InjOn profile (↑U : Set (WordStack A (Fin 2) ι)) :=
    profile_injOn_of_profileBadCountFiberConstant_of_badCountInjectiveOn C δ hconst hsep
  calc
    U.card = (U.image profile).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card P := Finset.card_le_univ _

/-- Cardinality refutation for zero-slack profile constancy: a finite set of stacks with pairwise
distinct bad counts and cardinality larger than the profile space kills the proposed invariant. -/
theorem not_profileBadCountFiberConstant_of_profileCard_lt_badCountInjectiveOn
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {U : Finset (WordStack A (Fin 2) ι)}
    (hsep : BadCountInjectiveOn F C δ U)
    (hcard : Fintype.card P < U.card) :
    ¬ ProfileBadCountFiberConstant F C δ profile := by
  intro hconst
  exact (not_lt_of_ge
    (card_le_profileCard_of_profileBadCountFiberConstant_badCountInjectiveOn
      C δ U hconst hsep)) hcard

/-- Cardinality refutation for representative bad-count factorization.  If the profile type is too
small to separate a finite family of distinct bad counts, no representative map can make bad counts
factor through the profile. -/
theorem not_profileBadCountRepresented_of_profileCard_lt_badCountInjectiveOn
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    {U : Finset (WordStack A (Fin 2) ι)}
    (hsep : BadCountInjectiveOn F C δ U)
    (hcard : Fintype.card P < U.card) :
    ¬ ProfileBadCountRepresented F C δ profile rep := by
  intro hfactor
  exact (not_profileBadCountFiberConstant_of_profileCard_lt_badCountInjectiveOn
    C δ hsep hcard)
    (profileBadCountFiberConstant_of_profileBadCountRepresented C δ hfactor)

/-- Cardinality refutation for zero same-profile oscillation.  A zero-slack oscillation theorem
also forces the profile to separate every finite family of distinct bad-count stacks. -/
theorem not_profileFiberOscillationBounded_zero_of_profileCard_lt_badCountInjectiveOn
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {U : Finset (WordStack A (Fin 2) ι)}
    (hsep : BadCountInjectiveOn F C δ U)
    (hcard : Fintype.card P < U.card) :
    ¬ ProfileFiberOscillationBounded F C δ profile (fun _ => 0) := by
  intro hosc
  exact (not_profileBadCountFiberConstant_of_profileCard_lt_badCountInjectiveOn
    C δ hsep hcard)
    (profileBadCountFiberConstant_of_zero_oscillation C δ hosc)

open Classical in
/-- The finite image of actual bad-scalar counts across the whole stack universe. -/
noncomputable def StackBadCountImage (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0) : Finset ℕ :=
  (Finset.univ : Finset (WordStack A (Fin 2) ι)).image
    (fun u => StackBadCount K C δ u)

open Classical in
/-- Global bad-count image pressure: a zero-slack profile needs at least as many profile labels as
there are distinct realized `StackBadCount` values. -/
theorem stackBadCountImage_card_le_profileCard_of_profileBadCountFiberConstant
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    (hconst : ProfileBadCountFiberConstant F C δ profile) :
    (StackBadCountImage F C δ).card ≤ Fintype.card P := by
  let countOfProfile : P -> ℕ := fun p =>
    if hused : UsedProfile profile p then
      StackBadCount F C δ (Classical.choose hused)
    else
      0
  have hfactor : ∀ u : WordStack A (Fin 2) ι,
      StackBadCount F C δ u = countOfProfile (profile u) := by
    intro u
    have hused : UsedProfile profile (profile u) := ⟨u, rfl⟩
    dsimp [countOfProfile]
    rw [dif_pos hused]
    exact hconst u (Classical.choose hused) (Classical.choose_spec hused).symm
  have hsubset :
      StackBadCountImage F C δ ⊆
        (Finset.univ : Finset P).image countOfProfile := by
    intro b hb
    change b ∈ (Finset.univ : Finset (WordStack A (Fin 2) ι)).image
      (fun u => StackBadCount F C δ u) at hb
    rcases Finset.mem_image.mp hb with ⟨u, _hu, hu⟩
    exact Finset.mem_image.mpr
      ⟨profile u, Finset.mem_univ _, by
        calc
          countOfProfile (profile u) = StackBadCount F C δ u := (hfactor u).symm
          _ = b := hu⟩
  calc
    (StackBadCountImage F C δ).card ≤
        ((Finset.univ : Finset P).image countOfProfile).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.univ : Finset P).card := Finset.card_image_le
    _ = Fintype.card P := by simp

/-- Global cardinality refutation for zero-slack profile constancy.  If there are more distinct
bad-scalar counts than profile labels, bad counts cannot be constant on profile fibers. -/
theorem not_profileBadCountFiberConstant_of_profileCard_lt_stackBadCountImage
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    (hcard : Fintype.card P < (StackBadCountImage F C δ).card) :
    ¬ ProfileBadCountFiberConstant F C δ profile := by
  intro hconst
  exact (not_lt_of_ge
    (stackBadCountImage_card_le_profileCard_of_profileBadCountFiberConstant
      C δ hconst)) hcard

/-- Global cardinality refutation for representative bad-count factorization. -/
theorem not_profileBadCountRepresented_of_profileCard_lt_stackBadCountImage
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hcard : Fintype.card P < (StackBadCountImage F C δ).card) :
    ¬ ProfileBadCountRepresented F C δ profile rep := by
  intro hfactor
  exact (not_profileBadCountFiberConstant_of_profileCard_lt_stackBadCountImage
    C δ hcard)
    (profileBadCountFiberConstant_of_profileBadCountRepresented C δ hfactor)

/-- Global cardinality refutation for zero same-profile oscillation. -/
theorem not_profileFiberOscillationBounded_zero_of_profileCard_lt_stackBadCountImage
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    (hcard : Fintype.card P < (StackBadCountImage F C δ).card) :
    ¬ ProfileFiberOscillationBounded F C δ profile (fun _ => 0) := by
  intro hosc
  exact (not_profileBadCountFiberConstant_of_profileCard_lt_stackBadCountImage
    C δ hcard)
    (profileBadCountFiberConstant_of_zero_oscillation C δ hosc)

/-- A profile-indexed finite cover for the realized bad-count values.  This is the positive-slack
version of the zero-slack image gate: a profile need not make counts constant, but it must explain
which finite set of counts can occur in each fiber. -/
def ProfileBadCountImageCovered (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (profile : WordStack A (Fin 2) ι -> P) (cover : P -> Finset ℕ) : Prop :=
  ∀ u : WordStack A (Fin 2) ι, StackBadCount K C δ u ∈ cover (profile u)

open Classical in
/-- If profile fibers have finite bad-count covers, the global bad-count image is bounded by the
sum of the cover sizes. -/
theorem stackBadCountImage_card_le_sum_profileBadCountCover
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P} {cover : P -> Finset ℕ}
    (hcover : ProfileBadCountImageCovered F C δ profile cover) :
    (StackBadCountImage F C δ).card ≤ ∑ p : P, (cover p).card := by
  have hsubset :
      StackBadCountImage F C δ ⊆ (Finset.univ : Finset P).biUnion cover := by
    intro b hb
    change b ∈ (Finset.univ : Finset (WordStack A (Fin 2) ι)).image
      (fun u => StackBadCount F C δ u) at hb
    rcases Finset.mem_image.mp hb with ⟨u, _hu, hu⟩
    exact Finset.mem_biUnion.mpr
      ⟨profile u, Finset.mem_univ _, by
        rw [← hu]
        exact hcover u⟩
  calc
    (StackBadCountImage F C δ).card ≤ ((Finset.univ : Finset P).biUnion cover).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ p ∈ (Finset.univ : Finset P), (cover p).card := Finset.card_biUnion_le
    _ = ∑ p : P, (cover p).card := by simp

/-- Refutation socket for profile-indexed finite bad-count covers. -/
theorem not_profileBadCountImageCovered_of_sum_cover_lt_stackBadCountImage
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P} {cover : P -> Finset ℕ}
    (hsmall : (∑ p : P, (cover p).card) < (StackBadCountImage F C δ).card) :
    ¬ ProfileBadCountImageCovered F C δ profile cover := by
  intro hcover
  exact (not_lt_of_ge
    (stackBadCountImage_card_le_sum_profileBadCountCover C δ hcover)) hsmall

/-- Plain slack domination gives a coarse one-sided cover: every stack in profile `p` has bad-count
at most the representative count plus the profile slack.  This does not require the representative
to lie in the fiber, so the interval starts at zero rather than around the representative. -/
theorem profileBadCountImageCovered_of_profileFiberSlackDominates
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hdom : ProfileFiberSlackDominates F C δ profile rep slack) :
    ProfileBadCountImageCovered F C δ profile
      (fun p => Finset.Icc 0 (StackBadCount F C δ (rep p) + slack p)) := by
  intro u
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hdom u⟩

/-- Image-size pressure for an unstructured slack-domination theorem.  Since domination is only
one-sided, the profile fiber is covered by `[0, bad(rep p) + slack p]`. -/
theorem stackBadCountImage_card_le_sum_profileFiberSlackDominationCaps
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hdom : ProfileFiberSlackDominates F C δ profile rep slack) :
    (StackBadCountImage F C δ).card ≤
      ∑ p : P, (Finset.Icc 0
        (StackBadCount F C δ (rep p) + slack p)).card := by
  exact stackBadCountImage_card_le_sum_profileBadCountCover C δ
    (profileBadCountImageCovered_of_profileFiberSlackDominates C δ hdom)

/-- Refutation socket for plain slack domination: if the one-sided profile cap intervals have too
little total size, then the advertised domination theorem is false. -/
theorem not_profileFiberSlackDominates_of_sum_capIntervalCard_lt_stackBadCountImage
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hsmall :
      (∑ p : P, (Finset.Icc 0
        (StackBadCount F C δ (rep p) + slack p)).card) <
        (StackBadCountImage F C δ).card) :
    ¬ ProfileFiberSlackDominates F C δ profile rep slack := by
  intro hdom
  exact (not_lt_of_ge
    (stackBadCountImage_card_le_sum_profileFiberSlackDominationCaps
      C δ hdom)) hsmall

/-- A budgeted slack certificate bounds the whole bad-count image by `[0, B]`.  This is weaker
than the oscillation-specific `2 * slack + 1` tests, but it applies to any slack certificate. -/
theorem stackBadCountImage_card_le_budget_add_one_of_profileFiberSlack
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hdom : ProfileFiberSlackDominates F C δ profile rep slack)
    (hbudget : ProfileFiberSlackBudgeted F C δ profile rep slack B) :
    (StackBadCountImage F C δ).card ≤ B + 1 := by
  have hsubset : StackBadCountImage F C δ ⊆ Finset.Icc 0 B := by
    intro b hb
    change b ∈ (Finset.univ : Finset (WordStack A (Fin 2) ι)).image
      (fun u => StackBadCount F C δ u) at hb
    rcases Finset.mem_image.mp hb with ⟨u, _hu, hu⟩
    rw [← hu]
    exact Finset.mem_Icc.mpr
      ⟨Nat.zero_le _,
        le_trans (hdom u) (hbudget (profile u) ⟨u, rfl⟩)⟩
  calc
    (StackBadCountImage F C δ).card ≤ (Finset.Icc 0 B).card :=
      Finset.card_le_card hsubset
    _ = B + 1 := by
      rw [Nat.card_Icc]
      omega

/-- Bundled-certificate form of the budget image-size pressure. -/
theorem stackBadCountImage_card_le_budget_add_one_of_profileFiberSlackCertificate
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hcert : ProfileFiberSlackCertificate F C δ profile rep slack B) :
    (StackBadCountImage F C δ).card ≤ B + 1 :=
  stackBadCountImage_card_le_budget_add_one_of_profileFiberSlack C δ hcert.1 hcert.2

/-- Certificate-level budget refuter: a certificate with budget `B` cannot realize more than
`B + 1` distinct bad-count values. -/
theorem not_profileFiberSlackCertificate_of_budget_add_one_lt_stackBadCountImage
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hsmall : B + 1 < (StackBadCountImage F C δ).card) :
    ¬ ProfileFiberSlackCertificate F C δ profile rep slack B := by
  intro hcert
  exact (not_lt_of_ge
    (stackBadCountImage_card_le_budget_add_one_of_profileFiberSlackCertificate
      C δ hcert)) hsmall

/-- Same-profile oscillation gives a concrete finite bad-count cover: each profile fiber's counts
lie in the interval of radius `slack p` around the representative's bad count. -/
theorem profileBadCountImageCovered_of_profileFiberOscillation
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hosc : ProfileFiberOscillationBounded F C δ profile slack)
    (hrep : ProfileRepresentativeInFiber profile rep) :
    ProfileBadCountImageCovered F C δ profile
      (fun p => Finset.Icc
        (StackBadCount F C δ (rep p) - slack p)
        (StackBadCount F C δ (rep p) + slack p)) := by
  intro u
  have hsame : profile u = profile (rep (profile u)) :=
    (hrep (profile u) ⟨u, rfl⟩).symm
  have hupper :
      StackBadCount F C δ u ≤
        StackBadCount F C δ (rep (profile u)) + slack (profile u) :=
    hosc u (rep (profile u)) hsame
  have hlowerWitness :
      StackBadCount F C δ (rep (profile u)) ≤
        StackBadCount F C δ u + slack (profile u) := by
    simpa [hsame.symm] using hosc (rep (profile u)) u hsame.symm
  exact Finset.mem_Icc.mpr ⟨by omega, hupper⟩

/-- Image-size pressure for a concrete same-profile oscillation certificate. -/
theorem stackBadCountImage_card_le_sum_profileFiberOscillationIntervals
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hosc : ProfileFiberOscillationBounded F C δ profile slack)
    (hrep : ProfileRepresentativeInFiber profile rep) :
    (StackBadCountImage F C δ).card ≤
      ∑ p : P, (Finset.Icc
        (StackBadCount F C δ (rep p) - slack p)
        (StackBadCount F C δ (rep p) + slack p)).card := by
  exact stackBadCountImage_card_le_sum_profileBadCountCover C δ
    (profileBadCountImageCovered_of_profileFiberOscillation C δ hosc hrep)

/-- Refutation socket for same-profile oscillation certificates with too little total interval
mass. -/
theorem not_profileFiberOscillationBounded_of_sum_intervalCard_lt_stackBadCountImage
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hrep : ProfileRepresentativeInFiber profile rep)
    (hsmall :
      (∑ p : P, (Finset.Icc
        (StackBadCount F C δ (rep p) - slack p)
        (StackBadCount F C δ (rep p) + slack p)).card) <
        (StackBadCountImage F C δ).card) :
    ¬ ProfileFiberOscillationBounded F C δ profile slack := by
  intro hosc
  exact (not_lt_of_ge
    (stackBadCountImage_card_le_sum_profileFiberOscillationIntervals
      C δ hosc hrep)) hsmall

/-- A natural-number interval centered at `m` with radius `s` has at most `2 * s + 1` values.
The lower endpoint is truncated at zero, so this is only an upper bound. -/
theorem card_Icc_sub_add_le_two_mul_add_one (m s : ℕ) :
    (Finset.Icc (m - s) (m + s)).card ≤ 2 * s + 1 := by
  rw [Nat.card_Icc]
  omega

/-- Same-profile oscillation forces the global bad-count image to fit inside the total
`2 * slack + 1` interval budget. -/
theorem stackBadCountImage_card_le_sum_profileFiberOscillationSlack
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hosc : ProfileFiberOscillationBounded F C δ profile slack)
    (hrep : ProfileRepresentativeInFiber profile rep) :
    (StackBadCountImage F C δ).card ≤ ∑ p : P, (2 * slack p + 1) := by
  calc
    (StackBadCountImage F C δ).card ≤
        ∑ p : P, (Finset.Icc
          (StackBadCount F C δ (rep p) - slack p)
          (StackBadCount F C δ (rep p) + slack p)).card :=
      stackBadCountImage_card_le_sum_profileFiberOscillationIntervals C δ hosc hrep
    _ ≤ ∑ p : P, (2 * slack p + 1) := by
      exact Finset.sum_le_sum (fun p _ =>
        card_Icc_sub_add_le_two_mul_add_one
          (StackBadCount F C δ (rep p)) (slack p))

/-- Uniform-slack form of the same image-size pressure. -/
theorem stackBadCountImage_card_le_profileCard_mul_uniformOscillationSlack
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hosc : ProfileFiberOscillationBounded F C δ profile slack)
    (hrep : ProfileRepresentativeInFiber profile rep)
    {S : ℕ} (hslack : ∀ p : P, slack p ≤ S) :
    (StackBadCountImage F C δ).card ≤ Fintype.card P * (2 * S + 1) := by
  calc
    (StackBadCountImage F C δ).card ≤ ∑ p : P, (2 * slack p + 1) :=
      stackBadCountImage_card_le_sum_profileFiberOscillationSlack C δ hosc hrep
    _ ≤ ∑ p : P, (2 * S + 1) := by
      exact Finset.sum_le_sum (fun p _ => by
        have hp : slack p ≤ S := hslack p
        omega)
    _ = Fintype.card P * (2 * S + 1) := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- Refutation socket using only the summed slack budget. -/
theorem not_profileFiberOscillationBounded_of_sum_slack_lt_stackBadCountImage
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hrep : ProfileRepresentativeInFiber profile rep)
    (hsmall : (∑ p : P, (2 * slack p + 1)) < (StackBadCountImage F C δ).card) :
    ¬ ProfileFiberOscillationBounded F C δ profile slack := by
  intro hosc
  exact (not_lt_of_ge
    (stackBadCountImage_card_le_sum_profileFiberOscillationSlack
      C δ hosc hrep)) hsmall

/-- Uniform-slack refutation socket: too few profiles times too little slack cannot explain all
realized bad-count values. -/
theorem not_profileFiberOscillationBounded_of_profileCard_mul_uniformSlack_lt_stackBadCountImage
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hrep : ProfileRepresentativeInFiber profile rep)
    {S : ℕ} (hslack : ∀ p : P, slack p ≤ S)
    (hsmall : Fintype.card P * (2 * S + 1) < (StackBadCountImage F C δ).card) :
    ¬ ProfileFiberOscillationBounded F C δ profile slack := by
  intro hosc
  exact (not_lt_of_ge
    (stackBadCountImage_card_le_profileCard_mul_uniformOscillationSlack
      C δ hosc hrep hslack)) hsmall

/-- Bundled-certificate form of the summed-slack image-size pressure. -/
theorem stackBadCountImage_card_le_sum_profileFiberOscillationCertificateSlack
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ} {B : ℕ}
    (hcert : ProfileFiberOscillationCertificate F C δ profile rep slack B) :
    (StackBadCountImage F C δ).card ≤ ∑ p : P, (2 * slack p + 1) :=
  stackBadCountImage_card_le_sum_profileFiberOscillationSlack C δ hcert.2.1 hcert.1

/-- Bundled-certificate form of the uniform-slack image-size pressure. -/
theorem stackBadCountImage_card_le_profileCard_mul_uniformOscillationCertificateSlack
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ} {B : ℕ}
    (hcert : ProfileFiberOscillationCertificate F C δ profile rep slack B)
    {S : ℕ} (hslack : ∀ p : P, slack p ≤ S) :
    (StackBadCountImage F C δ).card ≤ Fintype.card P * (2 * S + 1) :=
  stackBadCountImage_card_le_profileCard_mul_uniformOscillationSlack
    C δ hcert.2.1 hcert.1 hslack

/-- Certificate-level refutation socket using only the summed slack budget. -/
theorem not_profileFiberOscillationCertificate_of_sum_slack_lt_stackBadCountImage
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ} {B : ℕ}
    (hsmall : (∑ p : P, (2 * slack p + 1)) < (StackBadCountImage F C δ).card) :
    ¬ ProfileFiberOscillationCertificate F C δ profile rep slack B := by
  intro hcert
  exact (not_lt_of_ge
    (stackBadCountImage_card_le_sum_profileFiberOscillationCertificateSlack
      C δ hcert)) hsmall

/-- Certificate-level refutation socket using a uniform slack cap. -/
theorem not_profileFiberOscillationCertificate_of_profileCard_mul_uniformSlack_lt_stackBadCountImage
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ} {B : ℕ}
    {S : ℕ} (hslack : ∀ p : P, slack p ≤ S)
    (hsmall : Fintype.card P * (2 * S + 1) < (StackBadCountImage F C δ).card) :
    ¬ ProfileFiberOscillationCertificate F C δ profile rep slack B := by
  intro hcert
  exact (not_lt_of_ge
    (stackBadCountImage_card_le_profileCard_mul_uniformOscillationCertificateSlack
      C δ hcert hslack)) hsmall

/-! ## Endpoint sanity checks for coarse profiles -/

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [AddCommGroup A] in
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

/-! ## Identity-profile endpoint -/

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [AddCommGroup A] in
/-- The identity profile with identity representatives and zero slack has the representative in its
own fiber. -/
theorem profileRepresentativeInFiber_identity :
    ProfileRepresentativeInFiber
      (fun u : WordStack A (Fin 2) ι => u)
      (fun u : WordStack A (Fin 2) ι => u) := by
  intro p _hp
  rfl

/-- The identity profile with identity representatives and zero slack trivially satisfies slack
domination. -/
theorem profileFiberSlackDominates_identity_zero
    (C : Set (ι -> A)) (δ : ℝ≥0) :
    ProfileFiberSlackDominates F C δ
      (fun u : WordStack A (Fin 2) ι => u)
      (fun u : WordStack A (Fin 2) ι => u) (fun _ => 0) := by
  intro u
  simp

/-- The identity profile with zero slack has zero same-fiber oscillation: same profile means the
same stack. -/
theorem profileFiberOscillationBounded_identity_zero
    (C : Set (ι -> A)) (δ : ℝ≥0) :
    ProfileFiberOscillationBounded F C δ
      (fun u : WordStack A (Fin 2) ι => u) (fun _ => 0) := by
  intro u v hsame
  change u = v at hsame
  cases hsame
  simp

/-- For the identity profile with zero slack, slack budgeting is exactly the original all-stack
worst-case incidence bound.  Thus the finest profile recreates the target theorem pointwise. -/
theorem profileFiberSlackBudgeted_identity_zero_iff_worstCaseIncidenceBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ} :
    ProfileFiberSlackBudgeted F C δ
        (fun u : WordStack A (Fin 2) ι => u)
        (fun u : WordStack A (Fin 2) ι => u) (fun _ => 0) B ↔
      ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  constructor
  · intro hbudget u
    simpa [StackBadCount] using hbudget u ⟨u, rfl⟩
  · intro hbound u _hu
    simpa [StackBadCount] using hbound u

/-- The identity/zero-slack certificate is equivalent to the original worst-case incidence bound. -/
theorem profileFiberSlackCertificate_identity_zero_iff_worstCaseIncidenceBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ} :
    ProfileFiberSlackCertificate F C δ
        (fun u : WordStack A (Fin 2) ι => u)
        (fun u : WordStack A (Fin 2) ι => u) (fun _ => 0) B ↔
      ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  constructor
  · intro hcert u
    have hle : StackBadCount F C δ u ≤ B :=
      le_trans (hcert.1 u) (hcert.2 u ⟨u, rfl⟩)
    simpa [StackBadCount] using hle
  · intro hbound
    exact ⟨profileFiberSlackDominates_identity_zero C δ,
      (profileFiberSlackBudgeted_identity_zero_iff_worstCaseIncidenceBounded C δ).mpr hbound⟩

/-- The structured identity/zero-slack oscillation certificate is also equivalent to the original
worst-case incidence bound. -/
theorem profileFiberOscillationCertificate_identity_zero_iff_worstCaseIncidenceBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ} :
    ProfileFiberOscillationCertificate F C δ
        (fun u : WordStack A (Fin 2) ι => u)
        (fun u : WordStack A (Fin 2) ι => u) (fun _ => 0) B ↔
      ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  constructor
  · intro hcert u
    have hdom : ProfileFiberSlackDominates F C δ
        (fun u : WordStack A (Fin 2) ι => u)
        (fun u : WordStack A (Fin 2) ι => u) (fun _ => 0) :=
      profileFiberSlackDominates_of_fiberOscillation C δ hcert.2.1 hcert.1
    have hle : StackBadCount F C δ u ≤ B :=
      le_trans (hdom u) (hcert.2.2 u ⟨u, rfl⟩)
    simpa [StackBadCount] using hle
  · intro hbound
    exact ⟨profileRepresentativeInFiber_identity,
      profileFiberOscillationBounded_identity_zero C δ,
      (profileFiberSlackBudgeted_identity_zero_iff_worstCaseIncidenceBounded C δ).mpr hbound⟩

/-! ## Injective-profile endpoint -/

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [AddCommGroup A] in
/-- If the profile map is injective and representatives lie in used fibers, the selected
representative of `profile u` is exactly `u`.  Thus an injective profile is only a relabeling of the
stack universe. -/
theorem rep_profile_eq_of_injective
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hinj : Function.Injective profile)
    (hrep : ProfileRepresentativeInFiber profile rep)
    (u : WordStack A (Fin 2) ι) :
    rep (profile u) = u :=
  hinj (hrep (profile u) ⟨u, rfl⟩)

/-- An injective profile has zero same-fiber oscillation: equal profiles force equal stacks. -/
theorem profileFiberOscillationBounded_zero_of_injective
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    (hinj : Function.Injective profile) :
    ProfileFiberOscillationBounded F C δ profile (fun _ => 0) := by
  intro u v hsame
  have huv : u = v := hinj hsame
  cases huv
  simp

/-- An injective profile with representatives in their fibers trivially satisfies zero-slack
domination. -/
theorem profileFiberSlackDominates_zero_of_injective
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hinj : Function.Injective profile)
    (hrep : ProfileRepresentativeInFiber profile rep) :
    ProfileFiberSlackDominates F C δ profile rep (fun _ => 0) := by
  intro u
  have hrep_u : rep (profile u) = u :=
    rep_profile_eq_of_injective hinj hrep u
  simp [hrep_u]

/-- For an injective profile with zero slack, used-profile budgeting is exactly the original
all-stack worst-case incidence bound.  The profile is fine enough that it has not reduced the
target theorem. -/
theorem profileFiberSlackBudgeted_zero_iff_worstCaseIncidenceBounded_of_injective
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hinj : Function.Injective profile)
    (hrep : ProfileRepresentativeInFiber profile rep) :
    ProfileFiberSlackBudgeted F C δ profile rep (fun _ => 0) B ↔
      ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  constructor
  · intro hbudget u
    have hrep_u : rep (profile u) = u :=
      rep_profile_eq_of_injective hinj hrep u
    have hb : StackBadCount F C δ u ≤ B := by
      have hbudget_u : StackBadCount F C δ (rep (profile u)) ≤ B := by
        simpa using hbudget (profile u) ⟨u, rfl⟩
      simpa [hrep_u] using hbudget_u
    simpa [StackBadCount] using hb
  · intro hbound p _hp
    simpa [StackBadCount] using hbound (rep p)

/-- The zero-slack certificate for an injective profile is equivalent to the original open-core
incidence hypothesis. -/
theorem profileFiberSlackCertificate_zero_iff_worstCaseIncidenceBounded_of_injective
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hinj : Function.Injective profile)
    (hrep : ProfileRepresentativeInFiber profile rep) :
    ProfileFiberSlackCertificate F C δ profile rep (fun _ => 0) B ↔
      ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  constructor
  · intro hcert u
    have hle : StackBadCount F C δ u ≤ B :=
      le_trans (hcert.1 u) (hcert.2 (profile u) ⟨u, rfl⟩)
    simpa [StackBadCount] using hle
  · intro hbound
    exact ⟨profileFiberSlackDominates_zero_of_injective C δ hinj hrep,
      (profileFiberSlackBudgeted_zero_iff_worstCaseIncidenceBounded_of_injective
        C δ hinj hrep).mpr hbound⟩

/-- The structured zero-slack oscillation certificate for an injective profile is also equivalent
to the original open-core incidence hypothesis. -/
theorem profileFiberOscillationCertificate_zero_iff_worstCaseIncidenceBounded_of_injective
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hinj : Function.Injective profile)
    (hrep : ProfileRepresentativeInFiber profile rep) :
    ProfileFiberOscillationCertificate F C δ profile rep (fun _ => 0) B ↔
      ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  constructor
  · intro hcert u
    have hdom : ProfileFiberSlackDominates F C δ profile rep (fun _ => 0) :=
      profileFiberSlackDominates_of_fiberOscillation C δ hcert.2.1 hcert.1
    have hle : StackBadCount F C δ u ≤ B :=
      le_trans (hdom u) (hcert.2.2 (profile u) ⟨u, rfl⟩)
    simpa [StackBadCount] using hle
  · intro hbound
    exact ⟨hrep, profileFiberOscillationBounded_zero_of_injective C δ hinj,
      (profileFiberSlackBudgeted_zero_iff_worstCaseIncidenceBounded_of_injective
        C δ hinj hrep).mpr hbound⟩

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
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileBadCountFiberConstant_of_zero_oscillation
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberOscillationBounded_zero_of_profileBadCountFiberConstant
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberOscillationBounded_zero_iff_profileBadCountFiberConstant
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileBadCountRepresented_of_profileBadCountFiberConstant
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileBadCountFiberConstant_of_profileBadCountRepresented
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileBadCountRepresented_iff_profileBadCountFiberConstant_of_repInFiber
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileBadCountRepresented_of_zero_oscillation
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberOscillationBounded_zero_of_profileBadCountRepresented
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberOscillationBounded_zero_iff_profileBadCountRepresented_of_repInFiber
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.worstCaseIncidenceBounded_of_profileBadCountRepresented_budget
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.deltaStar_pin_of_profileBadCountRepresented_budget
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.worstCaseIncidenceBounded_of_profileBadCountFiberConstant_budget
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.deltaStar_pin_of_profileBadCountFiberConstant_budget
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberOscillationCertificate_zero_iff_profileBadCountRepresented_and_budget
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileBadCountFiberConstant_iff_exists_sameProfile_count_ne
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileBadCountRepresented_iff_exists_stack_count_ne
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileBadCountRepresented_and_zeroBudgeted_iff_exists_factor_miss_or_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.BadCountInjectiveOn
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profile_injOn_of_profileBadCountFiberConstant_of_badCountInjectiveOn
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.card_le_profileCard_of_profileBadCountFiberConstant_badCountInjectiveOn
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileBadCountFiberConstant_of_profileCard_lt_badCountInjectiveOn
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileBadCountRepresented_of_profileCard_lt_badCountInjectiveOn
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberOscillationBounded_zero_of_profileCard_lt_badCountInjectiveOn
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.StackBadCountImage
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.stackBadCountImage_card_le_profileCard_of_profileBadCountFiberConstant
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileBadCountFiberConstant_of_profileCard_lt_stackBadCountImage
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileBadCountRepresented_of_profileCard_lt_stackBadCountImage
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberOscillationBounded_zero_of_profileCard_lt_stackBadCountImage
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.ProfileBadCountImageCovered
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.stackBadCountImage_card_le_sum_profileBadCountCover
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileBadCountImageCovered_of_sum_cover_lt_stackBadCountImage
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileBadCountImageCovered_of_profileFiberSlackDominates
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.stackBadCountImage_card_le_sum_profileFiberSlackDominationCaps
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberSlackDominates_of_sum_capIntervalCard_lt_stackBadCountImage
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.stackBadCountImage_card_le_budget_add_one_of_profileFiberSlack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.stackBadCountImage_card_le_budget_add_one_of_profileFiberSlackCertificate
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberSlackCertificate_of_budget_add_one_lt_stackBadCountImage
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileBadCountImageCovered_of_profileFiberOscillation
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.stackBadCountImage_card_le_sum_profileFiberOscillationIntervals
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberOscillationBounded_of_sum_intervalCard_lt_stackBadCountImage
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.card_Icc_sub_add_le_two_mul_add_one
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.stackBadCountImage_card_le_sum_profileFiberOscillationSlack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.stackBadCountImage_card_le_profileCard_mul_uniformOscillationSlack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberOscillationBounded_of_sum_slack_lt_stackBadCountImage
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberOscillationBounded_of_profileCard_mul_uniformSlack_lt_stackBadCountImage
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.stackBadCountImage_card_le_sum_profileFiberOscillationCertificateSlack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.stackBadCountImage_card_le_profileCard_mul_uniformOscillationCertificateSlack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberOscillationCertificate_of_sum_slack_lt_stackBadCountImage
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberOscillationCertificate_of_profileCard_mul_uniformSlack_lt_stackBadCountImage
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileRepresentativeInFiber_of_constant
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackDominates_constant_iff_forall_le_rep_add_slack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberOscillationBounded_constant_iff_global_pairwise_bound
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.not_profileFiberOscillationBounded_constant_iff_exists_global_pair_exceeds_slack
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileRepresentativeInFiber_identity
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackDominates_identity_zero
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberOscillationBounded_identity_zero
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackBudgeted_identity_zero_iff_worstCaseIncidenceBounded
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackCertificate_identity_zero_iff_worstCaseIncidenceBounded
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberOscillationCertificate_identity_zero_iff_worstCaseIncidenceBounded
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.rep_profile_eq_of_injective
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberOscillationBounded_zero_of_injective
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackDominates_zero_of_injective
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackBudgeted_zero_iff_worstCaseIncidenceBounded_of_injective
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberSlackCertificate_zero_iff_worstCaseIncidenceBounded_of_injective
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberSlackDominance.profileFiberOscillationCertificate_zero_iff_worstCaseIncidenceBounded_of_injective
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
