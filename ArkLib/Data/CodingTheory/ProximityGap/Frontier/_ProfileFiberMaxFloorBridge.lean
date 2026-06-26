/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorClosureContract
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._StackProfileFiberMax

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Profile-fiber maximizers feed the floor closure contract

`_StackProfileFiberMax` proves that exact fiber-max representatives contain a true global
bad-scalar maximizer in its local interface.  `_FloorClosureContract` now consumes exactly that
kind of certificate through `FamilyContainsGlobalMax`.

This file is the composition bridge: a profile/fiber classification proof can now feed the
floor-localization Linnik/TZ contracts without restating the domination theorem.

The preferred finite family is the used-profile image `usedProfileRepFamily profile rep`; the
older full image `(Finset.univ : Finset P).image rep` remains available when a caller has already
budgeted every profile, including unattained ones.

It is not a prize proof.  It packages the remaining obligation:

* exact singleton floor-bad scanner evidence;
* sub-prize least-prime supply;
* floor-goodness budgets the chosen representative family;
* profile representatives are exact fiber maximizers;
* the scaled MCA budget is small enough.
-/

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.FloorLocalization
open ArkLib.ProximityGap.Frontier.FloorLinnikTZClosure

namespace ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The profile values actually attained by some stack. -/
noncomputable def usedProfileFinset {P : Type} [Fintype P]
    (profile : WordStack A (Fin 2) ι -> P) : Finset P := by
  classical
  exact (Finset.univ : Finset P).filter (fun p => StackProfileFiberMax.UsedProfile profile p)

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [AddCommGroup A] in
@[simp] theorem mem_usedProfileFinset {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P} {p : P} :
    p ∈ usedProfileFinset profile ↔ StackProfileFiberMax.UsedProfile profile p := by
  classical
  simp [usedProfileFinset]

/-- The representative family restricted to profiles that actually occur. -/
noncomputable def usedProfileRepFamily {P : Type} [Fintype P]
    (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) :
    Finset (WordStack A (Fin 2) ι) :=
  (usedProfileFinset profile).image rep

omit [Nonempty ι] [DecidableEq ι] [Fintype A] [AddCommGroup A] in
@[simp] theorem mem_usedProfileRepFamily {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    {r : WordStack A (Fin 2) ι} :
    r ∈ usedProfileRepFamily profile rep ↔
      ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧ rep p = r := by
  classical
  simp [usedProfileRepFamily, usedProfileFinset]

/-- Exact profile-fiber representatives give the floor contract's global-max containment
certificate for the image of representatives. -/
theorem floorFamilyContainsGlobalMax_of_profileFiberMaxReps
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hmax : StackProfileFiberMax.ProfileFiberMaxReps F C δ profile rep) :
    FloorClosureContract.FamilyContainsGlobalMax F C δ
      ((Finset.univ : Finset P).image rep) := by
  rcases StackProfileFiberMax.exists_usedProfile_stackDominates_of_profileFiberMaxReps
      (F := F) (A := A) C δ hmax with
    ⟨p, _hused, hdom⟩
  refine ⟨rep p, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩, ?_⟩
  intro u
  simpa [FloorClosureContract.StackBadCount, StackProfileFiberMax.StackBadCount] using hdom u

/-- Exact profile-fiber representatives give the floor contract's global-max containment
certificate for the image of representatives of used profiles only. -/
theorem floorFamilyContainsGlobalMax_of_profileFiberMaxReps_usedProfileFamily
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hmax : StackProfileFiberMax.ProfileFiberMaxReps F C δ profile rep) :
    FloorClosureContract.FamilyContainsGlobalMax F C δ
      (usedProfileRepFamily profile rep) := by
  rcases StackProfileFiberMax.exists_usedProfile_stackDominates_of_profileFiberMaxReps
      (F := F) (A := A) C δ hmax with
    ⟨p, hused, hdom⟩
  refine ⟨rep p, ?_, ?_⟩
  · exact mem_usedProfileRepFamily.mpr ⟨p, hused, rfl⟩
  · intro u
    simpa [FloorClosureContract.StackBadCount, StackProfileFiberMax.StackBadCount] using hdom u

/-- Scanner-to-floor bridge.  If no used profile has an outside representative or a same-profile
beating witness, then the representative image contains a floor-contract global maximizer. -/
theorem floorFamilyContainsGlobalMax_of_no_bad_used_profile
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hno : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackProfileFiberMax.StackBadCount F C δ (rep p) <
            StackProfileFiberMax.StackBadCount F C δ u)) :
    FloorClosureContract.FamilyContainsGlobalMax F C δ
      ((Finset.univ : Finset P).image rep) :=
  floorFamilyContainsGlobalMax_of_profileFiberMaxReps C δ
    ((StackProfileFiberMax.profileFiberMaxReps_iff_no_bad_used_profile C δ).mpr hno)

/-- Scanner-to-floor bridge for the used-profile representative family. -/
theorem floorFamilyContainsGlobalMax_of_no_bad_used_profile_usedProfileFamily
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hno : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackProfileFiberMax.StackBadCount F C δ (rep p) <
            StackProfileFiberMax.StackBadCount F C δ u)) :
    FloorClosureContract.FamilyContainsGlobalMax F C δ
      (usedProfileRepFamily profile rep) :=
  floorFamilyContainsGlobalMax_of_profileFiberMaxReps_usedProfileFamily C δ
    ((StackProfileFiberMax.profileFiberMaxReps_iff_no_bad_used_profile C δ).mpr hno)

/-- If every profile representative is beaten by some stack, the full representative image cannot
contain a global maximizer in the floor contract.  This stronger refutation checks all profiles,
including unused ones, because the finite image contains `rep p` for every `p : P`. -/
theorem not_floorFamilyContainsGlobalMax_of_each_profile_rep_beaten
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {rep : P -> WordStack A (Fin 2) ι}
    (hbeat : ∀ p : P, ∃ u : WordStack A (Fin 2) ι,
      FloorClosureContract.StackBadCount F C δ (rep p) <
        FloorClosureContract.StackBadCount F C δ u) :
    ¬ FloorClosureContract.FamilyContainsGlobalMax F C δ
      ((Finset.univ : Finset P).image rep) := by
  intro hcontains
  rcases hcontains with ⟨r, hr, hdom⟩
  rcases Finset.mem_image.mp hr with ⟨p, _hp, rfl⟩
  rcases hbeat p with ⟨u, hlt⟩
  exact (not_lt_of_ge (hdom u)) hlt

/-- If every used profile representative is beaten by some stack, then the used-profile
representative family cannot contain a global maximizer in the floor contract. -/
theorem not_floorFamilyContainsGlobalMax_of_each_used_profile_rep_beaten
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hbeat : ∀ p : P, StackProfileFiberMax.UsedProfile profile p →
      ∃ u : WordStack A (Fin 2) ι,
        FloorClosureContract.StackBadCount F C δ (rep p) <
          FloorClosureContract.StackBadCount F C δ u) :
    ¬ FloorClosureContract.FamilyContainsGlobalMax F C δ
      (usedProfileRepFamily profile rep) := by
  intro hcontains
  rcases hcontains with ⟨r, hr, hdom⟩
  rcases mem_usedProfileRepFamily.mp hr with ⟨p, hused, rfl⟩
  rcases hbeat p hused with ⟨u, hlt⟩
  exact (not_lt_of_ge (hdom u)) hlt

/-- Exact refutation certificate for the used-profile representative family. -/
theorem not_floorFamilyContainsGlobalMax_usedProfileFamily_iff_each_used_rep_beaten
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} :
    (¬ FloorClosureContract.FamilyContainsGlobalMax F C δ
      (usedProfileRepFamily profile rep)) ↔
      ∀ p : P, StackProfileFiberMax.UsedProfile profile p →
        ∃ u : WordStack A (Fin 2) ι,
          FloorClosureContract.StackBadCount F C δ (rep p) <
            FloorClosureContract.StackBadCount F C δ u := by
  constructor
  · intro hno p hused
    have hbeat :=
      (FloorClosureContract.not_familyContainsGlobalMax_iff_each_member_beaten
        (F := F) (A := A) C δ (usedProfileRepFamily profile rep)).mp hno
    exact hbeat (rep p) (mem_usedProfileRepFamily.mpr ⟨p, hused, rfl⟩)
  · intro hbeat
    exact not_floorFamilyContainsGlobalMax_of_each_used_profile_rep_beaten C δ hbeat

/-- A local scanner certificate that no used profile representative exceeds `B` gives a
floor-contract family budget for the used-profile representative family. -/
theorem familyBounded_of_no_usedProfile_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hnoBudgetBad : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      B < StackProfileFiberMax.StackBadCount F C δ (rep p)) :
    FloorClosureContract.FamilyBounded F C δ (usedProfileRepFamily profile rep) B := by
  intro r hr
  rcases mem_usedProfileRepFamily.mp hr with ⟨p, hused, rfl⟩
  exact le_of_not_gt (fun hgt =>
    hnoBudgetBad ⟨p, hused, by
      simpa [FloorClosureContract.StackBadCount, StackProfileFiberMax.StackBadCount] using hgt⟩)

/-- Exact budget certificate for the used-profile representative family. -/
theorem familyBounded_usedProfileRepFamily_iff_no_usedProfile_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} :
    FloorClosureContract.FamilyBounded F C δ (usedProfileRepFamily profile rep) B ↔
      ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
        B < StackProfileFiberMax.StackBadCount F C δ (rep p) := by
  constructor
  · intro hbounded hbad
    rcases hbad with ⟨p, hused, hgt⟩
    have hle :
        StackProfileFiberMax.StackBadCount F C δ (rep p) ≤ B := by
      simpa [FloorClosureContract.StackBadCount, StackProfileFiberMax.StackBadCount] using
        hbounded (rep p) (mem_usedProfileRepFamily.mpr ⟨p, hused, rfl⟩)
    exact (not_lt_of_ge hle) hgt
  · exact familyBounded_of_no_usedProfile_budget_lt C δ

/-- If a direct scanner already bounds all used-profile representatives, then the floor-good family
budget hypothesis is automatic for the used-profile family.  This is diagnostic: floor-goodness is
not doing the counting work in this degenerate use of the floor lane. -/
theorem floorGoodFamilyBudget_of_no_usedProfile_budget_lt
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hnoBudgetBad : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      B < StackProfileFiberMax.StackBadCount F C δ (rep p)) :
    FloorClosureContract.FloorGoodFamilyBudget
      (F := F) (A := A) FloorBad a C δ (usedProfileRepFamily profile rep) B := by
  intro _hgood
  exact familyBounded_of_no_usedProfile_budget_lt C δ hnoBudgetBad

/-- Exact local form of the floor-good family budget for the used-profile representative family.
The remaining floor-to-count theorem is precisely: once the modeled floor predicate is good at the
field prime, no used profile representative exceeds the target budget. -/
theorem floorGoodFamilyBudget_usedProfileRepFamily_iff_no_usedProfile_budget_lt
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} :
    FloorClosureContract.FloorGoodFamilyBudget
        (F := F) (A := A) FloorBad a C δ (usedProfileRepFamily profile rep) B
      ↔ (¬ FloorBad (2 ^ a) (Fintype.card F) →
        ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
          B < StackProfileFiberMax.StackBadCount F C δ (rep p)) := by
  constructor
  · intro hfloor hgood
    exact (familyBounded_usedProfileRepFamily_iff_no_usedProfile_budget_lt C δ).mp
      (hfloor hgood)
  · intro hlocal hgood
    exact (familyBounded_usedProfileRepFamily_iff_no_usedProfile_budget_lt C δ).mpr
      (hlocal hgood)

/-- A profile-fiber classification plus a floor-good family budget gives the universal incidence
bound.  This is the profile form of the floor contract's max-containment consumer. -/
theorem worstCaseIncidenceBounded_of_profileFiberMax_floorFamilyBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hmax : StackProfileFiberMax.ProfileFiberMaxReps F C δ profile rep)
    (hbounded : FloorClosureContract.FamilyBounded F C δ
      ((Finset.univ : Finset P).image rep) B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  FloorClosureContract.worstCaseIncidenceBounded_of_containsGlobalMax C δ
    (floorFamilyContainsGlobalMax_of_profileFiberMaxReps C δ hmax) hbounded

/-- A profile-fiber classification plus a floor-good budget on the used-profile representative
family gives the universal incidence bound. -/
theorem worstCaseIncidenceBounded_of_profileFiberMax_usedProfileFloorFamilyBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hmax : StackProfileFiberMax.ProfileFiberMaxReps F C δ profile rep)
    (hbounded : FloorClosureContract.FamilyBounded F C δ
      (usedProfileRepFamily profile rep) B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  FloorClosureContract.worstCaseIncidenceBounded_of_containsGlobalMax C δ
    (floorFamilyContainsGlobalMax_of_profileFiberMaxReps_usedProfileFamily C δ hmax) hbounded

/-- Positive scanner form of the profile floor bridge: no local representative failure plus a
floor-good family budget gives the universal incidence bound. -/
theorem worstCaseIncidenceBounded_of_no_bad_used_profile_floorFamilyBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hno : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackProfileFiberMax.StackBadCount F C δ (rep p) <
            StackProfileFiberMax.StackBadCount F C δ u))
    (hbounded : FloorClosureContract.FamilyBounded F C δ
      ((Finset.univ : Finset P).image rep) B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  FloorClosureContract.worstCaseIncidenceBounded_of_containsGlobalMax C δ
    (floorFamilyContainsGlobalMax_of_no_bad_used_profile C δ hno) hbounded

/-- Positive scanner form on the used-profile representative family. -/
theorem worstCaseIncidenceBounded_of_no_bad_used_profile_usedProfileFloorFamilyBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hno : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackProfileFiberMax.StackBadCount F C δ (rep p) <
            StackProfileFiberMax.StackBadCount F C δ u))
    (hbounded : FloorClosureContract.FamilyBounded F C δ
      (usedProfileRepFamily profile rep) B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  FloorClosureContract.worstCaseIncidenceBounded_of_containsGlobalMax C δ
    (floorFamilyContainsGlobalMax_of_no_bad_used_profile_usedProfileFamily C δ hno) hbounded

/-- Fully scanner-facing profile floor closure.  No used profile has an invalid or beaten
representative, and no used representative exceeds `B`; therefore the actual worst-case incidence
count is bounded by `B`. -/
theorem worstCaseIncidenceBounded_of_no_bad_used_profile_budgetScanner
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type}
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackProfileFiberMax.StackBadCount F C δ (rep p) <
            StackProfileFiberMax.StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      B < StackProfileFiberMax.StackBadCount F C δ (rep p)) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  StackProfileFiberMax.worstCaseIncidenceBounded_of_no_bad_used_profile_scanner
    C δ hnoMaxBad hnoBudgetBad

/-- Delta-star consumer for a fully local profile scanner certificate. -/
theorem deltaStar_pin_of_profileScannerBudget
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type}
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackProfileFiberMax.StackBadCount F C δ (rep p) <
            StackProfileFiberMax.StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      B < StackProfileFiberMax.StackBadCount F C δ (rep p))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_no_bad_used_profile_budgetScanner
      C δ hnoMaxBad hnoBudgetBad)
    hbudget

/-- Linnik-form floor closure with profile-fiber representatives as the max-containment certificate. -/
theorem deltaStar_pin_of_linnik_candidateListExactSmallest_profileFiberMaxContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hfloorBudget : FloorClosureContract.FloorGoodFamilyBudget
      (F := F) (A := A) FloorBad a C δ ((Finset.univ : Finset P).image rep) B)
    (hmax : StackProfileFiberMax.ProfileFiberMaxReps F C δ profile rep)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  FloorClosureContract.deltaStar_pin_of_linnik_candidateListExactSmallestMaxContract
    (F := F) (A := A) FloorBad hexact hLeast a ha
    hcardPrime hcardMod hcardPrize C εstar hδ hfloorBudget
    (floorFamilyContainsGlobalMax_of_profileFiberMaxReps C δ hmax) hbudget

/-- Linnik-form floor closure with used-profile representatives as the max-containment certificate. -/
theorem deltaStar_pin_of_linnik_candidateListExactSmallest_usedProfileFiberMaxContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hfloorBudget : FloorClosureContract.FloorGoodFamilyBudget
      (F := F) (A := A) FloorBad a C δ (usedProfileRepFamily profile rep) B)
    (hmax : StackProfileFiberMax.ProfileFiberMaxReps F C δ profile rep)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  FloorClosureContract.deltaStar_pin_of_linnik_candidateListExactSmallestMaxContract
    (F := F) (A := A) FloorBad hexact hLeast a ha
    hcardPrime hcardMod hcardPrize C εstar hδ hfloorBudget
    (floorFamilyContainsGlobalMax_of_profileFiberMaxReps_usedProfileFamily C δ hmax) hbudget

/-- Linnik-form floor closure with the scanner-positive no-bad-used-profile certificate. -/
theorem deltaStar_pin_of_linnik_candidateListExactSmallest_usedProfileScannerContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hfloorBudget : FloorClosureContract.FloorGoodFamilyBudget
      (F := F) (A := A) FloorBad a C δ (usedProfileRepFamily profile rep) B)
    (hno : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackProfileFiberMax.StackBadCount F C δ (rep p) <
            StackProfileFiberMax.StackBadCount F C δ u))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  FloorClosureContract.deltaStar_pin_of_linnik_candidateListExactSmallestMaxContract
    (F := F) (A := A) FloorBad hexact hLeast a ha
    hcardPrime hcardMod hcardPrize C εstar hδ hfloorBudget
    (floorFamilyContainsGlobalMax_of_no_bad_used_profile_usedProfileFamily C δ hno) hbudget

/-- Linnik-form floor closure with only local profile scanner certificates for max-containment and
the used-profile family budget. -/
theorem deltaStar_pin_of_linnik_candidateListExactSmallest_usedProfileBudgetScannerContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} [Finite P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackProfileFiberMax.StackBadCount F C δ (rep p) <
            StackProfileFiberMax.StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      B < StackProfileFiberMax.StackBadCount F C δ (rep p))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  exact
    deltaStar_pin_of_linnik_candidateListExactSmallest_usedProfileScannerContract
      (F := F) (A := A) FloorBad hexact hLeast a ha
      hcardPrime hcardMod hcardPrize C εstar hδ
      (floorGoodFamilyBudget_of_no_usedProfile_budget_lt
        (F := F) (A := A) FloorBad a C δ hnoBudgetBad)
      hnoMaxBad hbudget

/-- No-laundering form of the Linnik profile-budget scanner contract.  Once the scanner already
proves max-containment and the used-profile budget, the delta-star pin follows directly from the
local scanner theorem; Linnik/floor-localization inputs are not the source of the counting bound. -/
theorem deltaStar_pin_of_profileBudgetScanner_of_linnikInputs
    (FloorBad : ℕ -> ℕ -> Prop)
    (_hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (_hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (_ha : 4 ≤ a)
    (_hcardPrime : (Fintype.card F).Prime)
    (_hcardMod : Fintype.card F % (2 ^ a) = 1)
    (_hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type}
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackProfileFiberMax.StackBadCount F C δ (rep p) <
            StackProfileFiberMax.StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      B < StackProfileFiberMax.StackBadCount F C δ (rep p))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_profileScannerBudget C εstar hδ hnoMaxBad hnoBudgetBad hbudget

/-- TZ-form floor closure with profile-fiber representatives as the max-containment certificate. -/
theorem deltaStar_pin_of_tz_candidateListExactSmallest_profileFiberMaxContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hfloorBudget : FloorClosureContract.FloorGoodFamilyBudget
      (F := F) (A := A) FloorBad a C δ ((Finset.univ : Finset P).image rep) B)
    (hmax : StackProfileFiberMax.ProfileFiberMaxReps F C δ profile rep)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  FloorClosureContract.deltaStar_pin_of_tz_candidateListExactSmallestMaxContract
    (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
    hcardPrime hcardMod hcardPrize C εstar hδ hfloorBudget
    (floorFamilyContainsGlobalMax_of_profileFiberMaxReps C δ hmax) hbudget

/-- TZ-form floor closure with used-profile representatives as the max-containment certificate. -/
theorem deltaStar_pin_of_tz_candidateListExactSmallest_usedProfileFiberMaxContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hfloorBudget : FloorClosureContract.FloorGoodFamilyBudget
      (F := F) (A := A) FloorBad a C δ (usedProfileRepFamily profile rep) B)
    (hmax : StackProfileFiberMax.ProfileFiberMaxReps F C δ profile rep)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  FloorClosureContract.deltaStar_pin_of_tz_candidateListExactSmallestMaxContract
    (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
    hcardPrime hcardMod hcardPrize C εstar hδ hfloorBudget
    (floorFamilyContainsGlobalMax_of_profileFiberMaxReps_usedProfileFamily C δ hmax) hbudget

/-- TZ-form floor closure with the scanner-positive no-bad-used-profile certificate. -/
theorem deltaStar_pin_of_tz_candidateListExactSmallest_usedProfileScannerContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hfloorBudget : FloorClosureContract.FloorGoodFamilyBudget
      (F := F) (A := A) FloorBad a C δ (usedProfileRepFamily profile rep) B)
    (hno : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackProfileFiberMax.StackBadCount F C δ (rep p) <
            StackProfileFiberMax.StackBadCount F C δ u))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  FloorClosureContract.deltaStar_pin_of_tz_candidateListExactSmallestMaxContract
    (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
    hcardPrime hcardMod hcardPrize C εstar hδ hfloorBudget
    (floorFamilyContainsGlobalMax_of_no_bad_used_profile_usedProfileFamily C δ hno) hbudget

/-- TZ-form floor closure with only local profile scanner certificates for max-containment and the
used-profile family budget. -/
theorem deltaStar_pin_of_tz_candidateListExactSmallest_usedProfileBudgetScannerContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} [Finite P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackProfileFiberMax.StackBadCount F C δ (rep p) <
            StackProfileFiberMax.StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      B < StackProfileFiberMax.StackBadCount F C δ (rep p))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  exact
    deltaStar_pin_of_tz_candidateListExactSmallest_usedProfileScannerContract
      (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
      hcardPrime hcardMod hcardPrize C εstar hδ
      (floorGoodFamilyBudget_of_no_usedProfile_budget_lt
        (F := F) (A := A) FloorBad a C δ hnoBudgetBad)
      hnoMaxBad hbudget

/-- No-laundering form of the TZ profile-budget scanner contract. -/
theorem deltaStar_pin_of_profileBudgetScanner_of_tzInputs
    (FloorBad : ℕ -> ℕ -> Prop)
    (_hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (_hβ : β ≤ 3)
    (_hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (_ha : 4 ≤ a)
    (_hcardPrime : (Fintype.card F).Prime)
    (_hcardMod : Fintype.card F % (2 ^ a) = 1)
    (_hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type}
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackProfileFiberMax.StackBadCount F C δ (rep p) <
            StackProfileFiberMax.StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ p : P, StackProfileFiberMax.UsedProfile profile p ∧
      B < StackProfileFiberMax.StackBadCount F C δ (rep p))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_profileScannerBudget C εstar hδ hnoMaxBad hnoBudgetBad hbudget

end ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.floorFamilyContainsGlobalMax_of_profileFiberMaxReps
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.floorFamilyContainsGlobalMax_of_profileFiberMaxReps_usedProfileFamily
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.floorFamilyContainsGlobalMax_of_no_bad_used_profile
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.floorFamilyContainsGlobalMax_of_no_bad_used_profile_usedProfileFamily
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.not_floorFamilyContainsGlobalMax_of_each_profile_rep_beaten
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.not_floorFamilyContainsGlobalMax_of_each_used_profile_rep_beaten
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.not_floorFamilyContainsGlobalMax_usedProfileFamily_iff_each_used_rep_beaten
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.familyBounded_of_no_usedProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.familyBounded_usedProfileRepFamily_iff_no_usedProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.floorGoodFamilyBudget_of_no_usedProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.floorGoodFamilyBudget_usedProfileRepFamily_iff_no_usedProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.worstCaseIncidenceBounded_of_profileFiberMax_floorFamilyBounded
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.worstCaseIncidenceBounded_of_profileFiberMax_usedProfileFloorFamilyBounded
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.worstCaseIncidenceBounded_of_no_bad_used_profile_floorFamilyBounded
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.worstCaseIncidenceBounded_of_no_bad_used_profile_usedProfileFloorFamilyBounded
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.worstCaseIncidenceBounded_of_no_bad_used_profile_budgetScanner
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.deltaStar_pin_of_profileScannerBudget
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.deltaStar_pin_of_linnik_candidateListExactSmallest_profileFiberMaxContract
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.deltaStar_pin_of_linnik_candidateListExactSmallest_usedProfileFiberMaxContract
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.deltaStar_pin_of_linnik_candidateListExactSmallest_usedProfileScannerContract
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.deltaStar_pin_of_linnik_candidateListExactSmallest_usedProfileBudgetScannerContract
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.deltaStar_pin_of_profileBudgetScanner_of_linnikInputs
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.deltaStar_pin_of_tz_candidateListExactSmallest_profileFiberMaxContract
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.deltaStar_pin_of_tz_candidateListExactSmallest_usedProfileFiberMaxContract
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.deltaStar_pin_of_tz_candidateListExactSmallest_usedProfileScannerContract
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.deltaStar_pin_of_tz_candidateListExactSmallest_usedProfileBudgetScannerContract
#print axioms ArkLib.ProximityGap.Frontier.ProfileFiberMaxFloorBridge.deltaStar_pin_of_profileBudgetScanner_of_tzInputs
