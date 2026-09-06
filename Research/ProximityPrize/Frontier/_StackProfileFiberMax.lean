/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

/-!
# Profile fibers have exact maximizers

`_StackProfileDominationInterface` says that a classification proof may work by assigning each stack
to a profile and proving a cap for every profile.  This file makes the hidden target explicit:
for any profile value that is actually used, the finite fiber of stacks with that profile has a true
bad-scalar maximizer.

Consequently, a profile classification proves `WorstCaseIncidenceBounded C δ B` exactly when the
maximizer in every used profile fiber is bounded by `B`.  A binder/floor representative for a
profile is sufficient only if it is such a fiber maximizer, or at least dominates that fiber.

The refutation API is local: a single stack in the same profile with a larger bad-scalar count kills
the claim that the chosen representative is the profile-fiber maximizer.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.StackProfileFiberMax

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

/-- A stack dominates if it attains the global maximum of the bad-scalar count. -/
def StackDominates (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (uMax : WordStack A (Fin 2) ι) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    StackBadCount K C δ u ≤ StackBadCount K C δ uMax

/-- Every representative in a finite family satisfies the one-stack budget. -/
def FamilyBounded (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) : Prop :=
  ∀ r ∈ R, StackBounded K C δ r B

/-- A finite family dominates if every stack is bounded by one representative's bad-scalar count. -/
def FamilyDominates (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    ∃ r ∈ R, StackBadCount K C δ u ≤ StackBadCount K C δ r

/-- The profile value is actually attained by at least one stack. -/
def UsedProfile {P : Type}
    (profile : WordStack A (Fin 2) ι -> P) (p : P) : Prop :=
  ∃ u : WordStack A (Fin 2) ι, profile u = p

/-- The finite fiber of stacks with profile `p`. -/
noncomputable def profileFiber {P : Type}
    (profile : WordStack A (Fin 2) ι -> P) (p : P) :
    Finset (WordStack A (Fin 2) ι) := by
  classical
  exact Finset.univ.filter (fun u => profile u = p)

omit [Nonempty ι] [DecidableEq A] [AddCommGroup A] [Module F A] in
@[simp] theorem mem_profileFiber {P : Type}
    {profile : WordStack A (Fin 2) ι -> P} {p : P}
    {u : WordStack A (Fin 2) ι} :
    u ∈ profileFiber profile p ↔ profile u = p := by
  classical
  simp [profileFiber]

/-- `uMax` is a bad-scalar maximizer inside the profile fiber `p`. -/
def ProfileFiberMax (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (profile : WordStack A (Fin 2) ι -> P) (p : P)
    (uMax : WordStack A (Fin 2) ι) : Prop :=
  profile uMax = p
    ∧ ∀ u : WordStack A (Fin 2) ι, profile u = p →
      StackBadCount K C δ u ≤ StackBadCount K C δ uMax

/-- A profile-indexed representative function chooses a fiber maximizer for every used profile. -/
def ProfileFiberMaxReps (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) : Prop :=
  ∀ p : P, UsedProfile profile p → ProfileFiberMax K C δ profile p (rep p)

/-- The fiber-max representatives for used profiles are all within budget. -/
def ProfileFiberMaxesBounded (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (B : ℕ) : Prop :=
  ∀ p : P, UsedProfile profile p → StackBounded K C δ (rep p) B

/-- Every used profile fiber has an exact bad-scalar maximizer. -/
theorem exists_profileFiberMax_of_used
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type}
    {profile : WordStack A (Fin 2) ι -> P} {p : P}
    (hused : UsedProfile profile p) :
    ∃ uMax : WordStack A (Fin 2) ι, ProfileFiberMax F C δ profile p uMax := by
  classical
  rcases hused with ⟨u₀, hu₀⟩
  have hfiber : (profileFiber (A := A) profile p).Nonempty :=
    ⟨u₀, by simp [profileFiber, hu₀]⟩
  obtain ⟨uMax, huMax, hmax⟩ :=
    (profileFiber (A := A) profile p).exists_max_image
      (fun u : WordStack A (Fin 2) ι => StackBadCount F C δ u) hfiber
  refine ⟨uMax, ?_, ?_⟩
  · exact (mem_profileFiber.mp huMax)
  · intro u hu
    exact hmax u (mem_profileFiber.mpr hu)

/-- Fiber-max representatives dominate their own profile fibers. -/
theorem stackBadCount_le_profileFiberMaxRep
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hmax : ProfileFiberMaxReps F C δ profile rep)
    (u : WordStack A (Fin 2) ι) :
    StackBadCount F C δ u ≤ StackBadCount F C δ (rep (profile u)) := by
  exact (hmax (profile u) ⟨u, rfl⟩).2 u rfl

/-- Fiber-max representatives within budget give the full worst-case incidence hypothesis. -/
theorem worstCaseIncidenceBounded_of_profileFiberMaxesBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hmax : ProfileFiberMaxReps F C δ profile rep)
    (hbounded : ProfileFiberMaxesBounded F C δ profile rep B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro u
  exact le_trans (stackBadCount_le_profileFiberMaxRep C δ hmax u)
    (hbounded (profile u) ⟨u, rfl⟩)

/-- Under chosen fiber maximizers, the universal incidence bound is equivalent to bounding every
used profile's fiber maximum. -/
theorem worstCaseIncidenceBounded_iff_profileFiberMaxesBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hmax : ProfileFiberMaxReps F C δ profile rep) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B
      ↔ ProfileFiberMaxesBounded F C δ profile rep B :=
  ⟨fun hI p _hused => hI (rep p),
    fun hbounded => worstCaseIncidenceBounded_of_profileFiberMaxesBounded C δ hmax hbounded⟩

/-- If the profile space is finite, profile-fiber maximizers form a finite dominating family. -/
theorem familyDominates_of_profileFiberMaxReps
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hmax : ProfileFiberMaxReps F C δ profile rep) :
    FamilyDominates F C δ ((Finset.univ : Finset P).image rep) := by
  intro u
  refine ⟨rep (profile u), ?_, stackBadCount_le_profileFiberMaxRep C δ hmax u⟩
  exact Finset.mem_image.mpr ⟨profile u, Finset.mem_univ _, rfl⟩

/-- Exact fiber-max representatives contain a true global maximizer.  Pick a global maximizer
`uMax`; the representative of its profile dominates `uMax`'s fiber, hence has bad-scalar count at
least `uMax`, and therefore dominates every stack. -/
theorem exists_usedProfile_stackDominates_of_profileFiberMaxReps
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hmax : ProfileFiberMaxReps F C δ profile rep) :
    ∃ p : P, UsedProfile profile p ∧ StackDominates F C δ (rep p) := by
  classical
  obtain ⟨uMax, hglobal⟩ :=
    Finite.exists_max (fun u : WordStack A (Fin 2) ι => StackBadCount F C δ u)
  refine ⟨profile uMax, ⟨uMax, rfl⟩, ?_⟩
  intro u
  exact le_trans (hglobal u) ((hmax (profile uMax) ⟨uMax, rfl⟩).2 uMax rfl)

/-- If every selected representative of a used profile is beaten by some stack, then the selected
representatives cannot be exact profile-fiber maximizers.  This is the profile version of the
memberwise beating refutation used in the floor contract. -/
theorem not_profileFiberMaxReps_of_each_used_rep_beaten
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hbeat : ∀ p : P, UsedProfile profile p →
      ∃ u : WordStack A (Fin 2) ι,
        StackBadCount F C δ (rep p) < StackBadCount F C δ u) :
    ¬ ProfileFiberMaxReps F C δ profile rep := by
  intro hmax
  rcases exists_usedProfile_stackDominates_of_profileFiberMaxReps C δ hmax with
    ⟨p, hused, hdom⟩
  rcases hbeat p hused with ⟨u, hlt⟩
  exact (not_lt_of_ge (hdom u)) hlt

/-- A finite family of bounded profile-fiber maximizers gives the universal incidence bound. -/
theorem worstCaseIncidenceBounded_of_profileFiberMaxFamilyBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} [Fintype P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hmax : ProfileFiberMaxReps F C δ profile rep)
    (hbounded : FamilyBounded F C δ ((Finset.univ : Finset P).image rep) B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro u
  have hmem : rep (profile u) ∈ ((Finset.univ : Finset P).image rep) :=
    Finset.mem_image.mpr ⟨profile u, Finset.mem_univ _, rfl⟩
  exact le_trans (stackBadCount_le_profileFiberMaxRep C δ hmax u)
    (hbounded (rep (profile u)) hmem)

/-- If the profile map is constant, a fiber maximizer for that profile is a global stack maximizer.
Coarse profiles do not create a smaller theorem; they collapse back to the global maximum. -/
theorem stackDominates_of_profileFiberMax_constant
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P} {p₀ : P}
    {uMax : WordStack A (Fin 2) ι}
    (hconst : ∀ u : WordStack A (Fin 2) ι, profile u = p₀)
    (hmax : ProfileFiberMax F C δ profile p₀ uMax) :
    StackDominates F C δ uMax := by
  intro u
  exact hmax.2 u (hconst u)

/-- The identity profile has the tautological fiber-max representative: each stack represents its
own singleton fiber.  Fully fine profiles do not create a smaller theorem; they restate the
all-stack obligation. -/
theorem profileFiberMaxReps_identity
    (C : Set (ι -> A)) (δ : ℝ≥0) :
    ProfileFiberMaxReps F C δ
      (fun u : WordStack A (Fin 2) ι => u)
      (fun u : WordStack A (Fin 2) ι => u) := by
  intro p _hused
  refine ⟨rfl, ?_⟩
  intro u hu
  simp [hu]

/-- For the identity profile, bounding the chosen fiber maximizers is exactly the original
universal incidence bound. -/
theorem profileFiberMaxesBounded_identity_iff_worstCaseIncidenceBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) (B : ℕ) :
    ProfileFiberMaxesBounded F C δ
        (fun u : WordStack A (Fin 2) ι => u)
        (fun u : WordStack A (Fin 2) ι => u) B
      ↔ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
          (F := F) (A := A) C δ B := by
  constructor
  · intro hbounded u
    exact hbounded u ⟨u, rfl⟩
  · intro hI u _hused
    exact hI u

/-- Delta-star consumer for profile-fiber maximizers. -/
theorem deltaStar_pin_of_profileFiberMaxesBounded
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hmax : ProfileFiberMaxReps F C δ profile rep)
    (hbounded : ProfileFiberMaxesBounded F C δ profile rep B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_profileFiberMaxesBounded C δ hmax hbounded)
    hbudget

/-! ## Refutation APIs -/

/-- A same-profile stack with a larger bad-scalar count refutes the proposed fiber maximizer. -/
theorem not_profileFiberMax_of_sameProfile_strictly_larger
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P} {p : P}
    {uCand uWitness : WordStack A (Fin 2) ι}
    (hwitness : profile uWitness = p)
    (hgt : StackBadCount F C δ uCand < StackBadCount F C δ uWitness) :
    ¬ ProfileFiberMax F C δ profile p uCand := by
  intro hmax
  exact (not_lt_of_ge (hmax.2 uWitness hwitness)) hgt

/-- Exact scanner certificate for failed profile representatives.  A profile-indexed representative
function fails to choose fiber maximizers iff some used profile has either a representative outside
its fiber or a same-profile stack with a strictly larger bad-scalar count. -/
theorem not_profileFiberMaxReps_iff_exists_bad_used_profile
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} :
    (¬ ProfileFiberMaxReps F C δ profile rep) ↔
      ∃ p : P, UsedProfile profile p ∧
        (profile (rep p) ≠ p ∨
          ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
            StackBadCount F C δ (rep p) < StackBadCount F C δ u) := by
  constructor
  · intro hnot
    classical
    by_contra hnone
    apply hnot
    intro p hused
    refine ⟨?_, ?_⟩
    · by_contra hne
      exact hnone ⟨p, hused, Or.inl hne⟩
    · intro u hu
      by_contra hle
      exact hnone ⟨p, hused, Or.inr ⟨u, hu, Nat.lt_of_not_ge hle⟩⟩
  · rintro ⟨p, hused, hbad⟩ hmax
    rcases hbad with houtside | ⟨u, hu, hlt⟩
    · exact houtside (hmax p hused).1
    · exact (not_lt_of_ge ((hmax p hused).2 u hu)) hlt

/-- Positive scanner form.  A representative catalogue chooses exact fiber maximizers iff the
scanner finds no used profile where the representative is outside the advertised fiber and no
same-profile stack beats the representative. -/
theorem profileFiberMaxReps_iff_no_bad_used_profile
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} :
    ProfileFiberMaxReps F C δ profile rep ↔
      ¬ ∃ p : P, UsedProfile profile p ∧
        (profile (rep p) ≠ p ∨
          ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
            StackBadCount F C δ (rep p) < StackBadCount F C δ u) := by
  constructor
  · intro hmax hbad
    exact (not_profileFiberMaxReps_iff_exists_bad_used_profile C δ).mpr hbad hmax
  · intro hno
    by_contra hnot
    exact hno ((not_profileFiberMaxReps_iff_exists_bad_used_profile C δ).mp hnot)

/-- Profile-fiber boundedness fails exactly when some used profile representative is above budget.
This is the budget-side scanner certificate matching
`not_profileFiberMaxReps_iff_exists_bad_used_profile`. -/
theorem not_profileFiberMaxesBounded_iff_exists_usedProfile_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} :
    (¬ ProfileFiberMaxesBounded F C δ profile rep B) ↔
      ∃ p : P, UsedProfile profile p ∧ B < StackBadCount F C δ (rep p) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro p hused
    exact le_of_not_gt (fun hgt => hnone ⟨p, hused, hgt⟩)
  · rintro ⟨p, hused, hgt⟩ hbounded
    exact (not_lt_of_ge (hbounded p hused)) hgt

/-- Positive budget scanner form for profile-fiber maximizers.  Bounding all chosen used-profile
representatives is equivalent to the scanner finding no used representative above budget. -/
theorem profileFiberMaxesBounded_iff_no_usedProfile_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} :
    ProfileFiberMaxesBounded F C δ profile rep B ↔
      ¬ ∃ p : P, UsedProfile profile p ∧ B < StackBadCount F C δ (rep p) := by
  constructor
  · intro hbounded hbad
    exact (not_profileFiberMaxesBounded_iff_exists_usedProfile_budget_lt C δ).mpr hbad hbounded
  · intro hno
    by_contra hnot
    exact hno ((not_profileFiberMaxesBounded_iff_exists_usedProfile_budget_lt C δ).mp hnot)

/-- Under exact profile-fiber representatives, the universal incidence budget is exactly the local
scanner statement that no used profile representative exceeds the budget.  This removes the last
global quantifier from the profile route once the max-representative scanner has passed. -/
theorem worstCaseIncidenceBounded_iff_no_usedProfile_budget_lt_of_profileFiberMaxReps
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hmax : ProfileFiberMaxReps F C δ profile rep) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B
      ↔ ¬ ∃ p : P, UsedProfile profile p ∧
        B < StackBadCount F C δ (rep p) := by
  exact (worstCaseIncidenceBounded_iff_profileFiberMaxesBounded C δ hmax).trans
    (profileFiberMaxesBounded_iff_no_usedProfile_budget_lt C δ)

/-- Under exact profile-fiber representatives, failure of the universal incidence budget is exactly
a used profile representative above budget.  In this form a counterexample scanner only has to
return the offending used profile label. -/
theorem not_worstCaseIncidenceBounded_iff_exists_usedProfile_budget_lt_of_profileFiberMaxReps
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hmax : ProfileFiberMaxReps F C δ profile rep) :
    (¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B)
      ↔ ∃ p : P, UsedProfile profile p ∧
        B < StackBadCount F C δ (rep p) := by
  constructor
  · intro hnot
    exact (not_profileFiberMaxesBounded_iff_exists_usedProfile_budget_lt C δ).mp
      (fun hbounded => hnot
        ((worstCaseIncidenceBounded_iff_profileFiberMaxesBounded C δ hmax).mpr hbounded))
  · intro hbad hI
    exact ((not_profileFiberMaxesBounded_iff_exists_usedProfile_budget_lt C δ).mpr hbad)
      ((worstCaseIncidenceBounded_iff_profileFiberMaxesBounded C δ hmax).mp hI)

/-- Scanner-positive form of
`worstCaseIncidenceBounded_iff_no_usedProfile_budget_lt_of_profileFiberMaxReps`: once no used
profile has an invalid or beaten representative, the remaining universal incidence question is
exactly the used-profile budget scanner. -/
theorem worstCaseIncidenceBounded_iff_no_usedProfile_budget_lt_of_no_bad_used_profile
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ p : P, UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackBadCount F C δ (rep p) < StackBadCount F C δ u)) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B
      ↔ ¬ ∃ p : P, UsedProfile profile p ∧
        B < StackBadCount F C δ (rep p) :=
  worstCaseIncidenceBounded_iff_no_usedProfile_budget_lt_of_profileFiberMaxReps
    C δ ((profileFiberMaxReps_iff_no_bad_used_profile C δ).mpr hnoMaxBad)

/-- Scanner-negative form: after the max-representative scanner has passed, a universal incidence
failure is equivalent to a single used profile representative above budget. -/
theorem not_worstCaseIncidenceBounded_iff_exists_usedProfile_budget_lt_of_no_bad_used_profile
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ p : P, UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackBadCount F C δ (rep p) < StackBadCount F C δ u)) :
    (¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B)
      ↔ ∃ p : P, UsedProfile profile p ∧
        B < StackBadCount F C δ (rep p) :=
  not_worstCaseIncidenceBounded_iff_exists_usedProfile_budget_lt_of_profileFiberMaxReps
    C δ ((profileFiberMaxReps_iff_no_bad_used_profile C δ).mpr hnoMaxBad)

/-- Fully scanner-facing profile incidence consumer.  If no used profile has an invalid or beaten
representative, and no used representative is above budget, then the universal incidence bound
follows. -/
theorem worstCaseIncidenceBounded_of_no_bad_used_profile_scanner
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ p : P, UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackBadCount F C δ (rep p) < StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ p : P, UsedProfile profile p ∧
      B < StackBadCount F C δ (rep p)) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_profileFiberMaxesBounded C δ
    ((profileFiberMaxReps_iff_no_bad_used_profile C δ).mpr hnoMaxBad)
    ((profileFiberMaxesBounded_iff_no_usedProfile_budget_lt C δ).mpr hnoBudgetBad)

/-- Direct delta-star consumer for the fully scanner-facing profile route. -/
theorem deltaStar_pin_of_no_bad_used_profile_scanner
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ p : P, UsedProfile profile p ∧
      (profile (rep p) ≠ p ∨
        ∃ u : WordStack A (Fin 2) ι, profile u = p ∧
          StackBadCount F C δ (rep p) < StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ p : P, UsedProfile profile p ∧
      B < StackBadCount F C δ (rep p))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_no_bad_used_profile_scanner
      C δ hnoMaxBad hnoBudgetBad)
    hbudget

/-- A used profile whose selected fiber representative exceeds the budget refutes the universal
incidence hypothesis at that budget. -/
theorem not_worstCaseIncidenceBounded_of_profileFiberMax_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {p : P}
    (_hused : UsedProfile profile p)
    (hgt : B < StackBadCount F C δ (rep p)) :
    ¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro hI
  exact (not_lt_of_ge (hI (rep p))) hgt

end ArkLib.ProximityGap.Frontier.StackProfileFiberMax

/-! ## Axiom audit -/

namespace ArkLib.ProximityGap.Frontier.StackProfileFiberMax

#print axioms exists_profileFiberMax_of_used
#print axioms stackBadCount_le_profileFiberMaxRep
#print axioms worstCaseIncidenceBounded_of_profileFiberMaxesBounded
#print axioms worstCaseIncidenceBounded_iff_profileFiberMaxesBounded
#print axioms familyDominates_of_profileFiberMaxReps
#print axioms exists_usedProfile_stackDominates_of_profileFiberMaxReps
#print axioms not_profileFiberMaxReps_of_each_used_rep_beaten
#print axioms worstCaseIncidenceBounded_of_profileFiberMaxFamilyBounded
#print axioms stackDominates_of_profileFiberMax_constant
#print axioms profileFiberMaxReps_identity
#print axioms
  profileFiberMaxesBounded_identity_iff_worstCaseIncidenceBounded
#print axioms deltaStar_pin_of_profileFiberMaxesBounded
#print axioms not_profileFiberMax_of_sameProfile_strictly_larger
#print axioms not_profileFiberMaxReps_iff_exists_bad_used_profile
#print axioms profileFiberMaxReps_iff_no_bad_used_profile
#print axioms not_profileFiberMaxesBounded_iff_exists_usedProfile_budget_lt
#print axioms profileFiberMaxesBounded_iff_no_usedProfile_budget_lt
#print axioms
  worstCaseIncidenceBounded_iff_no_usedProfile_budget_lt_of_profileFiberMaxReps
#print axioms
  not_worstCaseIncidenceBounded_iff_exists_usedProfile_budget_lt_of_profileFiberMaxReps
#print axioms
  worstCaseIncidenceBounded_iff_no_usedProfile_budget_lt_of_no_bad_used_profile
#print axioms
  not_worstCaseIncidenceBounded_iff_exists_usedProfile_budget_lt_of_no_bad_used_profile
#print axioms worstCaseIncidenceBounded_of_no_bad_used_profile_scanner
#print axioms deltaStar_pin_of_no_bad_used_profile_scanner
#print axioms
  not_worstCaseIncidenceBounded_of_profileFiberMax_budget_lt

end ArkLib.ProximityGap.Frontier.StackProfileFiberMax
