/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

set_option autoImplicit false
set_option linter.style.longLine false

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

/-- A finite family dominates if every stack is bounded by some representative's bad-scalar count. -/
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
noncomputable def profileFiber {P : Type} [DecidableEq P]
    (profile : WordStack A (Fin 2) ι -> P) (p : P) :
    Finset (WordStack A (Fin 2) ι) := by
  classical
  exact Finset.univ.filter (fun u => profile u = p)

@[simp] theorem mem_profileFiber {P : Type} [DecidableEq P]
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
    {P : Type} [DecidableEq P]
    {profile : WordStack A (Fin 2) ι -> P} {p : P}
    (hused : UsedProfile profile p) :
    ∃ uMax : WordStack A (Fin 2) ι, ProfileFiberMax F C δ profile p uMax := by
  classical
  rcases hused with ⟨u₀, hu₀⟩
  have hfiber : (profileFiber (A := A) profile p).Nonempty :=
    ⟨u₀, by simpa [profileFiber, hu₀]⟩
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
    {P : Type} [Fintype P] [DecidableEq P]
    {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι}
    (hmax : ProfileFiberMaxReps F C δ profile rep) :
    FamilyDominates F C δ ((Finset.univ : Finset P).image rep) := by
  intro u
  refine ⟨rep (profile u), ?_, stackBadCount_le_profileFiberMaxRep C δ hmax u⟩
  exact Finset.mem_image.mpr ⟨profile u, Finset.mem_univ _, rfl⟩

/-- A finite family of bounded profile-fiber maximizers gives the universal incidence bound. -/
theorem worstCaseIncidenceBounded_of_profileFiberMaxFamilyBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} [Fintype P] [DecidableEq P]
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
  simpa [hu]

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
#print axioms ArkLib.ProximityGap.Frontier.StackProfileFiberMax.exists_profileFiberMax_of_used
#print axioms ArkLib.ProximityGap.Frontier.StackProfileFiberMax.stackBadCount_le_profileFiberMaxRep
#print axioms ArkLib.ProximityGap.Frontier.StackProfileFiberMax.worstCaseIncidenceBounded_of_profileFiberMaxesBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileFiberMax.worstCaseIncidenceBounded_iff_profileFiberMaxesBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileFiberMax.familyDominates_of_profileFiberMaxReps
#print axioms ArkLib.ProximityGap.Frontier.StackProfileFiberMax.worstCaseIncidenceBounded_of_profileFiberMaxFamilyBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileFiberMax.stackDominates_of_profileFiberMax_constant
#print axioms ArkLib.ProximityGap.Frontier.StackProfileFiberMax.profileFiberMaxReps_identity
#print axioms ArkLib.ProximityGap.Frontier.StackProfileFiberMax.profileFiberMaxesBounded_identity_iff_worstCaseIncidenceBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileFiberMax.deltaStar_pin_of_profileFiberMaxesBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileFiberMax.not_profileFiberMax_of_sameProfile_strictly_larger
#print axioms ArkLib.ProximityGap.Frontier.StackProfileFiberMax.not_worstCaseIncidenceBounded_of_profileFiberMax_budget_lt
