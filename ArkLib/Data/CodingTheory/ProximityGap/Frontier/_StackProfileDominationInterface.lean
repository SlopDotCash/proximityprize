/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Profile/cap interface for stack classification proofs

The candidate-family max file says that a finite binder/floor catalogue must dominate all stacks.
This file records a constructive way such a domination theorem could be proved.

Choose a profile map

`profile : WordStack A (Fin 2) ι -> P`

and a numerical cap

`cap : P -> ℕ`.

There are two honest consumers:

* Direct route: prove every stack's bad-scalar count is at most the cap of its profile, and every
  profile cap is at most the budget `B`.
* Representative route: prove every used profile cap is realized by a representative stack in a
  finite family `R`; then bounding `R` gives the universal incidence bound.

The counter-lemmas state exactly how to refute a proposed profile scheme: find a stack above its
assigned cap, or find a used profile whose cap is not realized by any member of the proposed family.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.StackProfileDominationInterface

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

/-- A profile cap is a pointwise upper bound on the actual bad-scalar count. -/
def ProfileCaps (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (profile : WordStack A (Fin 2) ι -> P) (cap : P -> ℕ) : Prop :=
  ∀ u : WordStack A (Fin 2) ι, StackBadCount K C δ u ≤ cap (profile u)

/-- Every profile cap is within the incidence budget. -/
def ProfileBudgeted {P : Type} (cap : P -> ℕ) (B : ℕ) : Prop :=
  ∀ p : P, cap p ≤ B

/-- Every used profile cap is realized by some representative in the proposed family. -/
def ProfileRealizedByFamily (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (profile : WordStack A (Fin 2) ι -> P) (cap : P -> ℕ)
    (R : Finset (WordStack A (Fin 2) ι)) : Prop :=
  ∀ p : P, UsedProfile profile p →
    ∃ r ∈ R, cap p ≤ StackBadCount K C δ r

/-- A profile-indexed representative function realizes every used profile cap. -/
def ProfileRealizedByReps (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (profile : WordStack A (Fin 2) ι -> P) (cap : P -> ℕ)
    (rep : P -> WordStack A (Fin 2) ι) : Prop :=
  ∀ p : P, UsedProfile profile p → cap p ≤ StackBadCount K C δ (rep p)

/-- Direct consumer: profile caps within budget give the full worst-case incidence hypothesis. -/
theorem worstCaseIncidenceBounded_of_profileCaps_budget
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P} {cap : P -> ℕ}
    (hcap : ProfileCaps F C δ profile cap)
    (hbudget : ProfileBudgeted cap B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro u
  exact le_trans (hcap u) (hbudget (profile u))

/-- Representative consumer: profile caps plus cap-realizing representatives imply family
domination. -/
theorem familyDominates_of_profileCaps_realized
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P} {cap : P -> ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hcap : ProfileCaps F C δ profile cap)
    (hreal : ProfileRealizedByFamily F C δ profile cap R) :
    FamilyDominates F C δ R := by
  intro u
  rcases hreal (profile u) ⟨u, rfl⟩ with ⟨r, hr, hrealized⟩
  exact ⟨r, hr, le_trans (hcap u) hrealized⟩

/-- A cap-realizing bounded family gives the full worst-case incidence hypothesis. -/
theorem worstCaseIncidenceBounded_of_profileCaps_realized_familyBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P} {cap : P -> ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hcap : ProfileCaps F C δ profile cap)
    (hreal : ProfileRealizedByFamily F C δ profile cap R)
    (hR : FamilyBounded F C δ R B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro u
  rcases familyDominates_of_profileCaps_realized C δ hcap hreal u with ⟨r, hr, hur⟩
  exact le_trans hur (hR r hr)

/-- A profile-indexed representative map generates a finite dominating candidate family. -/
theorem familyDominates_of_profileReps
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} [Fintype P] [DecidableEq P]
    {profile : WordStack A (Fin 2) ι -> P} {cap : P -> ℕ}
    {rep : P -> WordStack A (Fin 2) ι}
    (hcap : ProfileCaps F C δ profile cap)
    (hrep : ProfileRealizedByReps F C δ profile cap rep) :
    FamilyDominates F C δ ((Finset.univ : Finset P).image rep) := by
  intro u
  refine ⟨rep (profile u), ?_, le_trans (hcap u) (hrep (profile u) ⟨u, rfl⟩)⟩
  exact Finset.mem_image.mpr ⟨profile u, Finset.mem_univ _, rfl⟩

/-- A profile-indexed representative map plus bounds on its finite image gives the universal
incidence hypothesis. -/
theorem worstCaseIncidenceBounded_of_profileReps_familyBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} [Fintype P] [DecidableEq P]
    {profile : WordStack A (Fin 2) ι -> P} {cap : P -> ℕ}
    {rep : P -> WordStack A (Fin 2) ι}
    (hcap : ProfileCaps F C δ profile cap)
    (hrep : ProfileRealizedByReps F C δ profile cap rep)
    (hbounded : FamilyBounded F C δ ((Finset.univ : Finset P).image rep) B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  exact worstCaseIncidenceBounded_of_profileCaps_realized_familyBounded
    C δ hcap
    (fun p hp =>
      ⟨rep p, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩, hrep p hp⟩)
    hbounded

/-- Delta-star consumer for the direct profile-budget route. -/
theorem deltaStar_pin_of_profileCaps_budget
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P} {cap : P -> ℕ}
    (hcap : ProfileCaps F C δ profile cap)
    (hprofileBudget : ProfileBudgeted cap B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_profileCaps_budget C δ hcap hprofileBudget)
    hbudget

/-- Delta-star consumer for the profile-representative route. -/
theorem deltaStar_pin_of_profileReps_familyBounded
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} [Fintype P] [DecidableEq P]
    {profile : WordStack A (Fin 2) ι -> P} {cap : P -> ℕ}
    {rep : P -> WordStack A (Fin 2) ι}
    (hcap : ProfileCaps F C δ profile cap)
    (hrep : ProfileRealizedByReps F C δ profile cap rep)
    (hbounded : FamilyBounded F C δ ((Finset.univ : Finset P).image rep) B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_profileReps_familyBounded C δ hcap hrep hbounded)
    hbudget

/-! ## Refutation APIs -/

/-- A stack above its assigned cap refutes the proposed profile cap theorem. -/
theorem not_profileCaps_of_counterexample
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P} {cap : P -> ℕ}
    (hcounter :
      ∃ u : WordStack A (Fin 2) ι, cap (profile u) < StackBadCount F C δ u) :
    ¬ ProfileCaps F C δ profile cap := by
  intro hcap
  rcases hcounter with ⟨u, hu⟩
  exact (not_lt_of_ge (hcap u)) hu

/-- A profile above budget refutes the direct profile-budget route. -/
theorem not_profileBudgeted_of_counterprofile
    {P : Type} {cap : P -> ℕ} {B : ℕ}
    (hcounter : ∃ p : P, B < cap p) :
    ¬ ProfileBudgeted cap B := by
  intro hbudget
  rcases hcounter with ⟨p, hp⟩
  exact (not_lt_of_ge (hbudget p)) hp

/-- A used profile whose cap is larger than every representative's bad count refutes realization by
that representative family. -/
theorem not_profileRealizedByFamily_of_counterprofile
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P} {cap : P -> ℕ}
    {R : Finset (WordStack A (Fin 2) ι)} {p : P}
    (hused : UsedProfile profile p)
    (hcounter : ∀ r ∈ R, StackBadCount F C δ r < cap p) :
    ¬ ProfileRealizedByFamily F C δ profile cap R := by
  intro hreal
  rcases hreal p hused with ⟨r, hr, hcap⟩
  exact (not_lt_of_ge hcap) (hcounter r hr)

end ArkLib.ProximityGap.Frontier.StackProfileDominationInterface

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.StackProfileDominationInterface.worstCaseIncidenceBounded_of_profileCaps_budget
#print axioms ArkLib.ProximityGap.Frontier.StackProfileDominationInterface.familyDominates_of_profileCaps_realized
#print axioms ArkLib.ProximityGap.Frontier.StackProfileDominationInterface.worstCaseIncidenceBounded_of_profileCaps_realized_familyBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileDominationInterface.familyDominates_of_profileReps
#print axioms ArkLib.ProximityGap.Frontier.StackProfileDominationInterface.worstCaseIncidenceBounded_of_profileReps_familyBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileDominationInterface.deltaStar_pin_of_profileCaps_budget
#print axioms ArkLib.ProximityGap.Frontier.StackProfileDominationInterface.deltaStar_pin_of_profileReps_familyBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileDominationInterface.not_profileCaps_of_counterexample
#print axioms ArkLib.ProximityGap.Frontier.StackProfileDominationInterface.not_profileBudgeted_of_counterprofile
#print axioms ArkLib.ProximityGap.Frontier.StackProfileDominationInterface.not_profileRealizedByFamily_of_counterprofile
