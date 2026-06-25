/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Refining stack profiles

The profile route needs a profile that is neither too coarse nor too fine.  This file gives the
formal bridge for refining a coarse profile into a finer one.

If

`project (fine u) = coarse u`

and each used fine-profile fiber has a chosen bad-scalar maximizer, then the universal incidence
bound is equivalent to bounding those fine-profile maximizers, grouped over the used coarse
profiles.  This is the exact output type for an iterative classification search: split a hard
coarse fiber into finer fibers, then prove the maximizer in each fine fiber is within budget.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.StackProfileRefinement

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

/-- The profile value is actually attained by at least one stack. -/
def UsedProfile {P : Type}
    (profile : WordStack A (Fin 2) ι -> P) (p : P) : Prop :=
  ∃ u : WordStack A (Fin 2) ι, profile u = p

/-- `fine` refines `coarse` through `project` if `project` sends the fine label of every stack to
its coarse label. -/
def ProfileRefines {P Q : Type}
    (fine : WordStack A (Fin 2) ι -> Q)
    (coarse : WordStack A (Fin 2) ι -> P)
    (project : Q -> P) : Prop :=
  ∀ u : WordStack A (Fin 2) ι, project (fine u) = coarse u

/-- `rep q` is a bad-scalar maximizer inside the fine-profile fiber `q`, for every used `q`. -/
def FineFiberMaxReps (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {Q : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (fine : WordStack A (Fin 2) ι -> Q)
    (rep : Q -> WordStack A (Fin 2) ι) : Prop :=
  ∀ q : Q, UsedProfile fine q →
    fine (rep q) = q
      ∧ ∀ u : WordStack A (Fin 2) ι, fine u = q →
        StackBadCount K C δ u ≤ StackBadCount K C δ (rep q)

/-- Fine-profile representatives lying over a coarse profile value. -/
noncomputable def fineRepsOver {P Q : Type} [Fintype Q] [DecidableEq P]
    (project : Q -> P) (rep : Q -> WordStack A (Fin 2) ι) (p : P) :
    Finset (WordStack A (Fin 2) ι) := by
  classical
  exact (Finset.univ.filter (fun q : Q => project q = p)).image rep

/-- The fine-profile maximizers over one coarse profile are all within budget. -/
def FineRepsOverBounded (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P Q : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (fine : WordStack A (Fin 2) ι -> Q) (project : Q -> P)
    (rep : Q -> WordStack A (Fin 2) ι) (p : P) (B : ℕ) : Prop :=
  ∀ q : Q, project q = p -> UsedProfile fine q -> StackBounded K C δ (rep q) B

/-- All used coarse profiles have their lying-over fine-profile maximizers within budget. -/
def RefinedProfileMaxesBounded (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    {P Q : Type} (C : Set (ι -> A)) (δ : ℝ≥0)
    (fine : WordStack A (Fin 2) ι -> Q)
    (coarse : WordStack A (Fin 2) ι -> P) (project : Q -> P)
    (rep : Q -> WordStack A (Fin 2) ι) (B : ℕ) : Prop :=
  ∀ p : P, UsedProfile coarse p -> FineRepsOverBounded K C δ fine project rep p B

/-- A stack is bounded by the maximizer of its fine-profile fiber. -/
theorem stackBadCount_le_fineFiberMaxRep
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Q : Type} {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hmax : FineFiberMaxReps F C δ fine rep)
    (u : WordStack A (Fin 2) ι) :
    StackBadCount F C δ u ≤ StackBadCount F C δ (rep (fine u)) := by
  exact (hmax (fine u) ⟨u, rfl⟩).2 u rfl

/-- The fine representative of any stack belongs to the finite representative set over its coarse
profile. -/
theorem fineRep_mem_fineRepsOver_of_coarse
    {P Q : Type} [Fintype Q] [DecidableEq P]
    {fine : WordStack A (Fin 2) ι -> Q}
    {coarse : WordStack A (Fin 2) ι -> P} {project : Q -> P}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hrefine : ProfileRefines fine coarse project)
    (u : WordStack A (Fin 2) ι) :
    rep (fine u) ∈ fineRepsOver (A := A) project rep (coarse u) := by
  classical
  exact Finset.mem_image.mpr
    ⟨fine u, by simpa [fineRepsOver, hrefine u], rfl⟩

/-- If the fine representatives over a coarse profile are bounded, then every stack in that coarse
profile is bounded. -/
theorem stackBounded_of_fineRepsOverBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P Q : Type} {fine : WordStack A (Fin 2) ι -> Q}
    {coarse : WordStack A (Fin 2) ι -> P} {project : Q -> P}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hrefine : ProfileRefines fine coarse project)
    (hmax : FineFiberMaxReps F C δ fine rep)
    {p : P} {u : WordStack A (Fin 2) ι}
    (hp : coarse u = p)
    (hbounded : FineRepsOverBounded F C δ fine project rep p B) :
    StackBounded F C δ u B := by
  have hq : project (fine u) = p := by
    rw [hrefine u, hp]
  exact le_trans (stackBadCount_le_fineFiberMaxRep C δ hmax u)
    (hbounded (fine u) hq ⟨u, rfl⟩)

/-- Refined profile-fiber maximizers within budget give the full worst-case incidence hypothesis. -/
theorem worstCaseIncidenceBounded_of_refinedProfileMaxesBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P Q : Type} {fine : WordStack A (Fin 2) ι -> Q}
    {coarse : WordStack A (Fin 2) ι -> P} {project : Q -> P}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hrefine : ProfileRefines fine coarse project)
    (hmax : FineFiberMaxReps F C δ fine rep)
    (hbounded : RefinedProfileMaxesBounded F C δ fine coarse project rep B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro u
  exact stackBounded_of_fineRepsOverBounded C δ hrefine hmax rfl
    (hbounded (coarse u) ⟨u, rfl⟩)

/-- Conversely, the universal incidence hypothesis bounds every fine-profile representative. -/
theorem refinedProfileMaxesBounded_of_worstCaseIncidenceBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P Q : Type} {fine : WordStack A (Fin 2) ι -> Q}
    {coarse : WordStack A (Fin 2) ι -> P} {project : Q -> P}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hI : ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B) :
    RefinedProfileMaxesBounded F C δ fine coarse project rep B := by
  intro _p _hp q _hq _hused
  exact hI (rep q)

/-- Under a refinement and chosen fine-fiber maximizers, the universal incidence bound is equivalent
to bounding all used fine-profile maximizers grouped over the used coarse profiles. -/
theorem worstCaseIncidenceBounded_iff_refinedProfileMaxesBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P Q : Type} {fine : WordStack A (Fin 2) ι -> Q}
    {coarse : WordStack A (Fin 2) ι -> P} {project : Q -> P}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hrefine : ProfileRefines fine coarse project)
    (hmax : FineFiberMaxReps F C δ fine rep) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B
      ↔ RefinedProfileMaxesBounded F C δ fine coarse project rep B :=
  ⟨refinedProfileMaxesBounded_of_worstCaseIncidenceBounded C δ,
    worstCaseIncidenceBounded_of_refinedProfileMaxesBounded C δ hrefine hmax⟩

/-- Refining any coarse profile all the way to the identity stack profile is a valid refinement, but
it carries no compression. -/
theorem profileRefines_identity_fine
    {P : Type} (coarse : WordStack A (Fin 2) ι -> P) :
    ProfileRefines (fun u : WordStack A (Fin 2) ι => u) coarse coarse := by
  intro u
  rfl

/-- The identity fine profile has the tautological fine-fiber representative: every stack represents
its own singleton fine fiber. -/
theorem fineFiberMaxReps_identity
    (C : Set (ι -> A)) (δ : ℝ≥0) :
    FineFiberMaxReps F C δ
      (fun u : WordStack A (Fin 2) ι => u)
      (fun u : WordStack A (Fin 2) ι => u) := by
  intro q _hused
  refine ⟨rfl, ?_⟩
  intro u hu
  simpa [hu]

/-- If the fine profile is the identity stack profile, refined-profile boundedness is exactly the
original universal incidence hypothesis, no matter which coarse profile it lies over.  Thus
refinement helps only before it reaches the all-stack granularity. -/
theorem refinedProfileMaxesBounded_identity_iff_worstCaseIncidenceBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) (B : ℕ)
    {P : Type} (coarse : WordStack A (Fin 2) ι -> P) :
    RefinedProfileMaxesBounded F C δ
        (fun u : WordStack A (Fin 2) ι => u)
        coarse coarse
        (fun u : WordStack A (Fin 2) ι => u) B
      ↔ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
          (F := F) (A := A) C δ B := by
  constructor
  · intro hbounded u
    exact hbounded (coarse u) ⟨u, rfl⟩ u rfl ⟨u, rfl⟩
  · intro hI p hp q _hq _hused
    exact hI q

/-- Delta-star consumer for a refined-profile classification proof. -/
theorem deltaStar_pin_of_refinedProfileMaxesBounded
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P Q : Type} {fine : WordStack A (Fin 2) ι -> Q}
    {coarse : WordStack A (Fin 2) ι -> P} {project : Q -> P}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hrefine : ProfileRefines fine coarse project)
    (hmax : FineFiberMaxReps F C δ fine rep)
    (hbounded : RefinedProfileMaxesBounded F C δ fine coarse project rep B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_refinedProfileMaxesBounded C δ hrefine hmax hbounded)
    hbudget

/-! ## Refutation APIs -/

/-- A stack above budget refutes any claimed refined-profile boundedness theorem under the same
fine-fiber maximizers. -/
theorem not_refinedProfileMaxesBounded_of_counterStack
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P Q : Type} {fine : WordStack A (Fin 2) ι -> Q}
    {coarse : WordStack A (Fin 2) ι -> P} {project : Q -> P}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hrefine : ProfileRefines fine coarse project)
    (hmax : FineFiberMaxReps F C δ fine rep)
    {uWitness : WordStack A (Fin 2) ι}
    (hgt : B < StackBadCount F C δ uWitness) :
    ¬ RefinedProfileMaxesBounded F C δ fine coarse project rep B := by
  intro hbounded
  have hle : StackBadCount F C δ uWitness ≤ B :=
    worstCaseIncidenceBounded_of_refinedProfileMaxesBounded
      C δ hrefine hmax hbounded uWitness
  exact (not_lt_of_ge hle) hgt

/-- A same-fine-profile stack with a larger bad-scalar count refutes the proposed fine-fiber
maximizer. -/
theorem not_fineFiberMaxRep_of_sameFineProfile_strictly_larger
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Q : Type} {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι} {q : Q}
    {uWitness : WordStack A (Fin 2) ι}
    (hwitness : fine uWitness = q)
    (hgt : StackBadCount F C δ (rep q) < StackBadCount F C δ uWitness) :
    ¬ FineFiberMaxReps F C δ fine rep := by
  intro hmax
  exact (not_lt_of_ge ((hmax q ⟨uWitness, hwitness⟩).2 uWitness hwitness)) hgt

end ArkLib.ProximityGap.Frontier.StackProfileRefinement

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.stackBadCount_le_fineFiberMaxRep
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.fineRep_mem_fineRepsOver_of_coarse
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.stackBounded_of_fineRepsOverBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.worstCaseIncidenceBounded_of_refinedProfileMaxesBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.refinedProfileMaxesBounded_of_worstCaseIncidenceBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.worstCaseIncidenceBounded_iff_refinedProfileMaxesBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.profileRefines_identity_fine
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.fineFiberMaxReps_identity
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.refinedProfileMaxesBounded_identity_iff_worstCaseIncidenceBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.deltaStar_pin_of_refinedProfileMaxesBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.not_refinedProfileMaxesBounded_of_counterStack
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.not_fineFiberMaxRep_of_sameFineProfile_strictly_larger
