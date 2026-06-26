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

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

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
    ⟨fine u, by simp [hrefine u], rfl⟩

set_option linter.unusedSectionVars true
set_option linter.unusedDecidableInType true
set_option linter.unusedFintypeInType true

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

/-! ## Scanner-facing forms -/

/-- Exact scanner certificate for failed fine-profile representatives.  A representative function
fails to choose fine-fiber maximizers iff some used fine profile has either a representative outside
the advertised fine fiber or a same-fine-profile stack with a strictly larger bad-scalar count. -/
theorem not_fineFiberMaxReps_iff_exists_bad_used_fineProfile
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Q : Type} {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι} :
    (¬ FineFiberMaxReps F C δ fine rep) ↔
      ∃ q : Q, UsedProfile fine q ∧
        (fine (rep q) ≠ q ∨
          ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
            StackBadCount F C δ (rep q) < StackBadCount F C δ u) := by
  constructor
  · intro hnot
    classical
    by_contra hnone
    apply hnot
    intro q hused
    refine ⟨?_, ?_⟩
    · by_contra hne
      exact hnone ⟨q, hused, Or.inl hne⟩
    · intro u hu
      by_contra hle
      exact hnone ⟨q, hused, Or.inr ⟨u, hu, Nat.lt_of_not_ge hle⟩⟩
  · rintro ⟨q, hused, hbad⟩ hmax
    rcases hbad with houtside | ⟨u, hu, hlt⟩
    · exact houtside (hmax q hused).1
    · exact (not_lt_of_ge ((hmax q hused).2 u hu)) hlt

/-- Positive scanner form for fine-profile representatives.  A representative catalogue chooses
fine-fiber maximizers iff the scanner finds no used fine profile whose representative is outside its
fiber and no same-fine-profile stack beating the representative. -/
theorem fineFiberMaxReps_iff_no_bad_used_fineProfile
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Q : Type} {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι} :
    FineFiberMaxReps F C δ fine rep ↔
      ¬ ∃ q : Q, UsedProfile fine q ∧
        (fine (rep q) ≠ q ∨
          ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
            StackBadCount F C δ (rep q) < StackBadCount F C δ u) := by
  constructor
  · intro hmax hbad
    exact (not_fineFiberMaxReps_iff_exists_bad_used_fineProfile C δ).mpr hbad hmax
  · intro hno
    by_contra hnot
    exact hno ((not_fineFiberMaxReps_iff_exists_bad_used_fineProfile C δ).mp hnot)

/-- Refined-profile boundedness fails exactly when some used fine-profile representative exceeds
the budget.  The refinement hypothesis turns a used fine profile into a used coarse profile lying
over it, so the grouped boundedness condition has no hidden global content. -/
theorem not_refinedProfileMaxesBounded_iff_exists_usedFineProfile_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P Q : Type} {fine : WordStack A (Fin 2) ι -> Q}
    {coarse : WordStack A (Fin 2) ι -> P} {project : Q -> P}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hrefine : ProfileRefines fine coarse project) :
    (¬ RefinedProfileMaxesBounded F C δ fine coarse project rep B) ↔
      ∃ q : Q, UsedProfile fine q ∧ B < StackBadCount F C δ (rep q) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro p _hp q _hq hused
    exact le_of_not_gt (fun hgt => hnone ⟨q, hused, hgt⟩)
  · rintro ⟨q, hused, hgt⟩ hbounded
    rcases hused with ⟨u, hu⟩
    have hp : UsedProfile coarse (project q) := by
      refine ⟨u, ?_⟩
      rw [← hrefine u, hu]
    exact (not_lt_of_ge (hbounded (project q) hp q rfl ⟨u, hu⟩)) hgt

/-- Positive scanner form for refined-profile boundedness.  Bounding the grouped fine-profile
representatives is exactly the absence of a used fine-profile representative above budget. -/
theorem refinedProfileMaxesBounded_iff_no_usedFineProfile_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P Q : Type} {fine : WordStack A (Fin 2) ι -> Q}
    {coarse : WordStack A (Fin 2) ι -> P} {project : Q -> P}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hrefine : ProfileRefines fine coarse project) :
    RefinedProfileMaxesBounded F C δ fine coarse project rep B ↔
      ¬ ∃ q : Q, UsedProfile fine q ∧ B < StackBadCount F C δ (rep q) := by
  constructor
  · intro hbounded hbad
    exact (not_refinedProfileMaxesBounded_iff_exists_usedFineProfile_budget_lt
      C δ hrefine).mpr hbad hbounded
  · intro hno
    by_contra hnot
    exact hno
      ((not_refinedProfileMaxesBounded_iff_exists_usedFineProfile_budget_lt
        C δ hrefine).mp hnot)

/-- Scanner-facing refined-profile incidence consumer.  If no used fine profile has a bad
representative and no used fine-profile representative exceeds the budget, then the universal
incidence hypothesis follows. -/
theorem worstCaseIncidenceBounded_of_no_bad_fineProfile_scanner
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P Q : Type} {fine : WordStack A (Fin 2) ι -> Q}
    {coarse : WordStack A (Fin 2) ι -> P} {project : Q -> P}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hrefine : ProfileRefines fine coarse project)
    (hnoMaxBad : ¬ ∃ q : Q, UsedProfile fine q ∧
      (fine (rep q) ≠ q ∨
        ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
          StackBadCount F C δ (rep q) < StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ q : Q, UsedProfile fine q ∧
      B < StackBadCount F C δ (rep q)) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_refinedProfileMaxesBounded C δ hrefine
    ((fineFiberMaxReps_iff_no_bad_used_fineProfile C δ).mpr hnoMaxBad)
    ((refinedProfileMaxesBounded_iff_no_usedFineProfile_budget_lt
      C δ hrefine).mpr hnoBudgetBad)

/-- Direct delta-star consumer for the fully scanner-facing refined-profile route. -/
theorem deltaStar_pin_of_no_bad_fineProfile_scanner
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P Q : Type} {fine : WordStack A (Fin 2) ι -> Q}
    {coarse : WordStack A (Fin 2) ι -> P} {project : Q -> P}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hrefine : ProfileRefines fine coarse project)
    (hnoMaxBad : ¬ ∃ q : Q, UsedProfile fine q ∧
      (fine (rep q) ≠ q ∨
        ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
          StackBadCount F C δ (rep q) < StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ q : Q, UsedProfile fine q ∧
      B < StackBadCount F C δ (rep q))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_no_bad_fineProfile_scanner
      C δ hrefine hnoMaxBad hnoBudgetBad)
    hbudget

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-- Refining any coarse profile all the way to the identity stack profile is a valid refinement, but
it carries no compression. -/
theorem profileRefines_identity_fine
    {P : Type} (coarse : WordStack A (Fin 2) ι -> P) :
    ProfileRefines (fun u : WordStack A (Fin 2) ι => u) coarse coarse := by
  intro u
  rfl

set_option linter.unusedSectionVars true
set_option linter.unusedDecidableInType true
set_option linter.unusedFintypeInType true

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
  simp [hu]

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
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.not_fineFiberMaxReps_iff_exists_bad_used_fineProfile
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.fineFiberMaxReps_iff_no_bad_used_fineProfile
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.not_refinedProfileMaxesBounded_iff_exists_usedFineProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.refinedProfileMaxesBounded_iff_no_usedFineProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.worstCaseIncidenceBounded_of_no_bad_fineProfile_scanner
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.deltaStar_pin_of_no_bad_fineProfile_scanner
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.profileRefines_identity_fine
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.fineFiberMaxReps_identity
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.refinedProfileMaxesBounded_identity_iff_worstCaseIncidenceBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.deltaStar_pin_of_refinedProfileMaxesBounded
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.not_refinedProfileMaxesBounded_of_counterStack
#print axioms ArkLib.ProximityGap.Frontier.StackProfileRefinement.not_fineFiberMaxRep_of_sameFineProfile_strictly_larger
