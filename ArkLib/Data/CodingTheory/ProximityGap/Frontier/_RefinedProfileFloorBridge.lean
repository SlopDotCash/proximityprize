/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorClosureContract
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._StackProfileRefinement

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Refined-profile scanners feed the floor closure contract

`_StackProfileRefinement` gives scanner-facing certificates for an iterative profile
classification: no used fine profile has an invalid or beaten representative, and no used fine
representative exceeds the budget.  `_FloorClosureContract` consumes a finite family only after it
contains a true global bad-scalar maximizer.

This file composes those APIs.  It is not a prize proof; it is the refined-profile version of the
profile/fiber floor bridge.  The remaining mathematical obligation is still to choose a useful fine
profile and prove the scanner certificates.
-/

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.FloorLocalization
open ArkLib.ProximityGap.Frontier.FloorLinnikTZClosure

namespace ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The fine-profile values actually attained by some stack. -/
noncomputable def usedFineProfileFinset {Q : Type} [Fintype Q]
    (fine : WordStack A (Fin 2) ι -> Q) : Finset Q := by
  classical
  exact (Finset.univ : Finset Q).filter
    (fun q => StackProfileRefinement.UsedProfile fine q)

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    [AddCommGroup A] in
@[simp] theorem mem_usedFineProfileFinset {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q} {q : Q} :
    q ∈ usedFineProfileFinset fine ↔ StackProfileRefinement.UsedProfile fine q := by
  classical
  simp [usedFineProfileFinset]

/-- The representative family restricted to fine profiles that actually occur. -/
noncomputable def usedFineProfileRepFamily {Q : Type} [Fintype Q]
    (fine : WordStack A (Fin 2) ι -> Q)
    (rep : Q -> WordStack A (Fin 2) ι) :
    Finset (WordStack A (Fin 2) ι) :=
  (usedFineProfileFinset fine).image rep

omit [Nonempty ι] [DecidableEq ι] [Fintype A] [AddCommGroup A] in
@[simp] theorem mem_usedFineProfileRepFamily {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    {r : WordStack A (Fin 2) ι} :
    r ∈ usedFineProfileRepFamily fine rep ↔
      ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧ rep q = r := by
  classical
  simp [usedFineProfileRepFamily, usedFineProfileFinset]

/-- Fine-fiber maximizers contain a global maximizer for the full image of representatives. -/
theorem floorFamilyContainsGlobalMax_of_fineFiberMaxReps
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hmax : StackProfileRefinement.FineFiberMaxReps F C δ fine rep) :
    FloorClosureContract.FamilyContainsGlobalMax F C δ
      ((Finset.univ : Finset Q).image rep) := by
  classical
  obtain ⟨uMax, hglobal⟩ :=
    Finite.exists_max
      (fun u : WordStack A (Fin 2) ι =>
        StackProfileRefinement.StackBadCount F C δ u)
  refine ⟨rep (fine uMax), Finset.mem_image.mpr ⟨fine uMax, Finset.mem_univ _, rfl⟩, ?_⟩
  intro u
  have hfiber :
      StackProfileRefinement.StackBadCount F C δ uMax ≤
        StackProfileRefinement.StackBadCount F C δ (rep (fine uMax)) :=
    (hmax (fine uMax) ⟨uMax, rfl⟩).2 uMax rfl
  exact by
    simpa [FloorClosureContract.StackBadCount, StackProfileRefinement.StackBadCount]
      using le_trans (hglobal u) hfiber

/-- Fine-fiber maximizers contain a global maximizer for the used fine-profile representative
family. -/
theorem floorFamilyContainsGlobalMax_of_fineFiberMaxReps_usedFineProfileFamily
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hmax : StackProfileRefinement.FineFiberMaxReps F C δ fine rep) :
    FloorClosureContract.FamilyContainsGlobalMax F C δ
      (usedFineProfileRepFamily fine rep) := by
  classical
  obtain ⟨uMax, hglobal⟩ :=
    Finite.exists_max
      (fun u : WordStack A (Fin 2) ι =>
        StackProfileRefinement.StackBadCount F C δ u)
  refine ⟨rep (fine uMax), ?_, ?_⟩
  · exact mem_usedFineProfileRepFamily.mpr ⟨fine uMax, ⟨uMax, rfl⟩, rfl⟩
  · intro u
    have hfiber :
        StackProfileRefinement.StackBadCount F C δ uMax ≤
          StackProfileRefinement.StackBadCount F C δ (rep (fine uMax)) :=
      (hmax (fine uMax) ⟨uMax, rfl⟩).2 uMax rfl
    exact by
      simpa [FloorClosureContract.StackBadCount, StackProfileRefinement.StackBadCount]
        using le_trans (hglobal u) hfiber

/-- Scanner-to-floor bridge: if no used fine profile has an invalid representative or a
same-fine-profile beating witness, then the full representative image contains a floor-contract
global maximizer. -/
theorem floorFamilyContainsGlobalMax_of_no_bad_fineProfile
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hno : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      (fine (rep q) ≠ q ∨
        ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
          StackProfileRefinement.StackBadCount F C δ (rep q) <
            StackProfileRefinement.StackBadCount F C δ u)) :
    FloorClosureContract.FamilyContainsGlobalMax F C δ
      ((Finset.univ : Finset Q).image rep) :=
  floorFamilyContainsGlobalMax_of_fineFiberMaxReps C δ
    ((StackProfileRefinement.fineFiberMaxReps_iff_no_bad_used_fineProfile C δ).mpr hno)

/-- Scanner-to-floor bridge for the used fine-profile representative family. -/
theorem floorFamilyContainsGlobalMax_of_no_bad_fineProfile_usedFineProfileFamily
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hno : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      (fine (rep q) ≠ q ∨
        ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
          StackProfileRefinement.StackBadCount F C δ (rep q) <
            StackProfileRefinement.StackBadCount F C δ u)) :
    FloorClosureContract.FamilyContainsGlobalMax F C δ
      (usedFineProfileRepFamily fine rep) :=
  floorFamilyContainsGlobalMax_of_fineFiberMaxReps_usedFineProfileFamily C δ
    ((StackProfileRefinement.fineFiberMaxReps_iff_no_bad_used_fineProfile C δ).mpr hno)

/-- If every fine-profile representative is beaten by some stack, then the full representative
image cannot contain a global maximizer.  This checks all fine-profile labels, including labels not
attained by any stack. -/
theorem not_floorFamilyContainsGlobalMax_of_each_fineProfile_rep_beaten
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Q : Type} [Fintype Q]
    {rep : Q -> WordStack A (Fin 2) ι}
    (hbeat : ∀ q : Q, ∃ u : WordStack A (Fin 2) ι,
      FloorClosureContract.StackBadCount F C δ (rep q) <
        FloorClosureContract.StackBadCount F C δ u) :
    ¬ FloorClosureContract.FamilyContainsGlobalMax F C δ
      ((Finset.univ : Finset Q).image rep) := by
  intro hcontains
  rcases hcontains with ⟨r, hr, hdom⟩
  rcases Finset.mem_image.mp hr with ⟨q, _hq, rfl⟩
  rcases hbeat q with ⟨u, hlt⟩
  exact (not_lt_of_ge (hdom u)) hlt

/-- Exact refutation certificate for the full fine-profile representative image. -/
theorem not_floorFamilyContainsGlobalMax_fineProfileRepImage_iff_each_rep_beaten
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Q : Type} [Fintype Q]
    {rep : Q -> WordStack A (Fin 2) ι} :
    (¬ FloorClosureContract.FamilyContainsGlobalMax F C δ
      ((Finset.univ : Finset Q).image rep)) ↔
      ∀ q : Q, ∃ u : WordStack A (Fin 2) ι,
        FloorClosureContract.StackBadCount F C δ (rep q) <
          FloorClosureContract.StackBadCount F C δ u := by
  constructor
  · intro hno q
    have hbeat :=
      (FloorClosureContract.not_familyContainsGlobalMax_iff_each_member_beaten
        (F := F) (A := A) C δ ((Finset.univ : Finset Q).image rep)).mp hno
    exact hbeat (rep q) (Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩)
  · intro hbeat
    exact not_floorFamilyContainsGlobalMax_of_each_fineProfile_rep_beaten C δ hbeat

/-- If every used fine-profile representative is beaten by some stack, the used representative
family cannot contain a global maximizer. -/
theorem not_floorFamilyContainsGlobalMax_of_each_used_fineProfile_rep_beaten
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hbeat : ∀ q : Q, StackProfileRefinement.UsedProfile fine q →
      ∃ u : WordStack A (Fin 2) ι,
        FloorClosureContract.StackBadCount F C δ (rep q) <
          FloorClosureContract.StackBadCount F C δ u) :
    ¬ FloorClosureContract.FamilyContainsGlobalMax F C δ
      (usedFineProfileRepFamily fine rep) := by
  intro hcontains
  rcases hcontains with ⟨r, hr, hdom⟩
  rcases mem_usedFineProfileRepFamily.mp hr with ⟨q, hused, rfl⟩
  rcases hbeat q hused with ⟨u, hlt⟩
  exact (not_lt_of_ge (hdom u)) hlt

/-- Exact refutation certificate for the used fine-profile representative family.  Failure to
contain a global maximizer is equivalent to beating every used fine-profile representative, with
the beating witness allowed to depend on the fine profile. -/
theorem not_floorFamilyContainsGlobalMax_usedFineProfileFamily_iff_each_used_rep_beaten
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι} :
    (¬ FloorClosureContract.FamilyContainsGlobalMax F C δ
      (usedFineProfileRepFamily fine rep)) ↔
      ∀ q : Q, StackProfileRefinement.UsedProfile fine q →
        ∃ u : WordStack A (Fin 2) ι,
          FloorClosureContract.StackBadCount F C δ (rep q) <
            FloorClosureContract.StackBadCount F C δ u := by
  constructor
  · intro hno q hused
    have hbeat :=
      (FloorClosureContract.not_familyContainsGlobalMax_iff_each_member_beaten
        (F := F) (A := A) C δ (usedFineProfileRepFamily fine rep)).mp hno
    exact hbeat (rep q) (mem_usedFineProfileRepFamily.mpr ⟨q, hused, rfl⟩)
  · intro hbeat
    exact not_floorFamilyContainsGlobalMax_of_each_used_fineProfile_rep_beaten C δ hbeat

/-- Exact budget certificate for the full fine-profile representative image.  The full image is
bounded iff no representative for any fine-profile label exceeds the target budget. -/
theorem familyBounded_fineProfileRepImage_iff_no_fineProfile_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {Q : Type} [Fintype Q]
    {rep : Q -> WordStack A (Fin 2) ι} :
    FloorClosureContract.FamilyBounded F C δ ((Finset.univ : Finset Q).image rep) B ↔
      ¬ ∃ q : Q, B < StackProfileRefinement.StackBadCount F C δ (rep q) := by
  constructor
  · intro hbounded hbad
    rcases hbad with ⟨q, hgt⟩
    have hle :
        StackProfileRefinement.StackBadCount F C δ (rep q) ≤ B := by
      simpa [FloorClosureContract.StackBadCount, StackProfileRefinement.StackBadCount] using
        hbounded (rep q) (Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩)
    exact (not_lt_of_ge hle) hgt
  · intro hno r hr
    rcases Finset.mem_image.mp hr with ⟨q, _hq, rfl⟩
    exact le_of_not_gt (fun hgt =>
      hno ⟨q, by
        simpa [FloorClosureContract.StackBadCount, StackProfileRefinement.StackBadCount] using
          hgt⟩)

/-- Exact local form of the floor-good family budget for the full fine-profile representative
image.  This is deliberately stronger than the used fine-profile version because it budgets every
fine-profile label. -/
theorem floorGoodFamilyBudget_fineProfileRepImage_iff_no_fineProfile_budget_lt
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {Q : Type} [Fintype Q]
    {rep : Q -> WordStack A (Fin 2) ι} :
    FloorClosureContract.FloorGoodFamilyBudget
        (F := F) (A := A) FloorBad a C δ ((Finset.univ : Finset Q).image rep) B
      ↔ (¬ FloorBad (2 ^ a) (Fintype.card F) →
        ¬ ∃ q : Q, B < StackProfileRefinement.StackBadCount F C δ (rep q)) := by
  constructor
  · intro hfloor hgood
    exact (familyBounded_fineProfileRepImage_iff_no_fineProfile_budget_lt C δ).mp
      (hfloor hgood)
  · intro hlocal hgood
    exact (familyBounded_fineProfileRepImage_iff_no_fineProfile_budget_lt C δ).mpr
      (hlocal hgood)

/-- Exact negative form for the full fine-profile representative image. -/
theorem not_floorGoodFamilyBudget_fineProfileRepImage_iff_floorGood_and_exists_fineProfile_budget_lt
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {Q : Type} [Fintype Q]
    {rep : Q -> WordStack A (Fin 2) ι} :
    (¬ FloorClosureContract.FloorGoodFamilyBudget
        (F := F) (A := A) FloorBad a C δ ((Finset.univ : Finset Q).image rep) B)
      ↔ ¬ FloorBad (2 ^ a) (Fintype.card F) ∧
        ∃ q : Q, B < StackProfileRefinement.StackBadCount F C δ (rep q) := by
  constructor
  · intro hnot
    rcases (FloorClosureContract.not_floorGoodFamilyBudget_iff_floorGood_and_exists_member_budget_lt
      (F := F) (A := A) FloorBad a C δ ((Finset.univ : Finset Q).image rep) B).mp hnot with
      ⟨hgood, r, hr, hgt⟩
    rcases Finset.mem_image.mp hr with ⟨q, _hq, rfl⟩
    exact ⟨hgood, ⟨q, by
      simpa [FloorClosureContract.StackBadCount, StackProfileRefinement.StackBadCount] using hgt⟩⟩
  · rintro ⟨hgood, q, hgt⟩
    exact (FloorClosureContract.not_floorGoodFamilyBudget_iff_floorGood_and_exists_member_budget_lt
      (F := F) (A := A) FloorBad a C δ ((Finset.univ : Finset Q).image rep) B).mpr
      ⟨hgood, rep q, Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩, by
        simpa [FloorClosureContract.StackBadCount, StackProfileRefinement.StackBadCount] using hgt⟩

/-- A local scanner certificate that no used fine-profile representative exceeds `B` is exactly a
floor-contract family budget for the used fine-profile representative family. -/
theorem familyBounded_of_no_usedFineProfile_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hnoBudgetBad : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      B < StackProfileRefinement.StackBadCount F C δ (rep q)) :
    FloorClosureContract.FamilyBounded F C δ (usedFineProfileRepFamily fine rep) B := by
  intro r hr
  rcases mem_usedFineProfileRepFamily.mp hr with ⟨q, hused, rfl⟩
  exact le_of_not_gt (fun hgt =>
    hnoBudgetBad ⟨q, hused, by
      simpa [FloorClosureContract.StackBadCount, StackProfileRefinement.StackBadCount] using hgt⟩)

/-- Exact budget certificate for the used fine-profile representative family.  The family is within
budget iff no used fine-profile representative exceeds the budget. -/
theorem familyBounded_usedFineProfileRepFamily_iff_no_usedFineProfile_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι} :
    FloorClosureContract.FamilyBounded F C δ (usedFineProfileRepFamily fine rep) B ↔
      ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
        B < StackProfileRefinement.StackBadCount F C δ (rep q) := by
  constructor
  · intro hbounded hbad
    rcases hbad with ⟨q, hused, hgt⟩
    have hle :
        StackProfileRefinement.StackBadCount F C δ (rep q) ≤ B := by
      simpa [FloorClosureContract.StackBadCount, StackProfileRefinement.StackBadCount] using
        hbounded (rep q) (mem_usedFineProfileRepFamily.mpr ⟨q, hused, rfl⟩)
    exact (not_lt_of_ge hle) hgt
  · exact familyBounded_of_no_usedFineProfile_budget_lt C δ

/-- If a direct scanner already proves that no used fine-profile representative exceeds `B`, then
the floor-good-to-family-budget hypothesis is automatic for the used fine-profile family.  This is a
diagnostic bridge: in this case the least-prime/floor-good lane contributes localization, not the
actual counting budget. -/
theorem floorGoodFamilyBudget_of_no_usedFineProfile_budget_lt
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hnoBudgetBad : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      B < StackProfileRefinement.StackBadCount F C δ (rep q)) :
    FloorClosureContract.FloorGoodFamilyBudget
      (F := F) (A := A) FloorBad a C δ (usedFineProfileRepFamily fine rep) B := by
  intro _hgood
  exact familyBounded_of_no_usedFineProfile_budget_lt C δ hnoBudgetBad

/-- Exact local form of the floor-good family budget for the used fine-profile representative
family.  The remaining floor-to-count theorem is precisely: once the modeled floor predicate is good
at the field prime, no used fine-profile representative exceeds the target budget. -/
theorem floorGoodFamilyBudget_usedFineProfileRepFamily_iff_no_usedFineProfile_budget_lt
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι} :
    FloorClosureContract.FloorGoodFamilyBudget
        (F := F) (A := A) FloorBad a C δ (usedFineProfileRepFamily fine rep) B
      ↔ (¬ FloorBad (2 ^ a) (Fintype.card F) →
        ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
          B < StackProfileRefinement.StackBadCount F C δ (rep q)) := by
  constructor
  · intro hfloor hgood
    exact (familyBounded_usedFineProfileRepFamily_iff_no_usedFineProfile_budget_lt C δ).mp
      (hfloor hgood)
  · intro hlocal hgood
    exact (familyBounded_usedFineProfileRepFamily_iff_no_usedFineProfile_budget_lt C δ).mpr
      (hlocal hgood)

/-- Exact negative form for the used fine-profile representative family. -/
theorem not_floorGoodFamilyBudget_usedFineProfileRepFamily_iff_floorGood_and_exists_usedFineProfile_budget_lt
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι} :
    (¬ FloorClosureContract.FloorGoodFamilyBudget
        (F := F) (A := A) FloorBad a C δ (usedFineProfileRepFamily fine rep) B)
      ↔ ¬ FloorBad (2 ^ a) (Fintype.card F) ∧
        ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
          B < StackProfileRefinement.StackBadCount F C δ (rep q) := by
  constructor
  · intro hnot
    rcases (FloorClosureContract.not_floorGoodFamilyBudget_iff_floorGood_and_exists_member_budget_lt
      (F := F) (A := A) FloorBad a C δ (usedFineProfileRepFamily fine rep) B).mp hnot with
      ⟨hgood, r, hr, hgt⟩
    rcases mem_usedFineProfileRepFamily.mp hr with ⟨q, hused, rfl⟩
    exact ⟨hgood, ⟨q, hused, by
      simpa [FloorClosureContract.StackBadCount, StackProfileRefinement.StackBadCount] using hgt⟩⟩
  · rintro ⟨hgood, q, hused, hgt⟩
    exact (FloorClosureContract.not_floorGoodFamilyBudget_iff_floorGood_and_exists_member_budget_lt
      (F := F) (A := A) FloorBad a C δ (usedFineProfileRepFamily fine rep) B).mpr
      ⟨hgood, rep q, mem_usedFineProfileRepFamily.mpr ⟨q, hused, rfl⟩, by
        simpa [FloorClosureContract.StackBadCount, StackProfileRefinement.StackBadCount] using hgt⟩

/-- Refined-profile floor closure with fine-fiber representatives as the max-containment
certificate. -/
theorem worstCaseIncidenceBounded_of_fineFiberMax_floorFamilyBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hmax : StackProfileRefinement.FineFiberMaxReps F C δ fine rep)
    (hbounded : FloorClosureContract.FamilyBounded F C δ
      (usedFineProfileRepFamily fine rep) B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  FloorClosureContract.worstCaseIncidenceBounded_of_containsGlobalMax C δ
    (floorFamilyContainsGlobalMax_of_fineFiberMaxReps_usedFineProfileFamily C δ hmax) hbounded

/-- Scanner-positive refined-profile floor closure. -/
theorem worstCaseIncidenceBounded_of_no_bad_fineProfile_floorFamilyBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hno : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      (fine (rep q) ≠ q ∨
        ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
          StackProfileRefinement.StackBadCount F C δ (rep q) <
            StackProfileRefinement.StackBadCount F C δ u))
    (hbounded : FloorClosureContract.FamilyBounded F C δ
      (usedFineProfileRepFamily fine rep) B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  FloorClosureContract.worstCaseIncidenceBounded_of_containsGlobalMax C δ
    (floorFamilyContainsGlobalMax_of_no_bad_fineProfile_usedFineProfileFamily C δ hno) hbounded

/-- Fully scanner-facing refined-profile floor closure.  No used fine profile has an invalid or
beaten representative, and no used representative exceeds `B`; therefore the actual worst-case
incidence count is bounded by `B`. -/
theorem worstCaseIncidenceBounded_of_no_bad_fineProfile_budgetScanner
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {Q : Type}
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      (fine (rep q) ≠ q ∨
        ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
          StackProfileRefinement.StackBadCount F C δ (rep q) <
            StackProfileRefinement.StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      B < StackProfileRefinement.StackBadCount F C δ (rep q)) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  StackProfileRefinement.worstCaseIncidenceBounded_of_no_bad_fineProfile_scanner
    (F := F) (A := A) C δ
    (fine := fine)
    (coarse := fun _ : WordStack A (Fin 2) ι => ())
    (project := fun _ : Q => ())
    (rep := rep)
    (by intro u; rfl)
    hnoMaxBad hnoBudgetBad

/-- Delta-star consumer for a fully local refined-profile scanner certificate. -/
theorem deltaStar_pin_of_refinedScannerBudget
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {Q : Type}
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      (fine (rep q) ≠ q ∨
        ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
          StackProfileRefinement.StackBadCount F C δ (rep q) <
            StackProfileRefinement.StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      B < StackProfileRefinement.StackBadCount F C δ (rep q))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  StackProfileRefinement.deltaStar_pin_of_no_bad_fineProfile_scanner
    (F := F) (A := A) C εstar hδ
    (fine := fine)
    (coarse := fun _ : WordStack A (Fin 2) ι => ())
    (project := fun _ : Q => ())
    (rep := rep)
    (by intro u; rfl)
    hnoMaxBad hnoBudgetBad hbudget

/-- Linnik-form floor closure with refined-profile representatives as the max-containment
certificate. -/
theorem deltaStar_pin_of_linnik_candidateListExactSmallest_refinedProfileContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hfloorBudget : FloorClosureContract.FloorGoodFamilyBudget
      (F := F) (A := A) FloorBad a C δ (usedFineProfileRepFamily fine rep) B)
    (hmax : StackProfileRefinement.FineFiberMaxReps F C δ fine rep)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  FloorClosureContract.deltaStar_pin_of_linnik_candidateListExactSmallestMaxContract
    (F := F) (A := A) FloorBad hexact hLeast a ha
    hcardPrime hcardMod hcardPrize C εstar hδ hfloorBudget
    (floorFamilyContainsGlobalMax_of_fineFiberMaxReps_usedFineProfileFamily C δ hmax) hbudget

/-- Linnik-form floor closure with the scanner-positive no-bad-fine-profile certificate. -/
theorem deltaStar_pin_of_linnik_candidateListExactSmallest_refinedScannerContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hfloorBudget : FloorClosureContract.FloorGoodFamilyBudget
      (F := F) (A := A) FloorBad a C δ (usedFineProfileRepFamily fine rep) B)
    (hno : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      (fine (rep q) ≠ q ∨
        ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
          StackProfileRefinement.StackBadCount F C δ (rep q) <
            StackProfileRefinement.StackBadCount F C δ u))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  FloorClosureContract.deltaStar_pin_of_linnik_candidateListExactSmallestMaxContract
    (F := F) (A := A) FloorBad hexact hLeast a ha
    hcardPrime hcardMod hcardPrize C εstar hδ hfloorBudget
    (floorFamilyContainsGlobalMax_of_no_bad_fineProfile_usedFineProfileFamily C δ hno) hbudget

/-- Linnik-form floor closure with only local refined-profile scanner certificates for
max-containment and the family budget.  The direct budget scanner discharges
`FloorGoodFamilyBudget`; the Linnik inputs remain the floor-localization side of the contract. -/
theorem deltaStar_pin_of_linnik_candidateListExactSmallest_refinedBudgetScannerContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {Q : Type} [Finite Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      (fine (rep q) ≠ q ∨
        ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
          StackProfileRefinement.StackBadCount F C δ (rep q) <
            StackProfileRefinement.StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      B < StackProfileRefinement.StackBadCount F C δ (rep q))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  exact
    deltaStar_pin_of_linnik_candidateListExactSmallest_refinedScannerContract
      (F := F) (A := A) FloorBad hexact hLeast a ha
      hcardPrime hcardMod hcardPrize C εstar hδ
      (floorGoodFamilyBudget_of_no_usedFineProfile_budget_lt
        (F := F) (A := A) FloorBad a C δ hnoBudgetBad)
      hnoMaxBad hbudget

/-- No-laundering form of the Linnik refined-budget scanner contract.  Once the scanner already
proves no used fine-profile representative exceeds `B`, the delta-star pin follows directly from
the local scanner theorem; the Linnik/floor-localization inputs are not used for the counting
budget. -/
theorem deltaStar_pin_of_refinedBudgetScanner_of_linnikInputs
    (FloorBad : ℕ -> ℕ -> Prop)
    (_hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (_hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (_ha : 4 ≤ a)
    (_hcardPrime : (Fintype.card F).Prime)
    (_hcardMod : Fintype.card F % (2 ^ a) = 1)
    (_hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {Q : Type}
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      (fine (rep q) ≠ q ∨
        ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
          StackProfileRefinement.StackBadCount F C δ (rep q) <
            StackProfileRefinement.StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      B < StackProfileRefinement.StackBadCount F C δ (rep q))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_refinedScannerBudget C εstar hδ hnoMaxBad hnoBudgetBad hbudget

/-- TZ-form floor closure with refined-profile representatives as the max-containment certificate. -/
theorem deltaStar_pin_of_tz_candidateListExactSmallest_refinedProfileContract
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
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hfloorBudget : FloorClosureContract.FloorGoodFamilyBudget
      (F := F) (A := A) FloorBad a C δ (usedFineProfileRepFamily fine rep) B)
    (hmax : StackProfileRefinement.FineFiberMaxReps F C δ fine rep)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  FloorClosureContract.deltaStar_pin_of_tz_candidateListExactSmallestMaxContract
    (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
    hcardPrime hcardMod hcardPrize C εstar hδ hfloorBudget
    (floorFamilyContainsGlobalMax_of_fineFiberMaxReps_usedFineProfileFamily C δ hmax) hbudget

/-- TZ-form floor closure with the scanner-positive no-bad-fine-profile certificate. -/
theorem deltaStar_pin_of_tz_candidateListExactSmallest_refinedScannerContract
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
    {Q : Type} [Fintype Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hfloorBudget : FloorClosureContract.FloorGoodFamilyBudget
      (F := F) (A := A) FloorBad a C δ (usedFineProfileRepFamily fine rep) B)
    (hno : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      (fine (rep q) ≠ q ∨
        ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
          StackProfileRefinement.StackBadCount F C δ (rep q) <
            StackProfileRefinement.StackBadCount F C δ u))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  FloorClosureContract.deltaStar_pin_of_tz_candidateListExactSmallestMaxContract
    (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
    hcardPrime hcardMod hcardPrize C εstar hδ hfloorBudget
    (floorFamilyContainsGlobalMax_of_no_bad_fineProfile_usedFineProfileFamily C δ hno) hbudget

/-- TZ-form floor closure with only local refined-profile scanner certificates for max-containment
and the family budget. -/
theorem deltaStar_pin_of_tz_candidateListExactSmallest_refinedBudgetScannerContract
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
    {Q : Type} [Finite Q]
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      (fine (rep q) ≠ q ∨
        ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
          StackProfileRefinement.StackBadCount F C δ (rep q) <
            StackProfileRefinement.StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      B < StackProfileRefinement.StackBadCount F C δ (rep q))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  exact
    deltaStar_pin_of_tz_candidateListExactSmallest_refinedScannerContract
      (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
      hcardPrime hcardMod hcardPrize C εstar hδ
      (floorGoodFamilyBudget_of_no_usedFineProfile_budget_lt
        (F := F) (A := A) FloorBad a C δ hnoBudgetBad)
      hnoMaxBad hbudget

/-- No-laundering form of the TZ refined-budget scanner contract.  A local refined-profile scanner
that proves both max-containment and the budget already gives the delta-star lower pin; TZ prime
supply is not the source of that counting bound. -/
theorem deltaStar_pin_of_refinedBudgetScanner_of_tzInputs
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
    {Q : Type}
    {fine : WordStack A (Fin 2) ι -> Q}
    {rep : Q -> WordStack A (Fin 2) ι}
    (hnoMaxBad : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      (fine (rep q) ≠ q ∨
        ∃ u : WordStack A (Fin 2) ι, fine u = q ∧
          StackProfileRefinement.StackBadCount F C δ (rep q) <
            StackProfileRefinement.StackBadCount F C δ u))
    (hnoBudgetBad : ¬ ∃ q : Q, StackProfileRefinement.UsedProfile fine q ∧
      B < StackProfileRefinement.StackBadCount F C δ (rep q))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_refinedScannerBudget C εstar hδ hnoMaxBad hnoBudgetBad hbudget

end ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.floorFamilyContainsGlobalMax_of_fineFiberMaxReps
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.floorFamilyContainsGlobalMax_of_fineFiberMaxReps_usedFineProfileFamily
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.floorFamilyContainsGlobalMax_of_no_bad_fineProfile
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.floorFamilyContainsGlobalMax_of_no_bad_fineProfile_usedFineProfileFamily
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.not_floorFamilyContainsGlobalMax_of_each_fineProfile_rep_beaten
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.not_floorFamilyContainsGlobalMax_fineProfileRepImage_iff_each_rep_beaten
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.not_floorFamilyContainsGlobalMax_of_each_used_fineProfile_rep_beaten
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.not_floorFamilyContainsGlobalMax_usedFineProfileFamily_iff_each_used_rep_beaten
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.familyBounded_fineProfileRepImage_iff_no_fineProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.floorGoodFamilyBudget_fineProfileRepImage_iff_no_fineProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.not_floorGoodFamilyBudget_fineProfileRepImage_iff_floorGood_and_exists_fineProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.familyBounded_of_no_usedFineProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.familyBounded_usedFineProfileRepFamily_iff_no_usedFineProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.floorGoodFamilyBudget_of_no_usedFineProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.floorGoodFamilyBudget_usedFineProfileRepFamily_iff_no_usedFineProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.not_floorGoodFamilyBudget_usedFineProfileRepFamily_iff_floorGood_and_exists_usedFineProfile_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.worstCaseIncidenceBounded_of_fineFiberMax_floorFamilyBounded
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.worstCaseIncidenceBounded_of_no_bad_fineProfile_floorFamilyBounded
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.worstCaseIncidenceBounded_of_no_bad_fineProfile_budgetScanner
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.deltaStar_pin_of_refinedScannerBudget
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.deltaStar_pin_of_linnik_candidateListExactSmallest_refinedProfileContract
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.deltaStar_pin_of_linnik_candidateListExactSmallest_refinedScannerContract
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.deltaStar_pin_of_linnik_candidateListExactSmallest_refinedBudgetScannerContract
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.deltaStar_pin_of_refinedBudgetScanner_of_linnikInputs
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.deltaStar_pin_of_tz_candidateListExactSmallest_refinedProfileContract
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.deltaStar_pin_of_tz_candidateListExactSmallest_refinedScannerContract
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.deltaStar_pin_of_tz_candidateListExactSmallest_refinedBudgetScannerContract
#print axioms ArkLib.ProximityGap.Frontier.RefinedProfileFloorBridge.deltaStar_pin_of_refinedBudgetScanner_of_tzInputs
