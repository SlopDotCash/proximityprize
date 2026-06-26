/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorLinnikTZClosure
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# The full off-BGK floor closure contract

The smallest-prime floor-localization lane has a real off-BGK component:

* `FloorLocalizationUniform` identifies the modeled floor-bad primes with the least prime
  `1 mod 2^a`;
* `LinnikLeastPrimeBelowPrize`, or the sharper `TZPrimeSupply` bridge, puts that least prime below
  prize scale.

Those two inputs prove only `¬ FloorBad (2^a) p` for the modeled binder/floor predicate.  The
delta-star lower pin still consumes `WorstCaseIncidenceBounded`, a universal count over every
`WordStack`.

This file records the complete contract needed to turn the off-BGK lane into a prize-facing lower
bound:

1. localization plus least-prime supply gives `floor-good`;
2. `floor-good` must imply a budget on the chosen finite stack family;
3. that family must dominate all stacks for the actual MCA bad-scalar count.

Only after all three steps does the existing open-core conditional pin apply.  The last two
hypotheses are intentionally explicit: they are the missing sparse-domination/classification
content, not consequences of Linnik or Thorner--Zaman.
-/

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.FloorLocalization
open ArkLib.ProximityGap.Frontier.FloorLinnikTZClosure

namespace ArkLib.ProximityGap.Frontier.FloorClosureContract

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The actual bad-scalar count appearing in `WorstCaseIncidenceBounded`.  This local copy keeps the
contract independently checkable without importing another scratch frontier file. -/
noncomputable def StackBadCount (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) : ℕ := by
  classical
  exact (Finset.univ.filter (fun γ : K => mcaEvent (F := K) C δ (u 0) (u 1) γ)).card

/-- Every representative in a finite floor family satisfies the one-stack budget. -/
def FamilyBounded (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) : Prop :=
  ∀ r ∈ R, StackBadCount K C δ r ≤ B

/-- Failure of a finite-family budget is exactly an above-budget member. -/
theorem not_familyBounded_iff_exists_member_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) :
    (¬ FamilyBounded F C δ R B) ↔
      ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧ B < StackBadCount F C δ r := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro r hr
    exact le_of_not_gt (fun hgt => hnone ⟨r, hr, hgt⟩)
  · rintro ⟨r, hr, hgt⟩ hbounded
    exact (not_lt_of_ge (hbounded r hr)) hgt

/-- A finite floor family dominates if every stack is no worse than some family member. -/
def FamilyDominates (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    ∃ r ∈ R, StackBadCount K C δ u ≤ StackBadCount K C δ r

/-- A finite family contains a true global maximizer for the actual bad-scalar count. -/
def FamilyContainsGlobalMax (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) : Prop :=
  ∃ r ∈ R, ∀ u : WordStack A (Fin 2) ι,
    StackBadCount K C δ u ≤ StackBadCount K C δ r

/-- If a family contains a true global maximizer, it dominates all stacks. -/
theorem familyDominates_of_containsGlobalMax
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax : FamilyContainsGlobalMax F C δ R) :
    FamilyDominates F C δ R := by
  intro u
  rcases hmax with ⟨r, hr, hdom⟩
  exact ⟨r, hr, hdom u⟩

/-- Conversely, any dominating finite family contains a member that is a true global maximizer.
Proof idea: take an internal maximum of the family; domination compares every outside stack to some
family member, and internal maximality moves that comparison to the selected representative. -/
theorem containsGlobalMax_of_familyDominates
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hdom : FamilyDominates F C δ R) :
    FamilyContainsGlobalMax F C δ R := by
  classical
  rcases hdom (0 : WordStack A (Fin 2) ι) with ⟨r₀, hr₀, _hr₀⟩
  have hR : R.Nonempty := ⟨r₀, hr₀⟩
  obtain ⟨rMax, hrMax, hmax⟩ :=
    R.exists_max_image (fun r : WordStack A (Fin 2) ι => StackBadCount F C δ r) hR
  refine ⟨rMax, hrMax, ?_⟩
  intro u
  rcases hdom u with ⟨r, hr, hur⟩
  exact le_trans hur (hmax r hr)

/-- Domination by a finite family is exactly containment of a true global maximizer.  Thus a
compressed floor family cannot merely be bounded; it must include, or prove equivalent to, an actual
worst stack for the MCA bad-scalar count. -/
theorem familyDominates_iff_containsGlobalMax
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) :
    FamilyDominates F C δ R ↔ FamilyContainsGlobalMax F C δ R :=
  ⟨containsGlobalMax_of_familyDominates C δ,
    familyDominates_of_containsGlobalMax C δ⟩

/-- Failure to contain a global maximizer is exactly memberwise beatability: every proposed
representative has some stack with strictly larger bad-scalar count.  This is the exact scanner
certificate for refuting max containment. -/
theorem not_familyContainsGlobalMax_iff_each_member_beaten
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) :
    (¬ FamilyContainsGlobalMax F C δ R) ↔
      ∀ r ∈ R, ∃ u : WordStack A (Fin 2) ι,
        StackBadCount F C δ r < StackBadCount F C δ u := by
  constructor
  · intro hno r hr
    by_contra hnone
    have hdom : ∀ u : WordStack A (Fin 2) ι,
        StackBadCount F C δ u ≤ StackBadCount F C δ r := by
      intro u
      exact le_of_not_gt (by
        intro hgt
        exact hnone ⟨u, hgt⟩)
    exact hno ⟨r, hr, hdom⟩
  · intro hbeat hmax
    rcases hmax with ⟨r, hr, hdom⟩
    rcases hbeat r hr with ⟨u, hlt⟩
    exact (not_lt_of_ge (hdom u)) hlt

/-- Failure of finite-family domination is exactly memberwise beatability.  A scanner that can beat
each proposed floor/profile representative has fully refuted that compressed catalogue; no single
stack has to beat the entire family at once. -/
theorem not_familyDominates_iff_each_member_beaten
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) :
    (¬ FamilyDominates F C δ R) ↔
      ∀ r ∈ R, ∃ u : WordStack A (Fin 2) ι,
        StackBadCount F C δ r < StackBadCount F C δ u := by
  constructor
  · intro hnot
    exact (not_familyContainsGlobalMax_iff_each_member_beaten C δ R).mp
      (fun hmax => hnot ((familyDominates_iff_containsGlobalMax C δ R).mpr hmax))
  · intro hbeat hdom
    exact (not_familyContainsGlobalMax_iff_each_member_beaten C δ R).mpr hbeat
      ((familyDominates_iff_containsGlobalMax C δ R).mp hdom)

/-- The exhaustive family of all stacks dominates tautologically.  This is the calibration point for
the floor route: any smaller floor/binder catalogue must prove a genuine compression theorem beyond
this all-stack baseline. -/
theorem familyDominates_univ
    (C : Set (ι -> A)) (δ : ℝ≥0) :
    FamilyDominates F C δ (Finset.univ : Finset (WordStack A (Fin 2) ι)) := by
  intro u
  exact ⟨u, Finset.mem_univ u, le_rfl⟩

/-- Bounding the exhaustive family is exactly the original universal incidence hypothesis.  Thus an
all-stack scanner certificate is logically sufficient, while any useful floor-localization proof must
replace this infeasible family by a dominated compressed family. -/
theorem worstCaseIncidenceBounded_iff_familyBounded_univ
    (C : Set (ι -> A)) (δ : ℝ≥0) (B : ℕ) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B
      ↔ FamilyBounded F C δ (Finset.univ : Finset (WordStack A (Fin 2) ι)) B := by
  constructor
  · intro hI r _hr
    exact hI r
  · intro hR u
    exact hR u (Finset.mem_univ u)

/-- Delta-star consumer for a literal exhaustive all-stack certificate.  This is deliberately not a
compressed floor proof; it records the baseline that a scanner would have to certify directly if no
dominating smaller family is available. -/
theorem deltaStar_pin_of_exhaustiveFamilyBounded
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    (hbounded : FamilyBounded F C δ (Finset.univ : Finset (WordStack A (Fin 2) ι)) B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    ((worstCaseIncidenceBounded_iff_familyBounded_univ C δ B).mpr hbounded)
    hbudget

/-- Bounding a dominating finite family gives the full worst-case incidence hypothesis. -/
theorem worstCaseIncidenceBounded_of_familyDominates
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hdom : FamilyDominates F C δ R)
    (hR : FamilyBounded F C δ R B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro u
  rcases hdom u with ⟨r, hr, hur⟩
  exact le_trans hur (hR r hr)

/-- Delta-star consumer for a dominating finite family. -/
theorem deltaStar_pin_of_familyDominates
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hdom : FamilyDominates F C δ R)
    (hbounded : FamilyBounded F C δ R B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_familyDominates C δ hdom hbounded)
    hbudget

/-- Bounding a family that contains a true global maximizer gives the full worst-case incidence
hypothesis.  This is the sharper operational form of the domination bridge. -/
theorem worstCaseIncidenceBounded_of_containsGlobalMax
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax : FamilyContainsGlobalMax F C δ R)
    (hR : FamilyBounded F C δ R B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_familyDominates C δ
    (familyDominates_of_containsGlobalMax C δ hmax) hR

/-- Delta-star consumer in global-max-containment form.  A compressed floor family is useful exactly
when it contains a true maximizer and that family is within budget. -/
theorem deltaStar_pin_of_containsGlobalMax
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hmax : FamilyContainsGlobalMax F C δ R)
    (hbounded : FamilyBounded F C δ R B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_familyDominates C εstar hδ
    (familyDominates_of_containsGlobalMax C δ hmax) hbounded hbudget

/-- A stack beating every family member refutes finite-family domination. -/
theorem not_familyDominates_of_exists_strictly_larger_than_all
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {R : Finset (WordStack A (Fin 2) ι)}
    {uWitness : WordStack A (Fin 2) ι}
    (hgt : ∀ r ∈ R, StackBadCount F C δ r < StackBadCount F C δ uWitness) :
    ¬ FamilyDominates F C δ R := by
  intro hdom
  rcases hdom uWitness with ⟨r, hr, hur⟩
  exact (not_lt_of_ge hur) (hgt r hr)

/-- A more local scanner refutation: if every family member can be beaten by some stack (the witness
may depend on the member), then the family contains no global maximizer and cannot dominate. -/
theorem not_familyDominates_of_each_member_beaten
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hbeat : ∀ r ∈ R, ∃ u : WordStack A (Fin 2) ι,
      StackBadCount F C δ r < StackBadCount F C δ u) :
    ¬ FamilyDominates F C δ R := by
  intro hdom
  rcases containsGlobalMax_of_familyDominates C δ hdom with ⟨r, hr, hmax⟩
  rcases hbeat r hr with ⟨u, hlt⟩
  exact (not_lt_of_ge (hmax u)) hlt

/-- A stack above budget refutes the full worst-case incidence hypothesis. -/
theorem familyBounded_and_counterStack_not_worstCaseIncidenceBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    {uWitness : WordStack A (Fin 2) ι}
    (hR : FamilyBounded F C δ R B)
    (hgt : B < StackBadCount F C δ uWitness) :
    FamilyBounded F C δ R B
      ∧ ¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
          (F := F) (A := A) C δ B := by
  refine ⟨hR, ?_⟩
  intro hI
  exact (not_lt_of_ge (hI uWitness)) hgt

/-- Exact refutation form of the universal incidence budget: it fails precisely when some stack is
above the target bad-scalar budget. -/
theorem not_worstCaseIncidenceBounded_iff_exists_stack_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0) (B : ℕ) :
    (¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B)
      ↔ ∃ u : WordStack A (Fin 2) ι, B < StackBadCount F C δ u := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u
    exact le_of_not_gt (fun hgt => hnone ⟨u, hgt⟩)
  · rintro ⟨u, hgt⟩ hI
    exact (not_lt_of_ge (hI u)) hgt

/-- A bounded family beaten by one outside stack is not a domination proof. -/
theorem familyBounded_not_dominationProof_of_exists_strictly_larger_than_all
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    {uWitness : WordStack A (Fin 2) ι}
    (hR : FamilyBounded F C δ R B)
    (hgt : ∀ r ∈ R, StackBadCount F C δ r < StackBadCount F C δ uWitness) :
    FamilyBounded F C δ R B ∧ ¬ FamilyDominates F C δ R :=
  ⟨hR, not_familyDominates_of_exists_strictly_larger_than_all C δ hgt⟩

/-- The missing floor-to-family bridge: once the prize prime is good for the modeled floor predicate,
the selected finite stack family is within the count budget.  This is not supplied by the
least-prime theorem; it is the additional algebra/incidence theorem a floor proof must provide. -/
def FloorGoodFamilyBudget (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) : Prop :=
  ¬ FloorBad (2 ^ a) (Fintype.card F) ->
    FamilyBounded F C δ R B

/-- Failure of the floor-good-to-family-budget bridge means the modeled floor predicate is good at
the field prime, while the selected family is not actually within budget. -/
theorem not_floorGoodFamilyBudget_iff_floorGood_and_not_familyBounded
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) :
    (¬ FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B) ↔
      ¬ FloorBad (2 ^ a) (Fintype.card F) ∧ ¬ FamilyBounded F C δ R B := by
  constructor
  · intro hnot
    by_cases hgood : ¬ FloorBad (2 ^ a) (Fintype.card F)
    · refine ⟨hgood, ?_⟩
      intro hbounded
      exact hnot (fun _ => hbounded)
    · exfalso
      apply hnot
      intro hgood'
      exact False.elim (hgood hgood')
  · rintro ⟨hgood, hnotBounded⟩ hfloorBudget
    exact hnotBounded (hfloorBudget hgood)

/-- Exact scanner refutation for the missing floor-to-family budget theorem: it fails precisely
when the modeled floor predicate is good at the field prime and some selected representative is
above the target budget. -/
theorem not_floorGoodFamilyBudget_iff_floorGood_and_exists_member_budget_lt
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) :
    (¬ FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B) ↔
      ¬ FloorBad (2 ^ a) (Fintype.card F) ∧
        ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧ B < StackBadCount F C δ r := by
  constructor
  · intro hnot
    rcases (not_floorGoodFamilyBudget_iff_floorGood_and_not_familyBounded
      (F := F) (A := A) FloorBad a C δ R B).mp hnot with
      ⟨hgood, hnotBounded⟩
    exact ⟨hgood, (not_familyBounded_iff_exists_member_budget_lt C δ R B).mp hnotBounded⟩
  · rintro ⟨hgood, hmember⟩
    exact (not_floorGoodFamilyBudget_iff_floorGood_and_not_familyBounded
      (F := F) (A := A) FloorBad a C δ R B).mpr
      ⟨hgood, (not_familyBounded_iff_exists_member_budget_lt C δ R B).mpr hmember⟩

/-- Concrete field-level floor closure certificate.  This is the state after the arithmetic
localization step has already produced floor-goodness at the current field size: the floor predicate
is good at `|F|`, the selected family is budgeted, and the family dominates every stack. -/
def FloorClosureAtField (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) : Prop :=
  ¬ FloorBad (2 ^ a) (Fintype.card F) ∧
    FamilyBounded F C δ R B ∧ FamilyDominates F C δ R

/-- Floor-goodness plus the floor-to-family budget bridge and domination produce the concrete
field-level certificate. -/
theorem floorClosureAtField_of_floorGoodFamilyBudget
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {R : Finset (WordStack A (Fin 2) ι)} {B : ℕ}
    (hgood : ¬ FloorBad (2 ^ a) (Fintype.card F))
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hdom : FamilyDominates F C δ R) :
    FloorClosureAtField (F := F) (A := A) FloorBad a C δ R B :=
  ⟨hgood, hfloorBudget hgood, hdom⟩

/-- A concrete field-level floor closure certificate gives the actual universal incidence
hypothesis. -/
theorem worstCaseIncidenceBounded_of_floorClosureAtField
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hcert : FloorClosureAtField (F := F) (A := A) FloorBad a C δ R B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_familyDominates C δ hcert.2.2 hcert.2.1

/-- Delta-star consumer for a concrete field-level floor closure certificate. -/
theorem deltaStar_pin_of_floorClosureAtField
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hcert : FloorClosureAtField (F := F) (A := A) FloorBad a C δ R B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_familyDominates C εstar hδ hcert.2.2 hcert.2.1 hbudget

/-- Equivalent max-containment normal form for a concrete field-level floor certificate.  The
family-domination field is not extra magic: it says exactly that the proposed floor family contains
a true global maximizer for the actual bad-scalar count. -/
theorem floorClosureAtField_iff_floorGood_familyBounded_containsGlobalMax
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) :
    FloorClosureAtField (F := F) (A := A) FloorBad a C δ R B ↔
      ¬ FloorBad (2 ^ a) (Fintype.card F) ∧
        FamilyBounded F C δ R B ∧ FamilyContainsGlobalMax F C δ R := by
  constructor
  · intro hcert
    exact ⟨hcert.1, hcert.2.1,
      (familyDominates_iff_containsGlobalMax C δ R).mp hcert.2.2⟩
  · rintro ⟨hgood, hbounded, hmax⟩
    exact ⟨hgood, hbounded,
      (familyDominates_iff_containsGlobalMax C δ R).mpr hmax⟩

/-- Concrete field-level floor closure can be supplied directly by a bounded family that contains a
true global maximizer. -/
theorem floorClosureAtField_of_floorGood_familyBounded_containsGlobalMax
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {R : Finset (WordStack A (Fin 2) ι)} {B : ℕ}
    (hgood : ¬ FloorBad (2 ^ a) (Fintype.card F))
    (hbounded : FamilyBounded F C δ R B)
    (hmax : FamilyContainsGlobalMax F C δ R) :
    FloorClosureAtField (F := F) (A := A) FloorBad a C δ R B :=
  (floorClosureAtField_iff_floorGood_familyBounded_containsGlobalMax
    (F := F) (A := A) FloorBad a C δ R B).mpr ⟨hgood, hbounded, hmax⟩

/-- Exact max-containment scanner form for the concrete floor-closure certificate.  It fails
precisely when the floor predicate is bad at the field size, or a proposed family member is above
budget, or the family does not contain a true global maximizer. -/
theorem not_floorClosureAtField_iff_bad_or_member_budget_lt_or_not_containsGlobalMax
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) :
    (¬ FloorClosureAtField (F := F) (A := A) FloorBad a C δ R B) ↔
      FloorBad (2 ^ a) (Fintype.card F) ∨
        (∃ r : WordStack A (Fin 2) ι, r ∈ R ∧ B < StackBadCount F C δ r) ∨
          ¬ FamilyContainsGlobalMax F C δ R := by
  constructor
  · intro hnot
    by_cases hbad : FloorBad (2 ^ a) (Fintype.card F)
    · exact Or.inl hbad
    · have hnotBudgetOrMax :
          ¬ (FamilyBounded F C δ R B ∧ FamilyContainsGlobalMax F C δ R) := by
        intro hpair
        exact hnot
          ((floorClosureAtField_iff_floorGood_familyBounded_containsGlobalMax
            (F := F) (A := A) FloorBad a C δ R B).mpr ⟨hbad, hpair⟩)
      rw [not_and_or] at hnotBudgetOrMax
      rcases hnotBudgetOrMax with hnotBudget | hnotMax
      · exact Or.inr <| Or.inl
          ((not_familyBounded_iff_exists_member_budget_lt C δ R B).mp hnotBudget)
      · exact Or.inr <| Or.inr hnotMax
  · rintro (hbad | hbudgetOrMax) hcert
    · exact hcert.1 hbad
    · rcases hbudgetOrMax with hmember | hnotMax
      · exact ((not_familyBounded_iff_exists_member_budget_lt C δ R B).mpr hmember)
          hcert.2.1
      · exact hnotMax
          ((familyDominates_iff_containsGlobalMax C δ R).mp hcert.2.2)

/-- Exact scanner form for the concrete floor-closure certificate.  It fails precisely when the
floor predicate is still bad at the current field size, or some selected representative is above
budget, or every selected representative can be beaten by another stack. -/
theorem not_floorClosureAtField_iff_bad_or_member_budget_lt_or_each_member_beaten
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) :
    (¬ FloorClosureAtField (F := F) (A := A) FloorBad a C δ R B) ↔
      FloorBad (2 ^ a) (Fintype.card F) ∨
        (∃ r : WordStack A (Fin 2) ι, r ∈ R ∧ B < StackBadCount F C δ r) ∨
          ∀ r ∈ R, ∃ u : WordStack A (Fin 2) ι,
            StackBadCount F C δ r < StackBadCount F C δ u := by
  classical
  unfold FloorClosureAtField
  constructor
  · intro hnot
    by_cases hbad : FloorBad (2 ^ a) (Fintype.card F)
    · exact Or.inl hbad
    · have hnotBudgetOrDom :
          ¬ (FamilyBounded F C δ R B ∧ FamilyDominates F C δ R) := by
        intro hpair
        exact hnot ⟨hbad, hpair⟩
      rw [not_and_or] at hnotBudgetOrDom
      rcases hnotBudgetOrDom with hnotBudget | hnotDom
      · exact Or.inr <| Or.inl
          ((not_familyBounded_iff_exists_member_budget_lt C δ R B).mp hnotBudget)
      · exact Or.inr <| Or.inr
          ((not_familyDominates_iff_each_member_beaten C δ R).mp hnotDom)
  · rintro (hbad | hbudgetOrDom) hcert
    · exact hcert.1 hbad
    · rcases hbudgetOrDom with hmember | hbeat
      · exact ((not_familyBounded_iff_exists_member_budget_lt C δ R B).mpr hmember) hcert.2.1
      · exact ((not_familyDominates_iff_each_member_beaten C δ R).mpr hbeat) hcert.2.2

/-- Scanner-facing singleton exactness at every dyadic rung.  This is stronger than saying a
candidate list matches the least-prime rule: it identifies the true floor-bad predicate with that
singleton inside the split-prime family. -/
def CandidateListExactSmallestFamily (FloorBad : ℕ -> ℕ -> Prop) : Prop :=
  ∀ a : ℕ, 4 ≤ a ->
    CandidateListExactInAP FloorBad (2 ^ a)
      [smallestPrime1ModN (2 ^ a) (2 ^ (5 * a))]

/-- Exact singleton candidate-list evidence at one dyadic rung. -/
def CandidateListExactAt (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ) : Prop :=
  CandidateListExactInAP FloorBad (2 ^ a)
    [smallestPrime1ModN (2 ^ a) (2 ^ (5 * a))]

/-- The missing tower propagation theorem for scanner exactness.  If this holds, one exact base
rung promotes to exactness at every dyadic rung. -/
def CandidateListExactSuccessor (FloorBad : ℕ -> ℕ -> Prop) : Prop :=
  ∀ a : ℕ, 4 ≤ a -> CandidateListExactAt FloorBad a ->
    CandidateListExactAt FloorBad (a + 1)

/-- A base exact scanner certificate plus a successor propagation theorem gives the full uniform
scanner-facing input.  This is the positive replacement for finite-rung extrapolation. -/
theorem candidateListExactSmallestFamily_of_base_and_successor
    (FloorBad : ℕ -> ℕ -> Prop)
    (hbase : CandidateListExactAt FloorBad 4)
    (hstep : CandidateListExactSuccessor FloorBad) :
    CandidateListExactSmallestFamily FloorBad := by
  intro a ha
  exact Nat.le_induction hbase (fun n hn ih => hstep n hn ih) a ha

/-- A verified prefix plus the same successor propagation theorem also gives the full uniform
scanner-facing input.  The current `a = 4,5` evidence fits this shape; the missing mathematics is the
successor step, not more list arithmetic. -/
theorem candidateListExactSmallestFamily_of_prefix_and_successor
    (FloorBad : ℕ -> ℕ -> Prop) {cutoff : ℕ}
    (hcutoff : 4 ≤ cutoff)
    (hprefix : ∀ a : ℕ, 4 ≤ a -> a ≤ cutoff -> CandidateListExactAt FloorBad a)
    (hstep : CandidateListExactSuccessor FloorBad) :
    CandidateListExactSmallestFamily FloorBad :=
  candidateListExactSmallestFamily_of_base_and_successor FloorBad
    (hprefix 4 le_rfl hcutoff) hstep

/-- Uniform singleton exactness fails exactly when some dyadic rung at or above `a = 4` fails the
scanner exactness test. -/
theorem not_candidateListExactSmallestFamily_iff_exists_rung_not_exact
    (FloorBad : ℕ -> ℕ -> Prop) :
    (¬ CandidateListExactSmallestFamily FloorBad) ↔
      ∃ a : ℕ, 4 ≤ a ∧ ¬ CandidateListExactAt FloorBad a := by
  unfold CandidateListExactSmallestFamily CandidateListExactAt
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro a ha
    by_contra hbad
    exact hnone ⟨a, ha, hbad⟩
  · rintro ⟨a, ha, hbad⟩ hsmall
    exact hbad (hsmall a ha)

/-- Failure of the successor propagation theorem is exactly an exact rung whose successor is not
exact.  This is the refutable form of the tower step: a scanner can kill the step by finding one
such adjacent pair. -/
theorem not_candidateListExactSuccessor_iff_exists_exact_rung_next_fails
    (FloorBad : ℕ -> ℕ -> Prop) :
    (¬ CandidateListExactSuccessor FloorBad) ↔
      ∃ a : ℕ, 4 ≤ a ∧ CandidateListExactAt FloorBad a ∧
        ¬ CandidateListExactAt FloorBad (a + 1) := by
  unfold CandidateListExactSuccessor
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro a ha hexact
    by_contra hnext
    exact hnone ⟨a, ha, hexact, hnext⟩
  · rintro ⟨a, ha, hexact, hnext⟩ hstep
    exact hnext (hstep a ha hexact)

/-- A failed successor rung rules out the uniform singleton exactness hypothesis needed by the
off-BGK floor-localization lane. -/
theorem not_candidateListExactSmallestFamily_of_next_failure
    (FloorBad : ℕ -> ℕ -> Prop) {a : ℕ}
    (ha : 4 ≤ a)
    (hfail : ¬ CandidateListExactAt FloorBad (a + 1)) :
    ¬ CandidateListExactSmallestFamily FloorBad := by
  intro hsmall
  exact hfail (hsmall (a + 1) (Nat.le_trans ha (Nat.le_succ a)))

/-- Exact singleton candidate lists are the scanner-facing route to `FloorLocalizationUniform`. -/
theorem floorLocalizationUniform_of_candidateListExactSmallestFamily
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : CandidateListExactSmallestFamily FloorBad) :
    FloorLocalizationUniform FloorBad :=
  floorLocalizationUniform_of_candidateListExactSmallest FloorBad hexact

/-- Linnik-form localization plus the floor-to-family bridge gives a bounded candidate family. -/
theorem familyBounded_of_linnik_floorGood
    (FloorBad : ℕ -> ℕ -> Prop)
    (hUnif : FloorLocalizationUniform FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B) :
    FamilyBounded F C δ R B := by
  have hgood : ¬ FloorBad (2 ^ a) (Fintype.card F) :=
    floor_closes_by_linnik FloorBad hUnif hLeast
      a ha (Fintype.card F) hcardPrime hcardMod hcardPrize
  exact hfloorBudget hgood

/-- Scanner-facing Linnik form: exact singleton floor-bad lists plus the least-prime premise give a
bounded candidate family once floor-goodness is known to budget that family. -/
theorem familyBounded_of_linnik_candidateListExactSmallest
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B) :
    FamilyBounded F C δ R B :=
  familyBounded_of_linnik_floorGood
    (F := F) (A := A) FloorBad
    (floorLocalizationUniform_of_candidateListExactSmallestFamily FloorBad hexact)
    hLeast a ha hcardPrime hcardMod hcardPrize C δ hfloorBudget

/-- The Linnik-form full contract: if floor-goodness budgets a dominating finite family, then the
actual universal open-core incidence hypothesis follows. -/
theorem worstCaseIncidenceBounded_of_linnik_floorClosureContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hUnif : FloorLocalizationUniform FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hdom : FamilyDominates F C δ R) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_familyDominates C δ hdom
    (familyBounded_of_linnik_floorGood
      (F := F) (A := A) FloorBad hUnif hLeast a ha
      hcardPrime hcardMod hcardPrize C δ hfloorBudget)

/-- Scanner-facing Linnik full contract: exact singleton floor-bad lists, sub-prize least-prime
supply, floor-to-family budget, and family domination imply the actual universal incidence bound. -/
theorem worstCaseIncidenceBounded_of_linnik_candidateListExactSmallestContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hdom : FamilyDominates F C δ R) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_linnik_floorClosureContract
    (F := F) (A := A) FloorBad
    (floorLocalizationUniform_of_candidateListExactSmallestFamily FloorBad hexact)
    hLeast a ha hcardPrime hcardMod hcardPrize C δ hfloorBudget hdom

/-- Delta-star consumer for the Linnik-form full contract.  This is the honest final shape of a
floor-localization proof: localization, least-prime supply, floor-to-family budget, family
domination, and the scaled budget. -/
theorem deltaStar_pin_of_linnik_floorClosureContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hUnif : FloorLocalizationUniform FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hdom : FamilyDominates F C δ R)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_familyDominates C εstar hδ hdom
    (familyBounded_of_linnik_floorGood
      (F := F) (A := A) FloorBad hUnif hLeast a ha
      hcardPrime hcardMod hcardPrize C δ hfloorBudget)
    hbudget

/-- Scanner-facing Linnik delta-star consumer.  This is the same full contract as
`deltaStar_pin_of_linnik_floorClosureContract`, but with the uniform localization input replaced by
exact singleton candidate-list evidence. -/
theorem deltaStar_pin_of_linnik_candidateListExactSmallestContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hdom : FamilyDominates F C δ R)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_linnik_floorClosureContract
    (F := F) (A := A) FloorBad
    (floorLocalizationUniform_of_candidateListExactSmallestFamily FloorBad hexact)
    hLeast a ha hcardPrime hcardMod hcardPrize C εstar hδ hfloorBudget hdom hbudget

/-- Scanner-facing Linnik full contract, stated with the equivalent global-max containment
obligation instead of the abstract family-domination predicate. -/
theorem worstCaseIncidenceBounded_of_linnik_candidateListExactSmallestMaxContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hmax : FamilyContainsGlobalMax F C δ R) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_linnik_candidateListExactSmallestContract
    (F := F) (A := A) FloorBad hexact hLeast a ha
    hcardPrime hcardMod hcardPrize C δ hfloorBudget
    (familyDominates_of_containsGlobalMax C δ hmax)

/-- Scanner-facing Linnik delta-star consumer in global-max-containment form. -/
theorem deltaStar_pin_of_linnik_candidateListExactSmallestMaxContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hmax : FamilyContainsGlobalMax F C δ R)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_linnik_candidateListExactSmallestContract
    (F := F) (A := A) FloorBad hexact hLeast a ha
    hcardPrime hcardMod hcardPrize C εstar hδ hfloorBudget
    (familyDominates_of_containsGlobalMax C δ hmax) hbudget

/-- TZ-form localization plus the floor-to-family bridge gives a bounded candidate family. -/
theorem familyBounded_of_tz_floorGood
    (FloorBad : ℕ -> ℕ -> Prop)
    (hUnif : FloorLocalizationUniform FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B) :
    FamilyBounded F C δ R B := by
  have hgood : ¬ FloorBad (2 ^ a) (Fintype.card F) :=
    floor_closes_by_tzSupplyFamily FloorBad hUnif hβ hTZfam
      a ha (Fintype.card F) hcardPrime hcardMod hcardPrize
  exact hfloorBudget hgood

/-- Scanner-facing TZ form: exact singleton floor-bad lists plus a uniform TZ supply give a bounded
candidate family once floor-goodness is known to budget that family. -/
theorem familyBounded_of_tz_candidateListExactSmallest
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B) :
    FamilyBounded F C δ R B :=
  familyBounded_of_tz_floorGood
    (F := F) (A := A) FloorBad
    (floorLocalizationUniform_of_candidateListExactSmallestFamily FloorBad hexact)
    hβ hTZfam a ha hcardPrime hcardMod hcardPrize C δ hfloorBudget

/-- TZ-form full contract: a uniform TZ supply still needs the same floor-to-family and domination
bridges before it becomes the actual universal incidence bound. -/
theorem worstCaseIncidenceBounded_of_tz_floorClosureContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hUnif : FloorLocalizationUniform FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hdom : FamilyDominates F C δ R) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_familyDominates C δ hdom
    (familyBounded_of_tz_floorGood
      (F := F) (A := A) FloorBad hUnif hβ hTZfam a ha
      hcardPrime hcardMod hcardPrize C δ hfloorBudget)

/-- Scanner-facing TZ full contract: exact singleton floor-bad lists, uniform TZ supply,
floor-to-family budget, and family domination imply the actual universal incidence bound. -/
theorem worstCaseIncidenceBounded_of_tz_candidateListExactSmallestContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hdom : FamilyDominates F C δ R) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_tz_floorClosureContract
    (F := F) (A := A) FloorBad
    (floorLocalizationUniform_of_candidateListExactSmallestFamily FloorBad hexact)
    hβ hTZfam a ha hcardPrime hcardMod hcardPrize C δ hfloorBudget hdom

/-- Scanner-facing TZ delta-star consumer.  This is the current best honest shape of the off-BGK
floor lane under the TZ least-prime supply: exact scanner evidence, floor-to-family budget,
domination, and the scaled MCA budget. -/
theorem deltaStar_pin_of_tz_candidateListExactSmallestContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hdom : FamilyDominates F C δ R)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_familyDominates C εstar hδ hdom
    (familyBounded_of_tz_candidateListExactSmallest
      (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
      hcardPrime hcardMod hcardPrize C δ hfloorBudget)
    hbudget

/-- Scanner-facing TZ full contract, stated with global-max containment instead of the abstract
family-domination predicate. -/
theorem worstCaseIncidenceBounded_of_tz_candidateListExactSmallestMaxContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hmax : FamilyContainsGlobalMax F C δ R) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_tz_candidateListExactSmallestContract
    (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
    hcardPrime hcardMod hcardPrize C δ hfloorBudget
    (familyDominates_of_containsGlobalMax C δ hmax)

/-- Scanner-facing TZ delta-star consumer in global-max-containment form. -/
theorem deltaStar_pin_of_tz_candidateListExactSmallestMaxContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hmax : FamilyContainsGlobalMax F C δ R)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_tz_candidateListExactSmallestContract
    (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
    hcardPrime hcardMod hcardPrize C εstar hδ hfloorBudget
    (familyDominates_of_containsGlobalMax C δ hmax) hbudget

/-- A scanner witness that beats every member of the floor-good family refutes the domination part
of the closure contract. -/
theorem floorGood_familyBudget_not_dominationProof_of_larger_than_all
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    {uWitness : WordStack A (Fin 2) ι}
    (hgood : ¬ FloorBad (2 ^ a) (Fintype.card F))
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hgt : ∀ r ∈ R, StackBadCount F C δ r < StackBadCount F C δ uWitness) :
    FamilyBounded F C δ R B ∧ ¬ FamilyDominates F C δ R :=
  familyBounded_not_dominationProof_of_exists_strictly_larger_than_all
    C δ (hfloorBudget hgood) hgt

/-- Local scanner refutation for a floor-good family: if every family member can be beaten by some
stack, then the floor-good budget is still only a bounded-family result, not a domination proof. -/
theorem floorGood_familyBudget_not_dominationProof_of_each_member_beaten
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hgood : ¬ FloorBad (2 ^ a) (Fintype.card F))
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hbeat : ∀ r ∈ R, ∃ u : WordStack A (Fin 2) ι,
      StackBadCount F C δ r < StackBadCount F C δ u) :
    FamilyBounded F C δ R B ∧ ¬ FamilyDominates F C δ R :=
  ⟨hfloorBudget hgood, not_familyDominates_of_each_member_beaten C δ hbeat⟩

/-- A scanner witness above the budget refutes the universal incidence conclusion even if
floor-goodness bounded the proposed family. -/
theorem floorGood_familyBudget_not_worstCaseIncidenceBounded_of_counterStack
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    {uWitness : WordStack A (Fin 2) ι}
    (hgood : ¬ FloorBad (2 ^ a) (Fintype.card F))
    (hfloorBudget : FloorGoodFamilyBudget (F := F) (A := A) FloorBad a C δ R B)
    (hgt : B < StackBadCount F C δ uWitness) :
    FamilyBounded F C δ R B
      ∧ ¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
          (F := F) (A := A) C δ B :=
  familyBounded_and_counterStack_not_worstCaseIncidenceBounded
    C δ (hfloorBudget hgood) hgt

end ArkLib.ProximityGap.Frontier.FloorClosureContract

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.not_familyBounded_iff_exists_member_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.familyDominates_of_containsGlobalMax
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.containsGlobalMax_of_familyDominates
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.familyDominates_iff_containsGlobalMax
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.not_familyContainsGlobalMax_iff_each_member_beaten
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.not_familyDominates_iff_each_member_beaten
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.familyDominates_univ
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.worstCaseIncidenceBounded_iff_familyBounded_univ
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.deltaStar_pin_of_exhaustiveFamilyBounded
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.worstCaseIncidenceBounded_of_containsGlobalMax
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.deltaStar_pin_of_containsGlobalMax
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.not_worstCaseIncidenceBounded_iff_exists_stack_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.candidateListExactSmallestFamily_of_base_and_successor
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.candidateListExactSmallestFamily_of_prefix_and_successor
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.not_candidateListExactSmallestFamily_iff_exists_rung_not_exact
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.not_candidateListExactSuccessor_iff_exists_exact_rung_next_fails
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.not_candidateListExactSmallestFamily_of_next_failure
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.not_floorGoodFamilyBudget_iff_floorGood_and_not_familyBounded
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.not_floorGoodFamilyBudget_iff_floorGood_and_exists_member_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.floorClosureAtField_of_floorGoodFamilyBudget
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.worstCaseIncidenceBounded_of_floorClosureAtField
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.deltaStar_pin_of_floorClosureAtField
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.floorClosureAtField_iff_floorGood_familyBounded_containsGlobalMax
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.floorClosureAtField_of_floorGood_familyBounded_containsGlobalMax
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.not_floorClosureAtField_iff_bad_or_member_budget_lt_or_not_containsGlobalMax
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.not_floorClosureAtField_iff_bad_or_member_budget_lt_or_each_member_beaten
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.familyBounded_of_linnik_floorGood
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.floorLocalizationUniform_of_candidateListExactSmallestFamily
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.familyBounded_of_linnik_candidateListExactSmallest
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.worstCaseIncidenceBounded_of_linnik_floorClosureContract
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.worstCaseIncidenceBounded_of_linnik_candidateListExactSmallestContract
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.deltaStar_pin_of_linnik_floorClosureContract
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.deltaStar_pin_of_linnik_candidateListExactSmallestContract
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.worstCaseIncidenceBounded_of_linnik_candidateListExactSmallestMaxContract
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.deltaStar_pin_of_linnik_candidateListExactSmallestMaxContract
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.familyBounded_of_tz_floorGood
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.familyBounded_of_tz_candidateListExactSmallest
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.worstCaseIncidenceBounded_of_tz_floorClosureContract
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.worstCaseIncidenceBounded_of_tz_candidateListExactSmallestContract
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.deltaStar_pin_of_tz_candidateListExactSmallestContract
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.worstCaseIncidenceBounded_of_tz_candidateListExactSmallestMaxContract
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.deltaStar_pin_of_tz_candidateListExactSmallestMaxContract
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.floorGood_familyBudget_not_dominationProof_of_larger_than_all
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.not_familyDominates_of_each_member_beaten
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.floorGood_familyBudget_not_dominationProof_of_each_member_beaten
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.floorGood_familyBudget_not_worstCaseIncidenceBounded_of_counterStack
