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

/-- A finite floor family dominates if every stack is no worse than some family member. -/
def FamilyDominates (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    ∃ r ∈ R, StackBadCount K C δ u ≤ StackBadCount K C δ r

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
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.familyBounded_of_linnik_floorGood
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.worstCaseIncidenceBounded_of_linnik_floorClosureContract
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.deltaStar_pin_of_linnik_floorClosureContract
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.familyBounded_of_tz_floorGood
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.worstCaseIncidenceBounded_of_tz_floorClosureContract
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.floorGood_familyBudget_not_dominationProof_of_larger_than_all
#print axioms ArkLib.ProximityGap.Frontier.FloorClosureContract.floorGood_familyBudget_not_worstCaseIncidenceBounded_of_counterStack
