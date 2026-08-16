/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorClosureContract
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ProfileFiberSlackDominance

/-!
# Slack-profile certificates feed the floor closure contract

`_ProfileFiberSlackDominance` records an approximate profile route: every stack is bounded by a
profile representative plus a profile-indexed slack, and every used representative-plus-slack
allowance is within the target budget.

`_FloorClosureContract` records the honest floor-localization contract.  A least-prime/TZ theorem
can only make the modeled floor predicate good at the deployed field; it still has to budget the
chosen representatives and a separate domination theorem has to cover every stack.

This file composes those APIs for the slack route.  The missing floor-to-count theorem can now be
stated directly as:

```text
floor-good at |F| -> every used profile representative plus slack is within B.
```

Together with slack domination, that is enough for `WorstCaseIncidenceBounded` and the usual
delta-star pin.  The refutation surface is explicit: floor still bad, a stack exceeds its
representative-plus-slack allowance, or a used profile's allowance is above budget.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.FloorLocalization
open ArkLib.ProximityGap.Frontier.FloorLinnikTZClosure

namespace ArkLib.ProximityGap.Frontier.ProfileFiberSlackFloorBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The missing floor-to-slack-budget bridge.  Once the deployed field is good for the modeled
floor predicate, the selected profile representatives plus their slack allowances must be within
the MCA bad-scalar budget. -/
def FloorGoodProfileSlackBudget (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) (B : ℕ) : Prop :=
  ¬ FloorBad (2 ^ a) (Fintype.card F) ->
    ProfileFiberSlackDominance.ProfileFiberSlackBudgeted F C δ profile rep slack B

/-- Failure of the floor-good-to-slack-budget theorem means floor-goodness holds at the field size
but the profile slack budget is false. -/
theorem not_floorGoodProfileSlackBudget_iff_floorGood_and_not_profileSlackBudgeted
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) (B : ℕ) :
    (¬ FloorGoodProfileSlackBudget (F := F) (A := A)
        FloorBad a C δ profile rep slack B) ↔
      ¬ FloorBad (2 ^ a) (Fintype.card F) ∧
        ¬ ProfileFiberSlackDominance.ProfileFiberSlackBudgeted
          F C δ profile rep slack B := by
  constructor
  · intro hnot
    by_cases hgood : ¬ FloorBad (2 ^ a) (Fintype.card F)
    · refine ⟨hgood, ?_⟩
      intro hbudget
      exact hnot (fun _ => hbudget)
    · exfalso
      apply hnot
      intro hgood'
      exact False.elim (hgood hgood')
  · rintro ⟨hgood, hnotBudget⟩ hfloorBudget
    exact hnotBudget (hfloorBudget hgood)

/-- Scanner form: the floor-good-to-slack-budget theorem fails exactly when the field is floor-good
and some used profile has representative-plus-slack above budget. -/
theorem not_floorGoodProfileSlackBudget_iff_floorGood_and_exists_usedProfile_budget_lt
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) (B : ℕ) :
    (¬ FloorGoodProfileSlackBudget (F := F) (A := A)
        FloorBad a C δ profile rep slack B) ↔
      ¬ FloorBad (2 ^ a) (Fintype.card F) ∧
        ∃ p : P, ProfileFiberSlackDominance.UsedProfile profile p ∧
          B < ProfileFiberSlackDominance.StackBadCount F C δ (rep p) + slack p := by
  constructor
  · intro hnot
    rcases (not_floorGoodProfileSlackBudget_iff_floorGood_and_not_profileSlackBudgeted
      (F := F) (A := A) FloorBad a C δ profile rep slack B).mp hnot with
      ⟨hgood, hnotBudget⟩
    exact ⟨hgood,
      (ProfileFiberSlackDominance.not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
        C δ profile rep slack B).mp hnotBudget⟩
  · rintro ⟨hgood, hbad⟩
    exact (not_floorGoodProfileSlackBudget_iff_floorGood_and_not_profileSlackBudgeted
      (F := F) (A := A) FloorBad a C δ profile rep slack B).mpr
      ⟨hgood,
        (ProfileFiberSlackDominance.not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
          C δ profile rep slack B).mpr hbad⟩

/-- Field-level slack closure certificate: the floor predicate is good at the deployed field,
profile representatives plus slack are budgeted, and slack domination covers every stack. -/
def ProfileSlackClosureAtField (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) (B : ℕ) : Prop :=
  ¬ FloorBad (2 ^ a) (Fintype.card F) ∧
    ProfileFiberSlackDominance.ProfileFiberSlackDominates F C δ profile rep slack ∧
      ProfileFiberSlackDominance.ProfileFiberSlackBudgeted F C δ profile rep slack B

/-- Floor-goodness plus the floor-to-slack-budget bridge and slack domination give the concrete
field-level closure certificate. -/
theorem profileSlackClosureAtField_of_floorGoodProfileSlackBudget
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hgood : ¬ FloorBad (2 ^ a) (Fintype.card F))
    (hfloorBudget : FloorGoodProfileSlackBudget (F := F) (A := A)
      FloorBad a C δ profile rep slack B)
    (hdom : ProfileFiberSlackDominance.ProfileFiberSlackDominates F C δ profile rep slack) :
    ProfileSlackClosureAtField (F := F) (A := A)
      FloorBad a C δ profile rep slack B :=
  ⟨hgood, hdom, hfloorBudget hgood⟩

/-- A field-level slack closure certificate gives the actual universal incidence hypothesis. -/
theorem worstCaseIncidenceBounded_of_profileSlackClosureAtField
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hcert : ProfileSlackClosureAtField (F := F) (A := A)
      FloorBad a C δ profile rep slack B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  ProfileFiberSlackDominance.worstCaseIncidenceBounded_of_profileFiberSlack
    C δ hcert.2.1 hcert.2.2

/-- Delta-star consumer for a field-level slack closure certificate. -/
theorem deltaStar_pin_of_profileSlackClosureAtField
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hcert : ProfileSlackClosureAtField (F := F) (A := A)
      FloorBad a C δ profile rep slack B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProfileFiberSlackDominance.deltaStar_pin_of_profileFiberSlack
    C εstar hδ hcert.2.1 hcert.2.2 hbudget

/-- A field-level slack closure certificate bounds the realized bad-count image by `[0, B]`. -/
theorem stackBadCountImage_card_le_budget_add_one_of_profileSlackClosureAtField
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hcert : ProfileSlackClosureAtField (F := F) (A := A)
      FloorBad a C δ profile rep slack B) :
    (ProfileFiberSlackDominance.StackBadCountImage F C δ).card ≤ B + 1 := by
  have hsubset :
      ProfileFiberSlackDominance.StackBadCountImage F C δ ⊆ Finset.Icc 0 B := by
    intro b hb
    change b ∈ (Finset.univ : Finset (WordStack A (Fin 2) ι)).image
      (fun u => ProfileFiberSlackDominance.StackBadCount F C δ u) at hb
    rcases Finset.mem_image.mp hb with ⟨u, _hu, hu⟩
    rw [← hu]
    exact Finset.mem_Icc.mpr
      ⟨Nat.zero_le _,
        le_trans (hcert.2.1 u) (hcert.2.2 (profile u) ⟨u, rfl⟩)⟩
  calc
    (ProfileFiberSlackDominance.StackBadCountImage F C δ).card ≤ (Finset.Icc 0 B).card :=
      Finset.card_le_card hsubset
    _ = B + 1 := by
      rw [Nat.card_Icc]
      omega

/-- Image-size refuter for field-level slack closure: no closure certificate with budget `B` can
explain more than `B + 1` distinct realized bad-count values. -/
theorem not_profileSlackClosureAtField_of_budget_add_one_lt_stackBadCountImage
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hsmall : B + 1 <
      (ProfileFiberSlackDominance.StackBadCountImage F C δ).card) :
    ¬ ProfileSlackClosureAtField (F := F) (A := A)
      FloorBad a C δ profile rep slack B := by
  intro hcert
  exact (not_lt_of_ge
    (stackBadCountImage_card_le_budget_add_one_of_profileSlackClosureAtField
      FloorBad a C δ hcert)) hsmall

/-- Exact scanner form for the field-level slack closure certificate.  It fails precisely when the
floor predicate is still bad, a stack exceeds its representative-plus-slack allowance, or a used
profile's allowance exceeds budget. -/
theorem not_profileSlackClosureAtField_iff_bad_or_stack_exceeds_slack_or_usedProfile_budget_lt
    (FloorBad : ℕ -> ℕ -> Prop) (a : ℕ)
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {P : Type} (profile : WordStack A (Fin 2) ι -> P)
    (rep : P -> WordStack A (Fin 2) ι) (slack : P -> ℕ) (B : ℕ) :
    (¬ ProfileSlackClosureAtField (F := F) (A := A)
        FloorBad a C δ profile rep slack B) ↔
      FloorBad (2 ^ a) (Fintype.card F) ∨
        (∃ u : WordStack A (Fin 2) ι,
          ProfileFiberSlackDominance.StackBadCount F C δ (rep (profile u)) +
              slack (profile u) <
            ProfileFiberSlackDominance.StackBadCount F C δ u) ∨
          ∃ p : P, ProfileFiberSlackDominance.UsedProfile profile p ∧
            B < ProfileFiberSlackDominance.StackBadCount F C δ (rep p) + slack p := by
  classical
  unfold ProfileSlackClosureAtField
  constructor
  · intro hnot
    by_cases hbad : FloorBad (2 ^ a) (Fintype.card F)
    · exact Or.inl hbad
    · have hnotPair :
          ¬ (ProfileFiberSlackDominance.ProfileFiberSlackDominates F C δ profile rep slack ∧
            ProfileFiberSlackDominance.ProfileFiberSlackBudgeted F C δ profile rep slack B) := by
        intro hpair
        exact hnot ⟨hbad, hpair⟩
      rw [not_and_or] at hnotPair
      rcases hnotPair with hnotDom | hnotBudget
      · exact Or.inr <| Or.inl
          ((ProfileFiberSlackDominance.not_profileFiberSlackDominates_iff_exists_stack_exceeds_slack
            C δ profile rep slack).mp hnotDom)
      · exact Or.inr <| Or.inr
          ((ProfileFiberSlackDominance.not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
            C δ profile rep slack B).mp hnotBudget)
  · rintro (hbad | hdomOrBudget) hcert
    · exact hcert.1 hbad
    · rcases hdomOrBudget with hstack | hbudget
      · exact ((ProfileFiberSlackDominance.not_profileFiberSlackDominates_iff_exists_stack_exceeds_slack
          C δ profile rep slack).mpr hstack) hcert.2.1
      · exact ((ProfileFiberSlackDominance.not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
          C δ profile rep slack B).mpr hbudget) hcert.2.2

/-- Linnik-form localization plus the floor-to-slack-budget bridge gives a profile slack budget. -/
theorem profileFiberSlackBudgeted_of_linnik_floorGood
    (FloorBad : ℕ -> ℕ -> Prop)
    (hUnif : FloorLocalizationUniform FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hfloorBudget : FloorGoodProfileSlackBudget (F := F) (A := A)
      FloorBad a C δ profile rep slack B) :
    ProfileFiberSlackDominance.ProfileFiberSlackBudgeted F C δ profile rep slack B := by
  have hgood : ¬ FloorBad (2 ^ a) (Fintype.card F) :=
    floor_closes_by_linnik FloorBad hUnif hLeast
      a ha (Fintype.card F) hcardPrime hcardMod hcardPrize
  exact hfloorBudget hgood

/-- Scanner-facing Linnik form with exact singleton floor-bad lists. -/
theorem profileFiberSlackBudgeted_of_linnik_candidateListExactSmallest
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hfloorBudget : FloorGoodProfileSlackBudget (F := F) (A := A)
      FloorBad a C δ profile rep slack B) :
    ProfileFiberSlackDominance.ProfileFiberSlackBudgeted F C δ profile rep slack B :=
  profileFiberSlackBudgeted_of_linnik_floorGood
    (F := F) (A := A) FloorBad
    (FloorClosureContract.floorLocalizationUniform_of_candidateListExactSmallestFamily
      FloorBad hexact)
    hLeast a ha hcardPrime hcardMod hcardPrize C δ hfloorBudget

/-- Linnik-form full contract: floor localization supplies the slack budget, but a separate slack
domination theorem is still required before one obtains the actual universal incidence bound. -/
theorem worstCaseIncidenceBounded_of_linnik_profileSlackContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hUnif : FloorLocalizationUniform FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hfloorBudget : FloorGoodProfileSlackBudget (F := F) (A := A)
      FloorBad a C δ profile rep slack B)
    (hdom : ProfileFiberSlackDominance.ProfileFiberSlackDominates F C δ profile rep slack) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  ProfileFiberSlackDominance.worstCaseIncidenceBounded_of_profileFiberSlack C δ hdom
    (profileFiberSlackBudgeted_of_linnik_floorGood
      (F := F) (A := A) FloorBad hUnif hLeast a ha
      hcardPrime hcardMod hcardPrize C δ hfloorBudget)

/-- Scanner-facing Linnik full contract with exact singleton floor-bad lists. -/
theorem worstCaseIncidenceBounded_of_linnik_candidateListExactSmallest_profileSlackContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hfloorBudget : FloorGoodProfileSlackBudget (F := F) (A := A)
      FloorBad a C δ profile rep slack B)
    (hdom : ProfileFiberSlackDominance.ProfileFiberSlackDominates F C δ profile rep slack) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_linnik_profileSlackContract
    (F := F) (A := A) FloorBad
    (FloorClosureContract.floorLocalizationUniform_of_candidateListExactSmallestFamily
      FloorBad hexact)
    hLeast a ha hcardPrime hcardMod hcardPrize C δ hfloorBudget hdom

/-- Delta-star consumer for the Linnik slack-profile contract. -/
theorem deltaStar_pin_of_linnik_candidateListExactSmallest_profileSlackContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    (hLeast : LinnikLeastPrimeBelowPrize)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hfloorBudget : FloorGoodProfileSlackBudget (F := F) (A := A)
      FloorBad a C δ profile rep slack B)
    (hdom : ProfileFiberSlackDominance.ProfileFiberSlackDominates F C δ profile rep slack)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProfileFiberSlackDominance.deltaStar_pin_of_profileFiberSlack C εstar hδ hdom
    (profileFiberSlackBudgeted_of_linnik_candidateListExactSmallest
      (F := F) (A := A) FloorBad hexact hLeast a ha
      hcardPrime hcardMod hcardPrize C δ hfloorBudget)
    hbudget

/-- TZ-form localization plus the floor-to-slack-budget bridge gives a profile slack budget. -/
theorem profileFiberSlackBudgeted_of_tz_floorGood
    (FloorBad : ℕ -> ℕ -> Prop)
    (hUnif : FloorLocalizationUniform FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hfloorBudget : FloorGoodProfileSlackBudget (F := F) (A := A)
      FloorBad a C δ profile rep slack B) :
    ProfileFiberSlackDominance.ProfileFiberSlackBudgeted F C δ profile rep slack B := by
  have hgood : ¬ FloorBad (2 ^ a) (Fintype.card F) :=
    floor_closes_by_tzSupplyFamily FloorBad hUnif hβ hTZfam
      a ha (Fintype.card F) hcardPrime hcardMod hcardPrize
  exact hfloorBudget hgood

/-- Scanner-facing TZ form with exact singleton floor-bad lists. -/
theorem profileFiberSlackBudgeted_of_tz_candidateListExactSmallest
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hfloorBudget : FloorGoodProfileSlackBudget (F := F) (A := A)
      FloorBad a C δ profile rep slack B) :
    ProfileFiberSlackDominance.ProfileFiberSlackBudgeted F C δ profile rep slack B :=
  profileFiberSlackBudgeted_of_tz_floorGood
    (F := F) (A := A) FloorBad
    (FloorClosureContract.floorLocalizationUniform_of_candidateListExactSmallestFamily
      FloorBad hexact)
    hβ hTZfam a ha hcardPrime hcardMod hcardPrize C δ hfloorBudget

/-- TZ-form full contract: a uniform TZ supply still needs the same floor-to-slack-budget bridge
and an independent slack domination theorem before it becomes the actual universal incidence bound.
-/
theorem worstCaseIncidenceBounded_of_tz_candidateListExactSmallest_profileSlackContract
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : FloorClosureContract.CandidateListExactSmallestFamily FloorBad)
    {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a -> TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a)
    (hcardPrime : (Fintype.card F).Prime)
    (hcardMod : Fintype.card F % (2 ^ a) = 1)
    (hcardPrize : (2 ^ a) ^ 4 ≤ Fintype.card F)
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hfloorBudget : FloorGoodProfileSlackBudget (F := F) (A := A)
      FloorBad a C δ profile rep slack B)
    (hdom : ProfileFiberSlackDominance.ProfileFiberSlackDominates F C δ profile rep slack) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  ProfileFiberSlackDominance.worstCaseIncidenceBounded_of_profileFiberSlack C δ hdom
    (profileFiberSlackBudgeted_of_tz_candidateListExactSmallest
      (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
      hcardPrime hcardMod hcardPrize C δ hfloorBudget)

/-- Delta-star consumer for the TZ slack-profile contract. -/
theorem deltaStar_pin_of_tz_candidateListExactSmallest_profileSlackContract
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
    {P : Type} {profile : WordStack A (Fin 2) ι -> P}
    {rep : P -> WordStack A (Fin 2) ι} {slack : P -> ℕ}
    (hfloorBudget : FloorGoodProfileSlackBudget (F := F) (A := A)
      FloorBad a C δ profile rep slack B)
    (hdom : ProfileFiberSlackDominance.ProfileFiberSlackDominates F C δ profile rep slack)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProfileFiberSlackDominance.deltaStar_pin_of_profileFiberSlack C εstar hδ hdom
    (profileFiberSlackBudgeted_of_tz_candidateListExactSmallest
      (F := F) (A := A) FloorBad hexact hβ hTZfam a ha
      hcardPrime hcardMod hcardPrize C δ hfloorBudget)
    hbudget

#print axioms FloorGoodProfileSlackBudget
#print axioms not_floorGoodProfileSlackBudget_iff_floorGood_and_not_profileSlackBudgeted
#print axioms not_floorGoodProfileSlackBudget_iff_floorGood_and_exists_usedProfile_budget_lt
#print axioms ProfileSlackClosureAtField
#print axioms profileSlackClosureAtField_of_floorGoodProfileSlackBudget
#print axioms worstCaseIncidenceBounded_of_profileSlackClosureAtField
#print axioms deltaStar_pin_of_profileSlackClosureAtField
#print axioms stackBadCountImage_card_le_budget_add_one_of_profileSlackClosureAtField
#print axioms not_profileSlackClosureAtField_of_budget_add_one_lt_stackBadCountImage
#print axioms not_profileSlackClosureAtField_iff_bad_or_stack_exceeds_slack_or_usedProfile_budget_lt
#print axioms profileFiberSlackBudgeted_of_linnik_candidateListExactSmallest
#print axioms worstCaseIncidenceBounded_of_linnik_candidateListExactSmallest_profileSlackContract
#print axioms deltaStar_pin_of_linnik_candidateListExactSmallest_profileSlackContract
#print axioms profileFiberSlackBudgeted_of_tz_candidateListExactSmallest
#print axioms worstCaseIncidenceBounded_of_tz_candidateListExactSmallest_profileSlackContract
#print axioms deltaStar_pin_of_tz_candidateListExactSmallest_profileSlackContract

end ArkLib.ProximityGap.Frontier.ProfileFiberSlackFloorBridge
