/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAListBracketInterpolation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleOperationalCountConnector

/-!
# Injective bad-label families and the MCA upper ledger

This file isolates the finite-set plumbing shared by the prize-scale
rate-quarter constructions.  An injective map from a finite certificate index
to field labels, together with one `mcaEvent` proof per index, produces:

* the literal image finset of bad labels;
* its exact cardinality;
* a bad-event proof for every image member;
* the corresponding `mcaDeltaStar` upper bound through
  `mcaDeltaStar_le_of_badStack`.

The generic connector is independent of the concrete construction.  The P1
specialization records the arithmetic price of any `N+2`-element family and a
convenient index shape

`SafeCoord ⊕ (HoleKind × Fin 3)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset
open _root_.ProximityGap Code
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterBadLabelFamilyConnector

attribute [local instance] Classical.propDecidable

/-! ## Generic finite-index connector -/

variable {coordinate scalar alphabet certificate : Type}
variable [Fintype coordinate] [Nonempty coordinate] [DecidableEq coordinate]
variable [Field scalar] [Fintype scalar] [DecidableEq scalar]
variable [Fintype alphabet] [DecidableEq alphabet] [AddCommGroup alphabet]
variable [Module scalar alphabet]
variable [Fintype certificate]

/-- The literal finite image of a label family. -/
def badLabelImage (label : certificate → scalar) : Finset scalar :=
  Finset.univ.image label

/-- Injectivity makes the image cardinality exactly the certificate-index
cardinality. -/
theorem badLabelImage_card
    (label : certificate → scalar) (hinjective : Function.Injective label) :
    (badLabelImage label).card = Fintype.card certificate := by
  rw [badLabelImage, Finset.card_image_of_injective _ hinjective,
    Finset.card_univ]

/-- Pointwise certificate events descend to every member of the image
finset. -/
theorem badLabelImage_mcaEvent
    (C : Set (coordinate → alphabet)) (deltaBad : ℝ≥0)
    (stack : WordStack alphabet (Fin 2) coordinate)
    (label : certificate → scalar)
    (hevent : ∀ index, mcaEvent (F := scalar) C deltaBad
      (stack 0) (stack 1) (label index))
    {gamma : scalar} (hgamma : gamma ∈ badLabelImage label) :
    mcaEvent (F := scalar) C deltaBad (stack 0) (stack 1) gamma := by
  obtain ⟨index, -, rfl⟩ := Finset.mem_image.mp hgamma
  exact hevent index

/-- The image embeds in the literal bad-event filter. -/
theorem certificate_card_le_badEvent_filter_card
    (C : Set (coordinate → alphabet)) (deltaBad : ℝ≥0)
    (stack : WordStack alphabet (Fin 2) coordinate)
    (label : certificate → scalar)
    (hinjective : Function.Injective label)
    (hevent : ∀ index, mcaEvent (F := scalar) C deltaBad
      (stack 0) (stack 1) (label index)) :
    Fintype.card certificate ≤
      (Finset.univ.filter fun gamma : scalar =>
        mcaEvent (F := scalar) C deltaBad (stack 0) (stack 1) gamma).card := by
  classical
  rw [← badLabelImage_card label hinjective]
  apply Finset.card_le_card
  intro gamma hgamma
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact badLabelImage_mcaEvent C deltaBad stack label hevent hgamma

/-- **Injective bad labels feed the operational upper ledger.**  This is the
reusable handoff to `mcaDeltaStar_le_of_badStack`; consumers need only prove
label injectivity, pointwise events, and the normalized price inequality. -/
theorem mcaDeltaStar_le_of_injective_badLabels
    (C : Set (coordinate → alphabet)) (deltaBad : ℝ≥0)
    (stack : WordStack alphabet (Fin 2) coordinate)
    (label : certificate → scalar)
    (hinjective : Function.Injective label)
    (hevent : ∀ index, mcaEvent (F := scalar) C deltaBad
      (stack 0) (stack 1) (label index))
    (epsilonStar : ℝ≥0∞)
    (hprice : epsilonStar <
      (Fintype.card certificate : ℝ≥0∞) /
        (Fintype.card scalar : ℝ≥0∞)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := scalar) (A := alphabet) C epsilonStar ≤ deltaBad := by
  apply ProximityGap.MCAListBracketInterpolation.mcaDeltaStar_le_of_badStack
    C stack (badLabelImage label)
  · intro gamma hgamma
    exact badLabelImage_mcaEvent C deltaBad stack label hevent hgamma
  · rw [badLabelImage_card label hinjective]
    exact hprice

/-! ## The safe-plus-three-per-hole index shape -/

/-- A reusable index for safe coordinates and three affine labels per hole
kind. -/
abbrev ThreePerHoleIndex (SafeCoord HoleKind : Type) :=
  SafeCoord ⊕ (HoleKind × Fin 3)

theorem card_threePerHoleIndex
    (SafeCoord HoleKind : Type) [Fintype SafeCoord] [Fintype HoleKind] :
    Fintype.card (ThreePerHoleIndex SafeCoord HoleKind) =
      Fintype.card SafeCoord + Fintype.card HoleKind * 3 := by
  simp [ThreePerHoleIndex, Fintype.card_sum, Fintype.card_prod]

/-- `N-1` safe coordinates and one hole kind carrying three labels give
exactly `N+2` certificate indices. -/
theorem card_threePerHoleIndex_eq_N_add_two
    {SafeCoord HoleKind : Type} [Fintype SafeCoord] [Fintype HoleKind]
    {domainSize : ℕ} (hpositive : 1 ≤ domainSize)
    (hsafe : Fintype.card SafeCoord = domainSize - 1)
    (hhole : Fintype.card HoleKind = 1) :
    Fintype.card (ThreePerHoleIndex SafeCoord HoleKind) = domainSize + 2 := by
  rw [card_threePerHoleIndex, hsafe, hhole]
  omega

/-! ## Concrete P1 price and wrappers -/

namespace P1

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- The normalized mass of `N+2` labels is strictly larger than the prize
error `2^-128`. -/
theorem prizeEpsilon_lt_N_add_two_div_P :
    ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) <
      ((N + 2 : ℕ) : ℝ≥0∞) / (P : ℝ≥0∞) :=
  P1RateQuarterScaleOperationalCountConnector.prizeEpsilon_lt_N_add_two_div_P

variable {I certificateP1 : Type}
variable [Fintype I] [Nonempty I] [DecidableEq I]
variable [Fintype certificateP1]

/-- Any injectively labelled `N+2`-element P1 certificate family caps the MCA
threshold at its certified bad radius. -/
theorem mcaDeltaStar_le_of_N_add_two_badLabels
    (C : Set (I → F)) (deltaBad : ℝ≥0)
    (stack : WordStack F (Fin 2) I)
    (label : certificateP1 → F)
    (hcard : Fintype.card certificateP1 = N + 2)
    (hinjective : Function.Injective label)
    (hevent : ∀ index,
      mcaEvent C deltaBad (stack 0) (stack 1) (label index)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) C
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤ deltaBad := by
  apply mcaDeltaStar_le_of_injective_badLabels C deltaBad stack label
    hinjective hevent
  rw [hcard, ZMod.card]
  exact prizeEpsilon_lt_N_add_two_div_P

/-- Specialized wrapper for `N-1` safe indices and three labels attached to
one hole kind. -/
theorem mcaDeltaStar_le_of_threePerHole_badLabels
    {SafeCoord HoleKind : Type} [Fintype SafeCoord] [Fintype HoleKind]
    (C : Set (I → F)) (deltaBad : ℝ≥0)
    (stack : WordStack F (Fin 2) I)
    (label : ThreePerHoleIndex SafeCoord HoleKind → F)
    (hsafe : Fintype.card SafeCoord = N - 1)
    (hhole : Fintype.card HoleKind = 1)
    (hinjective : Function.Injective label)
    (hevent : ∀ index,
      mcaEvent C deltaBad (stack 0) (stack 1) (label index)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) C
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤ deltaBad := by
  apply mcaDeltaStar_le_of_N_add_two_badLabels C deltaBad stack label
  · exact card_threePerHoleIndex_eq_N_add_two (by norm_num [N]) hsafe hhole
  · exact hinjective
  · exact hevent

end P1

end ArkLib.ProximityGap.Frontier.P1RateQuarterBadLabelFamilyConnector

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterBadLabelFamilyConnector
#print axioms badLabelImage_card
#print axioms badLabelImage_mcaEvent
#print axioms certificate_card_le_badEvent_filter_card
#print axioms mcaDeltaStar_le_of_injective_badLabels
#print axioms card_threePerHoleIndex_eq_N_add_two
#print axioms P1.prizeEpsilon_lt_N_add_two_div_P
#print axioms P1.mcaDeltaStar_le_of_N_add_two_badLabels
#print axioms P1.mcaDeltaStar_le_of_threePerHole_badLabels
