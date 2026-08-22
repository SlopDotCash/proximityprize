/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKSevenSubsetOverlapDecomposition
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ANT46RungTwoAccidentOrbit

/-!
# Production budget for the marked seven-subset overlap decomposition

The exact common-core decomposition of a marked seven-subset collision has no depth-zero or
depth-one term.  This file removes those terms, evaluates every remaining completion coefficient
at the production cardinality `n = 2^30`, and audits the most optimistic positive Wick envelope.

After converting subsets back to ordered injective tuples, the independent depth-`r` Wick cap
would cost

`(7!)^2 (2r-1)!! / ((r!)^2 (7-r)!)`

units of the coefficient-`126871` allowance.  Already `r=2` costs `158760`; the largest single
term is `r=5`, at `833490`, and the five lower depths cost `2714355`, strictly between 21 and 22
times the entire allowance.  This is a no-go for a termwise **positive-count** completion proof.
It is not a lower bound on marked collisions: signed/DC cancellation, or an arithmetic theorem
showing that the marked strata are much smaller than their ambient Wick caps, can still win.

The depth-two stratum is also wired to the existing projective accident classifier.  Orient a
marked disjoint pair `{x₁,x₂}`, `{y₁,y₂}` and divide by `y₂`.  The normalized triple solves
`a+b=c+1`.  Disjointness excludes the first two lawful families, while oddness of the auxiliary
lift makes the antipodal lawful family unmarked.  Hence every such orientation is an accident.
The existing classifier supplies exact orbit/divisibility and difference-signature sockets, but
not accident-freeness; this bridge therefore localizes, rather than assumes away, the remaining
depth-two arithmetic input.  Issue #466.
-/

set_option autoImplicit false

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKSevenOverlapProductionBudget

open BGKSevenSubsetOverlapDecomposition
open ANT46RungTwoAccidentOrbit

/-! ## The two vacuous residual depths -/

section VanishingDepths

variable {α : Type*} [AddCommGroup α] [DecidableEq α]
variable {β : Type*} [AddCommGroup β] [DecidableEq β]

/-- The unique disjoint zero-subset collision has zero signed label, so it is never marked. -/
theorem markedDisjointCollisionPairs_zero_eq_empty
    (G : Finset α) (lift : α → β) :
    markedDisjointCollisionPairs G 0 lift = ∅ := by
  classical
  ext p
  constructor
  · intro hp
    rw [markedDisjointCollisionPairs, Finset.mem_filter,
      disjointCollisionPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_powersetCard, Finset.mem_powersetCard] at hp
    obtain ⟨⟨⟨⟨_hAsub, hAcard⟩, _hBsub, hBcard⟩, _hdisj, _hsum⟩, hmarked⟩ := hp
    have hA : p.1 = ∅ := Finset.card_eq_zero.mp hAcard
    have hB : p.2 = ∅ := Finset.card_eq_zero.mp hBcard
    exact (hmarked (by simp [signedPairLabel, hA, hB])).elim
  · simp

/-- Two disjoint singleton subsets cannot have the same sum. -/
theorem markedDisjointCollisionPairs_one_eq_empty
    (G : Finset α) (lift : α → β) :
    markedDisjointCollisionPairs G 1 lift = ∅ := by
  classical
  ext p
  constructor
  · intro hp
    rw [markedDisjointCollisionPairs, Finset.mem_filter,
      disjointCollisionPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_powersetCard, Finset.mem_powersetCard] at hp
    obtain ⟨⟨⟨⟨_hAsub, hAcard⟩, _hBsub, hBcard⟩, hdisj, hsum⟩, _hmarked⟩ := hp
    obtain ⟨x, hA⟩ := Finset.card_eq_one.mp hAcard
    obtain ⟨y, hB⟩ := Finset.card_eq_one.mp hBcard
    rw [hA, hB] at hdisj hsum
    simp only [Finset.sum_singleton] at hsum
    subst y
    rw [Finset.disjoint_singleton] at hdisj
    exact (hdisj rfl).elim
  · simp

/-- The depth-seven marked identity with the vacuous `r=0,1` terms removed. -/
theorem card_markedSevenCollisionPairs_eq_depths_two_through_seven
    (G : Finset α) (lift : α → β) :
    (markedCollisionPairs G 7 lift).card =
      (markedDisjointCollisionPairs G 2 lift).card *
          (G.card - 4).choose 5 +
      (markedDisjointCollisionPairs G 3 lift).card *
          (G.card - 6).choose 4 +
      (markedDisjointCollisionPairs G 4 lift).card *
          (G.card - 8).choose 3 +
      (markedDisjointCollisionPairs G 5 lift).card *
          (G.card - 10).choose 2 +
      (markedDisjointCollisionPairs G 6 lift).card *
          (G.card - 12) +
      (markedDisjointCollisionPairs G 7 lift).card := by
  rw [card_markedSevenCollisionPairs_eq_overlap_plus_primitive]
  simp [Finset.sum_range_succ, markedDisjointCollisionPairs_zero_eq_empty,
    markedDisjointCollisionPairs_one_eq_empty]

end VanishingDepths

/-! ## Exact production completion ledger -/

/-- The production subgroup cardinality. -/
def productionN : Nat := 2 ^ 30

def completionCoefficientTwo : Nat :=
  11893730440242670391496011184148106360913864

def completionCoefficientThree : Nat :=
  55384498276946461690462545205264510

def completionCoefficientFour : Nat :=
  206323334692749985059962760

def completionCoefficientFive : Nat :=
  576460741029134391

def completionCoefficientSix : Nat :=
  1073741812

theorem production_choose_two :
    (productionN - 4).choose 5 = completionCoefficientTwo := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [productionN, completionCoefficientTwo, Nat.descFactorial, Nat.factorial]

theorem production_choose_three :
    (productionN - 6).choose 4 = completionCoefficientThree := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [productionN, completionCoefficientThree, Nat.descFactorial, Nat.factorial]

theorem production_choose_four :
    (productionN - 8).choose 3 = completionCoefficientFour := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [productionN, completionCoefficientFour, Nat.descFactorial, Nat.factorial]

theorem production_choose_five :
    (productionN - 10).choose 2 = completionCoefficientFive := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [productionN, completionCoefficientFive, Nat.descFactorial, Nat.factorial]

theorem production_choose_six :
    productionN - 12 = completionCoefficientSix := by
  norm_num [productionN, completionCoefficientSix]

section ProductionLedger

variable {α : Type*} [AddCommGroup α] [DecidableEq α]
variable {β : Type*} [AddCommGroup β] [DecidableEq β]

/-- Exact marked seven-subset completion ledger at `|G|=2^30`. -/
theorem production_markedSeven_ledger
    (G : Finset α) (lift : α → β) (hG : G.card = productionN) :
    (markedCollisionPairs G 7 lift).card =
      (markedDisjointCollisionPairs G 2 lift).card * completionCoefficientTwo +
      (markedDisjointCollisionPairs G 3 lift).card * completionCoefficientThree +
      (markedDisjointCollisionPairs G 4 lift).card * completionCoefficientFour +
      (markedDisjointCollisionPairs G 5 lift).card * completionCoefficientFive +
      (markedDisjointCollisionPairs G 6 lift).card * completionCoefficientSix +
      (markedDisjointCollisionPairs G 7 lift).card := by
  rw [card_markedSevenCollisionPairs_eq_depths_two_through_seven, hG,
    production_choose_two, production_choose_three, production_choose_four,
    production_choose_five, production_choose_six]

end ProductionLedger

/-! ## Positive Wick-envelope no-go -/

/-- Ordered-injective coefficient contributed by the optimistic depth-two Wick cap. -/
def wickCompletionTwo : Nat := 158760

/-- Ordered-injective coefficient contributed by the optimistic depth-three Wick cap. -/
def wickCompletionThree : Nat := 441000

/-- Ordered-injective coefficient contributed by the optimistic depth-four Wick cap. -/
def wickCompletionFour : Nat := 771750

/-- Ordered-injective coefficient contributed by the optimistic depth-five Wick cap. -/
def wickCompletionFive : Nat := 833490

/-- Ordered-injective coefficient contributed by the optimistic depth-six Wick cap. -/
def wickCompletionSix : Nat := 509355

/-- Sum of all five lower-depth positive Wick completion coefficients. -/
def lowerDepthWickCompletionTotal : Nat :=
  wickCompletionTwo + wickCompletionThree + wickCompletionFour +
    wickCompletionFive + wickCompletionSix

/-- The coefficient left for the ordered injective depth-seven residual. -/
def injectiveAllowance : Nat := 126871

/-- The five constants really are the factorial/Wick completion constants
`(7!)^2 (2r-1)!! / ((r!)^2 (7-r)!)`. -/
theorem wick_completion_coefficients_exact :
    wickCompletionTwo =
        (Nat.factorial 7) ^ 2 * Nat.doubleFactorial (2 * 2 - 1) /
          ((Nat.factorial 2) ^ 2 * Nat.factorial (7 - 2)) ∧
    wickCompletionThree =
        (Nat.factorial 7) ^ 2 * Nat.doubleFactorial (2 * 3 - 1) /
          ((Nat.factorial 3) ^ 2 * Nat.factorial (7 - 3)) ∧
    wickCompletionFour =
        (Nat.factorial 7) ^ 2 * Nat.doubleFactorial (2 * 4 - 1) /
          ((Nat.factorial 4) ^ 2 * Nat.factorial (7 - 4)) ∧
    wickCompletionFive =
        (Nat.factorial 7) ^ 2 * Nat.doubleFactorial (2 * 5 - 1) /
          ((Nat.factorial 5) ^ 2 * Nat.factorial (7 - 5)) ∧
    wickCompletionSix =
        (Nat.factorial 7) ^ 2 * Nat.doubleFactorial (2 * 6 - 1) /
          ((Nat.factorial 6) ^ 2 * Nat.factorial (7 - 6)) := by
  norm_num [wickCompletionTwo, wickCompletionThree, wickCompletionFour,
    wickCompletionFive, wickCompletionSix, Nat.factorial, Nat.doubleFactorial]

/-- The very first nonvacuous depth already consumes more than the whole allowance. -/
theorem depth_two_already_exceeds_allowance :
    injectiveAllowance < wickCompletionTwo := by
  norm_num [injectiveAllowance, wickCompletionTwo]

/-- Depth five is the dominant single positive completion term. -/
theorem depth_five_is_dominant :
    wickCompletionTwo ≤ wickCompletionFive ∧
    wickCompletionThree ≤ wickCompletionFive ∧
    wickCompletionFour ≤ wickCompletionFive ∧
    wickCompletionSix ≤ wickCompletionFive := by
  norm_num [wickCompletionTwo, wickCompletionThree, wickCompletionFour,
    wickCompletionFive, wickCompletionSix]

/-- The exact total lower-depth coefficient is `2714355`. -/
theorem lowerDepthWickCompletionTotal_eq :
    lowerDepthWickCompletionTotal = 2714355 := by
  norm_num [lowerDepthWickCompletionTotal, wickCompletionTwo, wickCompletionThree,
    wickCompletionFour, wickCompletionFive, wickCompletionSix]

/-- Even perfect annihilation of the marked depth-two accident sector does not
produce the one-unit Wick-trajectory improvement by positive bookkeeping.  The
remaining depth-three through depth-six completion coefficients total
`2555595`, still more than twenty full injective allowances.  Connecting
accident-freeness to the trajectory target therefore requires signed
covariance cancellation, not deletion of the positive depth-two term alone. -/
theorem positive_completion_without_depthTwo_still_exceeds_twenty_allowances :
    lowerDepthWickCompletionTotal - wickCompletionTwo = 2555595 ∧
      20 * injectiveAllowance <
        lowerDepthWickCompletionTotal - wickCompletionTwo := by
  constructor <;>
    norm_num [lowerDepthWickCompletionTotal, wickCompletionTwo,
      wickCompletionThree, wickCompletionFour, wickCompletionFive,
      wickCompletionSix, injectiveAllowance]

/-- The positive lower-depth Wick completion envelope costs strictly between 21 and 22 complete
copies of the coefficient-`126871` allowance. -/
theorem positive_wick_completion_between_twentyOne_and_twentyTwo_allowances :
    21 * injectiveAllowance < lowerDepthWickCompletionTotal ∧
      lowerDepthWickCompletionTotal < 22 * injectiveAllowance := by
  norm_num [injectiveAllowance, lowerDepthWickCompletionTotal, wickCompletionTwo,
    wickCompletionThree, wickCompletionFour, wickCompletionFive, wickCompletionSix]

/-! ## Depth two normalizes to the existing projective accident socket -/

section AccidentBridge

variable {F : Type*} [Field F] [DecidableEq F]
variable {β : Type*} [AddCommGroup β] [DecidableEq β]

/-- An oriented marked disjoint two-pair normalizes to an `ANT46` accident.  This elementwise
version isolates the only marker property used at the third lawful family. -/
theorem oriented_marked_depthTwo_normalizes_to_accident
    (H : Finset F)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (hinv : ∀ x ∈ H, x⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H)
    (lift : F → β)
    {x₁ x₂ y₁ y₂ : F}
    (hx₁ : x₁ ∈ H) (hx₂ : x₂ ∈ H) (hy₁ : y₁ ∈ H) (hy₂ : y₂ ∈ H)
    (hsum : x₁ + x₂ = y₁ + y₂)
    (hx₁y₂ : x₁ ≠ y₂) (hx₂y₂ : x₂ ≠ y₂)
    (hmark : lift x₁ + lift x₂ - (lift y₁ + lift y₂) ≠ 0)
    (hantipodal : x₂ = -x₁ → y₁ = -y₂ →
      lift x₁ + lift x₂ - (lift y₁ + lift y₂) = 0) :
    Triple.mk (x₁ / y₂) (x₂ / y₂) (y₁ / y₂) ∈ accidents H := by
  have hy₂0 : y₂ ≠ 0 := fun hy₂zero => h0 (hy₂zero ▸ hy₂)
  rw [mem_accidents_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [div_eq_mul_inv] using hmul x₁ hx₁ y₂⁻¹ (hinv y₂ hy₂)
  · simpa [div_eq_mul_inv] using hmul x₂ hx₂ y₂⁻¹ (hinv y₂ hy₂)
  · simpa [div_eq_mul_inv] using hmul y₁ hy₁ y₂⁻¹ (hinv y₂ hy₂)
  · refine ⟨?_, ?_⟩
    · change x₁ / y₂ + x₂ / y₂ = y₁ / y₂ + 1
      field_simp [hy₂0]
      exact hsum
    · intro hlaw
      rcases hlaw with ha | hb | hc
      · exact hx₁y₂ ((div_eq_one_iff_eq hy₂0).mp ha)
      · exact hx₂y₂ ((div_eq_one_iff_eq hy₂0).mp hb)
      · rcases hc with ⟨hc, hbneg⟩
        have hyanti : y₁ = -y₂ := by
          apply (div_left_inj' hy₂0).mp
          simpa [hy₂0] using hc
        have hxanti : x₂ = -x₁ := by
          apply (div_left_inj' hy₂0).mp
          simpa only [neg_div] using hbneg
        exact hmark (hantipodal hxanti hyanti)

/-- Direct bridge from membership in the marked disjoint depth-two Finset.  Oddness of the lift
annihilates the antipodal lawful family. -/
theorem marked_depthTwo_pair_normalizes_to_accident
    (H : Finset F)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (hinv : ∀ x ∈ H, x⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H)
    (lift : F → β)
    (hliftNeg : ∀ x ∈ H, lift (-x) = -lift x)
    {x₁ x₂ y₁ y₂ : F}
    (hp : (⟨{x₁, x₂}, {y₁, y₂}⟩ : Finset F × Finset F) ∈
      markedDisjointCollisionPairs H 2 lift) :
    Triple.mk (x₁ / y₂) (x₂ / y₂) (y₁ / y₂) ∈ accidents H := by
  rw [markedDisjointCollisionPairs, Finset.mem_filter,
    disjointCollisionPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_powersetCard, Finset.mem_powersetCard] at hp
  obtain ⟨⟨⟨⟨hXsub, hXcard⟩, hYsub, hYcard⟩, hdisj, hsum⟩, hmark⟩ := hp
  have hx₁ : x₁ ∈ H := hXsub (by simp)
  have hx₂ : x₂ ∈ H := hXsub (by simp)
  have hy₁ : y₁ ∈ H := hYsub (by simp)
  have hy₂ : y₂ ∈ H := hYsub (by simp)
  have hxne : x₁ ≠ x₂ := by
    intro heq
    subst x₂
    simp at hXcard
  have hyne : y₁ ≠ y₂ := by
    intro heq
    subst y₂
    simp at hYcard
  have hx₁y₂ : x₁ ≠ y₂ := by
    intro heq
    have hxleft : x₁ ∈ ({x₁, x₂} : Finset F) := by simp
    have hxright : x₁ ∈ ({y₁, y₂} : Finset F) := by simp [heq]
    exact (Finset.disjoint_left.mp hdisj) hxleft hxright
  have hx₂y₂ : x₂ ≠ y₂ := by
    intro heq
    have hxleft : x₂ ∈ ({x₁, x₂} : Finset F) := by simp
    have hxright : x₂ ∈ ({y₁, y₂} : Finset F) := by simp [heq]
    exact (Finset.disjoint_left.mp hdisj) hxleft hxright
  apply oriented_marked_depthTwo_normalizes_to_accident H hmul hinv h0 lift
      hx₁ hx₂ hy₁ hy₂
  · simpa [Finset.sum_pair hxne, Finset.sum_pair hyne] using hsum
  · exact hx₁y₂
  · exact hx₂y₂
  · simpa [signedPairLabel, Finset.sum_pair hxne,
      Finset.sum_pair hyne] using hmark
  · intro hxanti hyanti
    rw [hxanti, hyanti, hliftNeg x₁ hx₁, hliftNeg y₂ hy₂]
    abel

/-- Accident-freeness annihilates the entire marked disjoint depth-two stratum.  The proof
extracts both two-element subsets, chooses either ordering, and feeds that orientation to
`marked_depthTwo_pair_normalizes_to_accident`; no cardinality or orbit-size converse is assumed. -/
theorem markedDisjointCollisionPairs_two_eq_empty_of_accidents_eq_empty
    (H : Finset F)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (hinv : ∀ x ∈ H, x⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H)
    (lift : F → β)
    (hliftNeg : ∀ x ∈ H, lift (-x) = -lift x)
    (hempty : accidents H = ∅) :
    markedDisjointCollisionPairs H 2 lift = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨A, B⟩ hp
  have hp' := hp
  rw [markedDisjointCollisionPairs, Finset.mem_filter,
    disjointCollisionPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_powersetCard, Finset.mem_powersetCard] at hp'
  obtain ⟨⟨⟨⟨_hAsub, hAcard⟩, _hBsub, hBcard⟩, _hdisj, _hsum⟩, _hmark⟩ := hp'
  obtain ⟨x₁, x₂, _hxne, hA⟩ := Finset.card_eq_two.mp hAcard
  obtain ⟨y₁, y₂, _hyne, hB⟩ := Finset.card_eq_two.mp hBcard
  have hpPair : (⟨{x₁, x₂}, {y₁, y₂}⟩ : Finset F × Finset F) ∈
      markedDisjointCollisionPairs H 2 lift := by
    have hpEq : (A, B) = (⟨{x₁, x₂}, {y₁, y₂}⟩ : Finset F × Finset F) :=
      Prod.ext hA hB
    rw [hpEq] at hp
    exact hp
  have hacc := marked_depthTwo_pair_normalizes_to_accident
    H hmul hinv h0 lift hliftNeg hpPair
  simpa [hempty] using hacc

/-- Exact `κ(x)=(x-1)^n` consumer: injectivity of the difference signature modulo inversion
forces the marked depth-two stratum to vanish. -/
theorem markedDisjointCollisionPairs_two_eq_empty_of_differenceSignatureInjectiveModInversion
    (H : Finset F) (n : Nat)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (hinv : ∀ x ∈ H, x⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H)
    (hpow : ∀ x ∈ H, x ^ n = 1)
    (lift : F → β)
    (hliftNeg : ∀ x ∈ H, lift (-x) = -lift x)
    (hinjective : DifferenceSignatureInjectiveModInversion H n) :
    markedDisjointCollisionPairs H 2 lift = ∅ := by
  apply markedDisjointCollisionPairs_two_eq_empty_of_accidents_eq_empty
    H hmul hinv h0 lift hliftNeg
  exact accidents_eq_empty_of_differenceSignatureInjectiveModInversion
    hmul hinv h0 hpow hinjective

local instance firstProductionPrimeFact :
    Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

local instance secondProductionPrimeFact :
    Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- First-production-prime depth-two socket.  Its only arithmetic input is the still-explicit
`κ`-injectivity hypothesis. -/
theorem firstPrime_markedDisjointCollisionPairs_two_eq_empty
    {H : Finset (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)}
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (hinv : ∀ x ∈ H, x⁻¹ ∈ H)
    (h0 : (0 : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) ∉ H)
    (hpow : ∀ x ∈ H, x ^ (2 ^ 30 : Nat) = 1)
    (lift : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P → β)
    (hliftNeg : ∀ x ∈ H, lift (-x) = -lift x)
    (hinjective : DifferenceSignatureInjectiveModInversion H (2 ^ 30)) :
    markedDisjointCollisionPairs H 2 lift = ∅ := by
  apply markedDisjointCollisionPairs_two_eq_empty_of_accidents_eq_empty
    H hmul hinv h0 lift hliftNeg
  exact firstPrime_accidents_eq_empty_of_differenceSignatureInjectiveModInversion
    hmul hinv h0 hpow hinjective

/-- Second-production-prime copy of the exact depth-two `κ` socket. -/
theorem secondPrime_markedDisjointCollisionPairs_two_eq_empty
    {H : Finset (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)}
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (hinv : ∀ x ∈ H, x⁻¹ ∈ H)
    (h0 : (0 : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) ∉ H)
    (hpow : ∀ x ∈ H, x ^ (2 ^ 30 : Nat) = 1)
    (lift : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P → β)
    (hliftNeg : ∀ x ∈ H, lift (-x) = -lift x)
    (hinjective : DifferenceSignatureInjectiveModInversion H (2 ^ 30)) :
    markedDisjointCollisionPairs H 2 lift = ∅ := by
  apply markedDisjointCollisionPairs_two_eq_empty_of_accidents_eq_empty
    H hmul hinv h0 lift hliftNeg
  exact secondPrime_accidents_eq_empty_of_differenceSignatureInjectiveModInversion
    hmul hinv h0 hpow hinjective

end AccidentBridge

#print axioms markedDisjointCollisionPairs_zero_eq_empty
#print axioms markedDisjointCollisionPairs_one_eq_empty
#print axioms production_markedSeven_ledger
#print axioms positive_wick_completion_between_twentyOne_and_twentyTwo_allowances
#print axioms positive_completion_without_depthTwo_still_exceeds_twenty_allowances
#print axioms oriented_marked_depthTwo_normalizes_to_accident
#print axioms marked_depthTwo_pair_normalizes_to_accident
#print axioms markedDisjointCollisionPairs_two_eq_empty_of_accidents_eq_empty
#print axioms markedDisjointCollisionPairs_two_eq_empty_of_differenceSignatureInjectiveModInversion
#print axioms firstPrime_markedDisjointCollisionPairs_two_eq_empty
#print axioms secondPrime_markedDisjointCollisionPairs_two_eq_empty

end ArkLib.ProximityGap.Frontier.BGKSevenOverlapProductionBudget
