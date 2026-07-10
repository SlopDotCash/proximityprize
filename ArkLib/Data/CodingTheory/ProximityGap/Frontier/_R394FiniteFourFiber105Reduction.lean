/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R393FourFiberPrimitiveDecomposition

/-!
# R394: the finite-characteristic `105|G|` reduction

R393's canonicalized decomposition has constants that line up exactly with the characteristic-zero
R390 bound:

* pair multiplicity at most `8`;
* primitive four-fiber size at most `9|G|`;
* 12 canonical coordinate permutations of antipodal insertion.

Then `9 + 12*8 = 105`, so the full nonzero four-fiber is at most `105|G|`. The original
`4`/`24` consumer is retained for compatibility. R397 refuted multiplicity four at `n=128`; a
subsequent `n=256` counterexample also refuted multiplicity eight. Thus both capstones are valid
conditional consumers, but neither pointwise pair hypothesis is a universal producer. The direct
four-fiber bound remains the live finite statement.

The two component estimates are the new arithmetic residuals. This file proves their exact consumer
with no hidden transfer hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.R394FiniteFourFiber105Reduction

open ArkLib.ProximityGap.Frontier.R390CharZeroNonzeroRepFourBound
open ArkLib.ProximityGap.Frontier.R392PairFiberNecessaryForFourFiber
open ArkLib.ProximityGap.Frontier.R393FourFiberPrimitiveDecomposition

variable {F : Type*} [Field F] [DecidableEq F]

/-- The constant pair-multiplicity component required by the finite four-step route. -/
def PairMultiplicityFour (G : Finset F) : Prop :=
  ∀ c : F, c ≠ 0 → (pairFiber G c).card ≤ 4

/-- Corrected pair-multiplicity component after canonicalizing residual-coordinate order. -/
def PairMultiplicityEight (G : Finset F) : Prop :=
  ∀ c : F, c ≠ 0 → (pairFiber G c).card ≤ 8

/-- The linear primitive-remainder component required by the finite four-step route. -/
def PrimitiveFourBoundNine (G : Finset F) : Prop :=
  ∀ c : F, c ≠ 0 → (primitiveFourFiber G c).card ≤ 9 * G.card

/-- **Finite-characteristic `105|G|` capstone.** -/
theorem card_fourFiber_le_105_mul_card
    (G : Finset F) (hpair : PairMultiplicityFour G) (hprimitive : PrimitiveFourBoundNine G)
    {c : F} (hc : c ≠ 0) :
    (fourFiber G c).card ≤ 105 * G.card := by
  have h := card_fourFiber_le_of_components G c 9 4 (hprimitive c hc) (hpair c hc)
  norm_num at h ⊢
  exact h

/-- **Corrected finite-characteristic `105|G|` capstone.** The twelve-permutation cover tolerates
ordered pair multiplicity eight while retaining the exact characteristic-zero constant. -/
theorem card_fourFiber_le_105_mul_card_of_eight
    (G : Finset F) (hpair : PairMultiplicityEight G) (hprimitive : PrimitiveFourBoundNine G)
    {c : F} (hc : c ≠ 0) :
    (fourFiber G c).card ≤ 105 * G.card := by
  have hsplit := card_fourFiber_le_primitive_add_pair_twelve G c
  have hp := hprimitive c hc
  have hpairMul : G.card * (pairFiber G c).card ≤ G.card * 8 :=
    Nat.mul_le_mul_left G.card (hpair c hc)
  have hpair12 : 12 * (G.card * (pairFiber G c).card) ≤ 12 * (G.card * 8) :=
    Nat.mul_le_mul_left 12 hpairMul
  calc
    (fourFiber G c).card
        ≤ (primitiveFourFiber G c).card + 12 * (G.card * (pairFiber G c).card) := hsplit
    _ ≤ 9 * G.card + 12 * (G.card * 8) := Nat.add_le_add hp hpair12
    _ = 105 * G.card := by ring

end ArkLib.ProximityGap.Frontier.R394FiniteFourFiber105Reduction

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R394FiniteFourFiber105Reduction.card_fourFiber_le_105_mul_card
#print axioms
  ArkLib.ProximityGap.Frontier.R394FiniteFourFiber105Reduction.card_fourFiber_le_105_mul_card_of_eight
