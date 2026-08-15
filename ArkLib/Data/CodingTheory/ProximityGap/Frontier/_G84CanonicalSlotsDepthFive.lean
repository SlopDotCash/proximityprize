/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharPMomentRecursion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G81FactorialPaddingWickAbsorption
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G84CanonicalSlotCode

/-!
# G84: canonical core slots close depth four, but not depth five

The corrected padding code used arbitrary embeddings `Fin s ↪ Fin r`, costing
`(r descFactorial s)^2`. Once endpoint slots are read in their ambient increasing order, only the
two underlying `s`-subsets are data. Their exact cost is `choose(r,s)^2`, saving `(s!)^2` without
quotienting any genuine endpoint mass.

The scaling-orbit quotient cannot itself be used as the decoder's core type: reconstructing an
actual core also requires its scale, restoring the factor `n`. With actual core counts, canonical
slots combine with the unconditional recursion `E₄ ≤ n⁴ E₂` to absorb depth four at the
production point for the generous fourth-moment constant `C = 7600` in `E₂² ≤ C² n⁵`.

The same route fails sharply at depth five. Even the optimistic constant `C = 1` propagated through
`E₅ ≤ n⁶ E₂` leaves a canonical envelope larger than Wick. Thus canonical slot ordering
repairs the honest depth-four claim but does not bypass the depth-five analytic residual.

Honest scope: the code cardinality and arithmetic consumers are proven. The concrete decoder must
be shown to use increasing core slots, and the production fourth-moment estimate remains an input.
Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G84CanonicalSlotsDepthFive

open ArkLib.ProximityGap.CharPMomentRecursion
open ArkLib.ProximityGap.SubgroupGaussSumMoment

/-- **Orbit-quotient decoder no-go.** If a nonempty core type has cardinality `n` times its orbit
representative type with `n>1`, no decoder from representatives alone can be surjective onto the
actual cores. The missing scale coordinate must be restored. -/
theorem no_surjective_decoder_from_orbit_representatives
    {Q X : Type*} [Finite Q] [Finite X] [Nonempty Q]
    (n : ℕ) (hn : 1 < n) (hcard : Nat.card X = Nat.card Q * n) :
    ¬ ∃ decode : Q → X, Function.Surjective decode := by
  rintro ⟨decode, hdecode⟩
  have hle : Nat.card X ≤ Nat.card Q :=
    Nat.card_le_card_of_surjective decode hdecode
  have hq : 0 < Nat.card Q := Nat.card_pos
  have hlt : Nat.card Q < Nat.card X := by
    calc
      Nat.card Q = Nat.card Q * 1 := by simp
      _ < Nat.card Q * n := (Nat.mul_lt_mul_left hq).2 hn
      _ = Nat.card X := hcard.symm
  exact (not_lt_of_ge hle) hlt

/-- Two recursion steps give `E₄ ≤ n⁴E₂`. -/
theorem rEnergy_four_le_card_pow_four_mul_two
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (G : Finset F) :
    rEnergy G 4 ≤ G.card ^ 4 * rEnergy G 2 := by
  calc
    rEnergy G 4 ≤ G.card ^ 2 * rEnergy G 3 := by
      simpa using rEnergy_succ_le G 3
    _ ≤ G.card ^ 2 * (G.card ^ 2 * rEnergy G 2) := by
      gcongr
      simpa using rEnergy_succ_le G 2
    _ = G.card ^ 4 * rEnergy G 2 := by ring

/-- Three recursion steps give `E₅ ≤ n⁶E₂`. -/
theorem rEnergy_five_le_card_pow_six_mul_two
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (G : Finset F) :
    rEnergy G 5 ≤ G.card ^ 6 * rEnergy G 2 := by
  calc
    rEnergy G 5 ≤ G.card ^ 2 * rEnergy G 4 := by
      simpa using rEnergy_succ_le G 4
    _ ≤ G.card ^ 2 * (G.card ^ 4 * rEnergy G 2) := by
      gcongr
      exact rEnergy_four_le_card_pow_four_mul_two G
    _ = G.card ^ 6 * rEnergy G 2 := by ring

/-- An actual depth-four core family bounded by `E₄`, the recurrence, and a fourth-moment square
bound satisfies `K² ≤ C²n¹³`. No orbit quotient is used. -/
theorem sq_core_depth_four_of_energy_two
    {n K E4 E2 C : ℕ}
    (hK : K ≤ E4) (hrec : E4 ≤ n ^ 4 * E2)
    (hE2 : E2 ^ 2 ≤ C ^ 2 * n ^ 5) :
    K ^ 2 ≤ C ^ 2 * n ^ 13 := by
  calc
    K ^ 2 ≤ E4 ^ 2 := Nat.pow_le_pow_left hK 2
    _ ≤ (n ^ 4 * E2) ^ 2 := Nat.pow_le_pow_left hrec 2
    _ = n ^ 8 * E2 ^ 2 := by ring
    _ ≤ n ^ 8 * (C ^ 2 * n ^ 5) := by gcongr
    _ = C ^ 2 * n ^ 13 := by ring

/-- Opaque names keep the production certificates cheap to reuse. -/
def productionN : ℕ := 2 ^ 30
def productionDepthFourBase : ℕ :=
  ((110 : ℕ).choose 4) ^ 2 * (110 - 4).factorial * productionN ^ (110 - 4)
def productionDepthFiveBase : ℕ :=
  ((110 : ℕ).choose 5) ^ 2 * (110 - 5).factorial * productionN ^ (110 - 5)
def productionWickBudget : ℕ :=
  Nat.doubleFactorial (2 * 110 - 1) * productionN ^ 110
def productionDepthFourCoreCeiling : ℕ := 7600 * productionN ^ 6 * 2 ^ 15
def productionDepthFiveC1CoreCeiling : ℕ := productionN ^ 8 * 2 ^ 15

/-- At `n=2^30`, the square bound converts to the explicit integer ceiling
`K ≤ 7600*n^6*2^15`. -/
theorem production_depth_four_sq_to_ceiling {K : ℕ}
    (hK : K ^ 2 ≤ 7600 ^ 2 * productionN ^ 13) :
    K ≤ productionDepthFourCoreCeiling := by
  apply (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp
  calc
    K ^ 2 ≤ 7600 ^ 2 * productionN ^ 13 := hK
    _ = productionDepthFourCoreCeiling ^ 2 := by
      norm_num [productionN, productionDepthFourCoreCeiling]

/-- Exact linear production arithmetic for the accepted depth-four ceiling. -/
theorem production_depth_four_C7600_budget :
    productionDepthFourCoreCeiling * productionDepthFourBase ≤
      productionWickBudget := by
  norm_num [productionN, productionDepthFourCoreCeiling, productionDepthFourBase,
    productionWickBudget, Nat.choose, Nat.doubleFactorial]

/-- Canonical slots plus the depth-four energy square bound absorb the actual core family. -/
theorem production_depth_four_canonical_absorbed
    {K W : ℕ}
    (hW : W ≤ canonicalPadEnvelope productionN 110 K 4)
    (hK : K ^ 2 ≤ 7600 ^ 2 * productionN ^ 13) :
    W ≤ productionWickBudget := by
  have hform : canonicalPadEnvelope productionN 110 K 4 =
      K * productionDepthFourBase := by
    unfold canonicalPadEnvelope productionDepthFourBase
    ring
  calc
    W ≤ canonicalPadEnvelope productionN 110 K 4 := hW
    _ = K * productionDepthFourBase := hform
    _ ≤ productionDepthFourCoreCeiling * productionDepthFourBase := by
      gcongr
      exact production_depth_four_sq_to_ceiling hK
    _ ≤ productionWickBudget := production_depth_four_C7600_budget

/-- **Depth-five red-team boundary.** Even `E₂² ≤ n⁵` (`C=1`) propagated through
`E₅ ≤ n⁶E₂` gives `K² ≤ n¹⁷`; its canonical envelope is already larger than Wick.
This refutes the claim that shallow energy plus canonical slots alone closes depth five. -/
theorem production_depth_five_C1_square_envelope_exceeds :
    productionWickBudget <
      productionDepthFiveC1CoreCeiling * productionDepthFiveBase := by
  norm_num [productionN, productionDepthFiveC1CoreCeiling, productionDepthFiveBase,
    productionWickBudget, Nat.choose, Nat.doubleFactorial]

end ArkLib.ProximityGap.Frontier.G84CanonicalSlotsDepthFive

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G84CanonicalSlotsDepthFive.no_surjective_decoder_from_orbit_representatives
#print axioms
  ArkLib.ProximityGap.Frontier.G84CanonicalSlotsDepthFive.rEnergy_four_le_card_pow_four_mul_two
#print axioms
  ArkLib.ProximityGap.Frontier.G84CanonicalSlotsDepthFive.rEnergy_five_le_card_pow_six_mul_two
#print axioms
  ArkLib.ProximityGap.Frontier.G84CanonicalSlotsDepthFive.sq_core_depth_four_of_energy_two
#print axioms
  ArkLib.ProximityGap.Frontier.G84CanonicalSlotsDepthFive.production_depth_four_C7600_budget
#print axioms
  ArkLib.ProximityGap.Frontier.G84CanonicalSlotsDepthFive.production_depth_four_canonical_absorbed
#print axioms
  ArkLib.ProximityGap.Frontier.G84CanonicalSlotsDepthFive.production_depth_five_C1_square_envelope_exceeds
