/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G117HBKFloorSafeParameters
import ArkLib.Data.CodingTheory.ProximityGap.StepanovPointCountEngine

/-!
# G118: production HBK prefix bound from the special auxiliary

G117 supplies explicit floor-safe parameters and proves that their degree quotient has normalized
coefficient `4`.  The generic Stepanov counting engine already turns a nonzero auxiliary of degree
`d`, vanishing to multiplicity `D` on `E`, into `#E ≤ d/D`.

This file welds those results.  For every production prefix length `1 ≤ T ≤ 2^30`, any HBK special
auxiliary with the advertised degree and multiplicity yields

`(#E)^3 ≤ 64 * (2^30*T)^2`.

Thus the only remaining Lemma-5 construction seam is special-form auxiliary existence and
nonvanishing.  In particular, generic high-multiplicity interpolation is not silently substituted:
HBK's gain comes from imposing polynomial identities for `T` coset representatives rather than one
independent condition block for every point of `E`. Issue #466.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.G118HBKPrefixFromAuxiliary

open Polynomial
open ArkLib.CodingTheory.Round6Stepanov
open G117HBKFloorSafeParameters

variable {F : Type*} [Field F] [DecidableEq F]

/-- The exact floor-safe Stepanov count for the production HBK parameters. -/
theorem production_card_le_degreeQuotient_of_auxiliary
    (E : Finset F) {T : ℕ} (hTle : T ≤ 2 ^ 30)
    (hex :
      let B := ceilCubeRoot (2 * (2 ^ 30) * T)
      let A := roundedA (2 ^ 30) B
      let D := roundedD (2 ^ 30) B
      ∃ Ψ : F[X], Ψ ≠ 0 ∧
        (∀ x ∈ E, D ≤ Ψ.rootMultiplicity x) ∧
        Ψ.natDegree ≤ A + 2 * (2 ^ 30) * B - 1) :
    let B := ceilCubeRoot (2 * (2 ^ 30) * T)
    E.card ≤ degreeQuotient (2 ^ 30) (roundedA (2 ^ 30) B) B := by
  dsimp only at hex ⊢
  let B := ceilCubeRoot (2 * (2 ^ 30) * T)
  let A := roundedA (2 ^ 30) B
  let D := roundedD (2 ^ 30) B
  have hA : 32 ≤ A := production_roundedA_ge_thirtyTwo hTle
  have hD : 0 < D := by
    have : 0 < A - 1 := by omega
    simpa [D, roundedD] using this
  have hcount : E.card ≤ (A + 2 * (2 ^ 30) * B - 1) / D :=
    stepanov_card_le_of_aux E hD hex
  simpa [degreeQuotient, A, D, B, roundedD] using hcount

/-- **Production coefficient-4 prefix bound.** This is the cube-free form of
`#E ≤ 4*(2^30*T)^(2/3)`. -/
theorem production_card_cube_le_of_auxiliary
    (E : Finset F) {T : ℕ} (hT : 0 < T) (hTle : T ≤ 2 ^ 30)
    (hex :
      let B := ceilCubeRoot (2 * (2 ^ 30) * T)
      let A := roundedA (2 ^ 30) B
      let D := roundedD (2 ^ 30) B
      ∃ Ψ : F[X], Ψ ≠ 0 ∧
        (∀ x ∈ E, D ≤ Ψ.rootMultiplicity x) ∧
        Ψ.natDegree ≤ A + 2 * (2 ^ 30) * B - 1) :
    E.card ^ 3 ≤ 64 * ((2 ^ 30) * T) ^ 2 := by
  let B := ceilCubeRoot (2 * (2 ^ 30) * T)
  let Q := degreeQuotient (2 ^ 30) (roundedA (2 ^ 30) B) B
  have hcard : E.card ≤ Q :=
    production_card_le_degreeQuotient_of_auxiliary E hTle hex
  calc
    E.card ^ 3 ≤ Q ^ 3 := Nat.pow_le_pow_left hcard 3
    _ ≤ 64 * ((2 ^ 30) * T) ^ 2 := production_degreeQuotient_cube_le hT hTle

end ArkLib.ProximityGap.Frontier.G118HBKPrefixFromAuxiliary

#print axioms
  ArkLib.ProximityGap.Frontier.G118HBKPrefixFromAuxiliary.production_card_le_degreeQuotient_of_auxiliary
#print axioms
  ArkLib.ProximityGap.Frontier.G118HBKPrefixFromAuxiliary.production_card_cube_le_of_auxiliary
