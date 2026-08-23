/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.RationalFunctionsCore

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The localized place evaluation `π̂_z`** (step 3 of the `hαβ` plan): the extension of
`π_z : 𝒪 H →+* F` to the `ξ`-inverted localization, defined whenever `π_z(ξ) ≠ 0` (the
in-data unit condition `hx`). `IsLocalization.Away.lift` supplies the ring hom. -/
noncomputable def π_hat_z {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) :
    Localization.Away (ξ x₀ R H hHyp) →+* F :=
  Localization.awayLift (π_z z root) (ξ x₀ R H hHyp) (isUnit_iff_ne_zero.mpr hx)

/-- `π̂_z` restricts to `π_z` on `𝒪 H` (the localization structure map is a section). -/
theorem π_hat_z_comp {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) (a : 𝒪 H) :
    π_hat_z hHyp z root hx (algebraMap (𝒪 H) (Localization.Away (ξ x₀ R H hHyp)) a)
      = (π_z z root) a := by
  unfold π_hat_z
  exact IsLocalization.lift_eq _ a

end ArkLib

#print axioms ArkLib.π_hat_z
#print axioms ArkLib.π_hat_z_comp
