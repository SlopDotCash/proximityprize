/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.LocalHenselSeries
import ArkLib.ToMathlib.MpFinSupply

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries

namespace ArkLib

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The constant coefficient of `localSeries` is `π_z(βHensel 0)` — the `t = 0` instance of
the read-off (the `ξ`-power truncates: `2·0 − 1 = 0`). -/
theorem constantCoeff_localSeries {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) :
    PowerSeries.constantCoeff (localSeries hHyp z root hx)
      = (π_z z root) (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0) := by
  have h := coeff_localSeries_mul hHyp z root hx 0
  simpa using h

/-- **`PlaceGeometry` from the constructed local series (the `hαβ`-plumbing constructor):**
`f` and `aβ` are supplied by the landed construction (`localSeries` + its root fact + the `t=0`
congruence); the proximate-root data (`aP`, its root/congruence) and separability arrive from
the GS side. -/
noncomputable def placeGeometry_of_localSeries {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    (aP : PowerSeries F)
    (haP_root : ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z root hx))).IsRoot aP)
    (haP_cong : aP - PowerSeries.C ((π_z z root)
        (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z root hx))).Separable) :
    MpFinSupply.PlaceGeometry (F := F) z where
  f := (R.map (coeffHom_loc x₀ hHyp)).map (PowerSeries.map (π_hat_z hHyp z root hx))
  aβ := localSeries hHyp z root hx
  aP := aP
  a₀ := PowerSeries.C ((π_z z root) (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
  haβ_root := localSeries_isRoot_of_monic hHyp hξ hlc z root hx
  haP_root := haP_root
  haβ_cong := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    rw [map_sub, constantCoeff_localSeries hHyp z root hx, PowerSeries.constantCoeff_C,
      sub_self]
  haP_cong := haP_cong
  hsep := hsep

end ArkLib

#print axioms ArkLib.constantCoeff_localSeries
#print axioms ArkLib.placeGeometry_of_localSeries
