/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.PlaceGeometryFromLocalSeries
import ArkLib.ToMathlib.BridgeDataMulForm
import ArkLib.ToMathlib.BetaRecGenuineBridge

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries

namespace ArkLib

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The per-`(t,z)` MatchingPoint from the completed `hαβ` construction (THE `mpFin` firing):**
combines `placeGeometry_of_localSeries` (the constructed local geometry) with
`bridgeData_of_mul_form` (the multiplied-out L12 reading, discharged by `coeff_localSeries_mul`
+ the signed-canonical bridge `betaRec_BcoeffSigned_eq_βHensel`; monic `w = 1`). Inputs are
exclusively GS-side: the proximate root `aP` (root + congruence + index-`t` vanishing) and
separability. -/
noncomputable def matchingPoint_of_localSeries {x₀ : F} {R : F[X][X][Y]}
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
        (PowerSeries.map (π_hat_z hHyp z root hx))).Separable)
    (t : ℕ) (haP_coeff : PowerSeries.coeff t aP = 0) :
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
      (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z root :=
  MpFinSupply.mkMatchingPoint_of_graph_vanishing
    (g := placeGeometry_of_localSeries hHyp hξ hlc z root hx aP haP_root haP_cong hsep)
    (bd := MpFinSupply.bridgeData_of_mul_form (1 : F) ((π_z z root) (ξ x₀ R H hHyp))
      (t + 1) (2 * t - 1)
      (by
        rw [one_pow, one_mul, BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel]
        exact coeff_localSeries_mul hHyp z root hx t)
      one_ne_zero hx haP_coeff)

/-- **The GS-handshake variant: per-`(t,z)` MatchingPoint from the GS matching-factor
divisibility.** Identical to `matchingPoint_of_localSeries`, but the proximate-root fact
arrives as the divisibility `(Y − C aP) ∣ f` — the exact shape of the GS matching-factor
cargo — converted by `dvd_iff_isRoot`. -/
noncomputable def matchingPoint_of_localSeries_dvd {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    (aP : PowerSeries F)
    (hdvd : (Polynomial.X - Polynomial.C aP) ∣
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z root hx))))
    (haP_cong : aP - PowerSeries.C ((π_z z root)
        (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z root hx))).Separable)
    (t : ℕ) (haP_coeff : PowerSeries.coeff t aP = 0) :
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
      (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z root :=
  matchingPoint_of_localSeries hHyp hξ hlc z root hx aP
    (Polynomial.dvd_iff_isRoot.mp hdvd) haP_cong hsep t haP_coeff

/-- **The per-`z` separability supply:** the specialized matching polynomial inherits
separability from `Y`-separability of `R` itself (the GS squarefree-factor condition), by
mapping the coprimality witnesses through the two coefficient homs. -/
theorem specialized_separable_of_R_separable {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    (hR : R.Separable) :
    ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable :=
  (hR.map (f := coeffHom_loc x₀ hHyp)).map
    (f := PowerSeries.map (π_hat_z hHyp z root hx))

end ArkLib

#print axioms ArkLib.matchingPoint_of_localSeries
#print axioms ArkLib.matchingPoint_of_localSeries_dvd
#print axioms ArkLib.specialized_separable_of_R_separable
