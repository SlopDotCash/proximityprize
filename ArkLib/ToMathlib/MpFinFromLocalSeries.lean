/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.MatchingPointFromLocalSeries

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries

namespace ArkLib

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The family-level `mpFin` supply from the completed construction** — the exact
`HcardDischarge`-shaped field `∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet, MatchingPoint …`
at the signed canonical coefficients, from per-`z` factor-level GS cargo: the unit
condition `π_z(ξ) ≠ 0`, the proximate root divisibility, its order-0 matching congruence,
the per-index vanishing window, and `R`-separability (one global fact via
`specialized_separable_of_R_separable`). -/
noncomputable def mpFin_of_localSeries {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (hR : R.Separable)
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (hx : ∀ z ∈ matchingSet, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (aP : F → PowerSeries F)
    (k T : ℕ)
    (hdvd : ∀ z (hz : z ∈ matchingSet),
      (Polynomial.X - Polynomial.C (aP z)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))))
    (hcong : ∀ z ∈ matchingSet,
      aP z - PowerSeries.C ((π_z z (root z))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hvanish : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      PowerSeries.coeff t (aP z) = 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z (root z) :=
  fun t hkt htT z hz =>
    matchingPoint_of_localSeries_dvd hHyp hξ hlc z (root z) (hx z hz) (aP z)
      (hdvd z hz) (hcong z hz)
      (specialized_separable_of_R_separable hHyp z (root z) (hx z hz) hR)
      t (hvanish t hkt htT z hz)

end ArkLib

#print axioms ArkLib.mpFin_of_localSeries
