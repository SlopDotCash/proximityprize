/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GSSurfaceKeystone
import ArkLib.ToMathlib.NewtonTailTransport

/-!
# Issue #304 — `htail` of `GSSurfaceData` from the pigeonhole matching lane

The Claim-5.8′ ab-initio capstone (`gammaGenuine_eq_trunc_of_pigeonhole_abInitio`)
specializes to the **section divisor** `H := T − C v` with three hypotheses turning FREE:
monicity and positive degree are structural, and the per-place `ξ`-nonvanishing holds at
EVERY incidence root (`π_z_ξ_ne_zero_sectionH` — the `ξ`-content is a unit constant).  The
resulting truncation identity extracts to the `αFromBeta`-tail through the monic bridge —
i.e. **the `htail` field of `GSSurfaceData` is produced from pigeonhole matching data**:
per-place incidence + specialized matching divisibility + decoded degree bounds + the graded
numeric chain.  Together with `SectionFromSurface` (the section `Hypotheses`) and
`GSSurfaceDegSupply` (the weight reduction of `hdegc`), every analytic field of the keystone
bundle now has a GS-construction-level producer.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claim 5.8′), §6, Appendix A.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator BCIKS20.HenselNumerator.S5Genuine
open ProximityPrize.BCIKS20.GammaGenuine
open scoped BigOperators

namespace ArkLib

namespace GSSurfaceKeystone

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {x₀ : F} {R : F[X][X][Y]} {v : F[X]}
variable [Fact (Irreducible (Polynomial.X - Polynomial.C v : F[X][Y]))]
variable [Fact (0 < (Polynomial.X - Polynomial.C v : F[X][Y]).natDegree)]

/-- **The `htail` field of `GSSurfaceData` from the pigeonhole matching lane** — the
Claim-5.8′ ab-initio capstone at the section divisor, with monicity, positive degree, and
the per-place `ξ`-nonvanishing all structural. -/
theorem htail_sectionH_of_pigeonhole
    (hHyp : Hypotheses x₀ R (Polynomial.X - Polynomial.C v))
    {D DX k : ℕ} (hk : 0 < k)
    (hD : Bivariate.totalDegree (Polynomial.X - Polynomial.C v : F[X][Y]) ≤ D)
    (hd2 : 2 ≤ Bivariate.natDegreeY R) (hd2' : 2 ≤ R.natDegree)
    (hdHD : (Polynomial.X - Polynomial.C v : F[X][Y]).natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDX : ∀ i, (R.coeff i).natDegree ≤ DX)
    {matchingSet : Finset F} {Pz : F → F[X]}
    (hinc : ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((Pz z).eval x₀) (Polynomial.X - Polynomial.C v) = 0)
    (hdvdM : ∀ z ∈ matchingSet, Polynomial.X - Polynomial.C (Pz z) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (hR : R.Separable)
    {n : ℕ}
    (hbudget : gradedCardBudget (Bivariate.natDegreeY R) D
        (Polynomial.X - Polynomial.C v : F[X][Y]).natDegree
        (DX + R.natDegree * (k - 1)) < n)
    (hcard : n ≤ matchingSet.card) :
    ∀ t, k ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R (Polynomial.X - Polynomial.C v) hHyp
        (BetaRecGenuineBridge.BcoeffSigned (Polynomial.X - Polynomial.C v) x₀ R) t = 0 := by
  have htr := NewtonTailTransport.gammaGenuine_eq_trunc_of_pigeonhole_abInitio hHyp
    (ξ_ne_zero_sectionH hHyp hd2') hk hD
    (by rw [sectionH_natDegree]; omega)
    (sectionH_monic v) hd2 hdHD hD_Rx0 hRgrade hDX hinc hdvdM hdeg
    (fun z hz => π_z_ξ_ne_zero_sectionH hHyp hd2' z _) hR hbudget hcard
  intro t ht
  rw [BetaRecGenuineBridge.alphaFromBeta_BcoeffSigned_eq_αGenuine_of_monic x₀ R hHyp
    (sectionH_monic v).leadingCoeff t]
  have hcoeff : PowerSeries.coeff t
      (gammaGenuine x₀ R (Polynomial.X - Polynomial.C v) hHyp)
      = αGenuine (Polynomial.X - Polynomial.C v) x₀ R hHyp t := rfl
  rw [← hcoeff, htr, Polynomial.coeff_coe, PowerSeries.coeff_trunc,
    if_neg (not_lt.mpr ht)]

end GSSurfaceKeystone

end ArkLib

/-! ## Axiom audit. -/
#print axioms ArkLib.GSSurfaceKeystone.htail_sectionH_of_pigeonhole
