/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MonicWfreeConsumers
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2RootBridgeS5

/-!
# BCIKS20 Appendix A.4 — monic W-free consumers for genuine §5

`P2MonicWfreeConsumers.lean` routes the monic W-free residual into the repaired P2 lift
identity. This cold companion exposes that same bridge at the genuine §5 API in
`S5Genuine`: once the global W-free equations and `H.leadingCoeff = 1` are supplied,
Claim 5.8 and Claim 5.8' can consume them without unpacking the intermediate restricted
Faà-di-Bruno match.

The hard #139 content remains the W-free equations themselves: the ξ telescope,
Faà-di-Bruno reindexing, and monic cancellation. The wrappers here are endpoint plumbing.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.S5Genuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The genuine §5 `LiftIdentityAt` bridge supplied by the global monic W-free P2 target. -/
theorem LiftIdentityAt.of_WfreeMatch {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) (t : ℕ) :
    LiftIdentityAt H x₀ R hHyp t :=
  BCIKS20.HenselNumerator.βHensel_lift_identity_of_WfreeMatch
    H x₀ R hHyp hlc hWfree t

/-- Claim 5.8 from the global monic W-free P2 target. -/
theorem claim58_genuine_via_WfreeMatch {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    {t : ℕ} (hlarge : SβLargeAt H x₀ R hHyp t) :
    αGenuine H x₀ R hHyp t = 0 :=
  claim58_genuine H hHyp hlarge
    (LiftIdentityAt.of_WfreeMatch H hHyp hlc hWfree t)

/-- Claim 5.8' tail vanishing from the global monic W-free P2 target. -/
theorem claim58prime_genuine_tail_via_WfreeMatch {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) {k : ℕ}
    (hlarge : ∀ t ≥ k, SβLargeAt H x₀ R hHyp t) :
    ∀ t ≥ k, αGenuine H x₀ R hHyp t = 0 :=
  claim58prime_genuine_tail H hHyp hlarge
    (fun t _ => LiftIdentityAt.of_WfreeMatch H hHyp hlc hWfree t)

/-- Claim 5.8' polynomial form from the global monic W-free P2 target. -/
theorem claim58prime_genuine_via_WfreeMatch {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) {k : ℕ}
    (hlarge : ∀ t ≥ k, SβLargeAt H x₀ R hHyp t) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : (𝕃 H)⟦X⟧) :=
  claim58prime_genuine H hHyp hlarge
    (fun t _ => LiftIdentityAt.of_WfreeMatch H hHyp hlc hWfree t)

#print axioms LiftIdentityAt.of_WfreeMatch
#print axioms claim58_genuine_via_WfreeMatch
#print axioms claim58prime_genuine_tail_via_WfreeMatch
#print axioms claim58prime_genuine_via_WfreeMatch

end BCIKS20.HenselNumerator.S5Genuine
