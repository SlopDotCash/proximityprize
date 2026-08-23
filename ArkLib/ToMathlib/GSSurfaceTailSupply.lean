/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GSSurfaceKeystone
import ArkLib.ToMathlib.BetaTailDegreeVanishing

/-!
# Issue #304 — the `htail` supply of `GSSurfaceData` from the tail window

The `htail` field of the keystone bundle (`αFromBeta`-tail vanishing from order `n` on) is
supplied by the **proven** tail-propagation capstone
(`BetaTail.βHensel_eq_zero_of_initial_window`): a vanishing initial window `[1, T₀]` (with
`T₀` bounding the lift-`X` degrees of `R`'s fiber coefficients) propagates to ALL orders
`t ≥ 1`, and a vanishing `βHensel`-numerator kills the quotient `αFromBeta` directly
(`alphaFromBeta_eq_zero_of_embedding_zero` — no lift identity needed).

What remains GS-level for this field is therefore only the **window itself** — the finitely
many vanishings `βHensel l = 0`, `1 ≤ l ≤ T₀` — which is the §5 weight/matching content
(the Claim-5.8 lane), not analytic Hensel machinery.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5, Appendix A.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open scoped BigOperators

namespace ArkLib

namespace GSSurfaceKeystone

variable {F : Type} [Field F]
variable {x₀ : F} {R : F[X][X][Y]} {v : F[X]}

/-- **The `htail` field of `GSSurfaceData`, from the tail window.**  A vanishing initial
window `[1, T₀]` with `T₀` bounding the fiber-coefficient degrees of `R` supplies the full
`αFromBeta`-tail vanishing at every order `t ≥ n ≥ 1`. -/
theorem htail_sectionH_of_window
    (hHyp : Hypotheses x₀ R (Polynomial.X - Polynomial.C v))
    {T₀ : ℕ} (hdX : ∀ j, (R.coeff j).natDegree ≤ T₀)
    (hwin : ∀ l, 1 ≤ l → l ≤ T₀ →
      βHensel (Polynomial.X - Polynomial.C v) x₀ R hHyp l = 0)
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ t, n ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R (Polynomial.X - Polynomial.C v) hHyp
        (BetaRecGenuineBridge.BcoeffSigned (Polynomial.X - Polynomial.C v) x₀ R) t = 0 := by
  intro t ht
  apply BetaToCurveCoeffPolys.alphaFromBeta_eq_zero_of_embedding_zero
  rw [BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel,
    BCIKS20.HenselNumerator.BetaTail.βHensel_eq_zero_of_initial_window
      (Polynomial.X - Polynomial.C v) x₀ R hHyp hdX hwin t (le_trans hn ht), map_zero]

end GSSurfaceKeystone

end ArkLib

/-! ## Axiom audit. -/
#print axioms ArkLib.GSSurfaceKeystone.htail_sectionH_of_window
