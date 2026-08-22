/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator

/-!
# BCIKS20 Appendix A.4 — P2 root bridge: residual ⇔ analytic root form

Companion to `HenselNumerator.lean`. The remaining mathematical content of (P2) is the
single carved residual `FaaDiBrunoSuccSumZeroResidual` — the per-successor-order
Faà-di-Bruno / `(A.1)` combinatorial collapse. `HenselNumerator.lean` already proves the
*forward* direction `coeff_succ_eval_βHenselAssembled` (residual ⟹ the order-`(t+1)`
coefficient of `eval (βHenselAssembled …) Q` vanishes), the order-`0` vanishing
`coeff_zero_eval_βHenselAssembled`, and the extensionality assembly
`assembledSeries_isRoot_of_coeff_succ_eval`.

This file closes the loop with the two missing *analytic* characterizations, so downstream
work can move freely between the combinatorial residual and the root form:

* `faaDiBrunoSuccSumZeroResidual_iff_coeff_succ_eval` — the carved residual is **exactly**
  "`βHenselAssembled` is a root of `Q` at every positive order". The reverse direction is
  new; both directions are immediate from the proven Faà-di-Bruno expansion
  `coeff_eval_Q_faaDiBruno`.
* `eval_βHenselAssembled_eq_zero_iff_residual` — the full root statement
  `eval (βHenselAssembled …) Q = 0` is **equivalent** to the carved residual, combining the
  proven order-`0` vanishing with the per-order bridge.

No new mathematical content is asserted: the term-level Faà-di-Bruno / `(A.1)` partition
equality (the actual hard residual, carved as `RestrictedFaaDiBrunoMatch` in `P2Close.lean`)
remains open. These are reduction endpoints over the already-proven expansion.
-/

noncomputable section

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The carved P2 residual is exactly the positive-order root condition.**
`FaaDiBrunoSuccSumZeroResidual` holds iff every order-`(t+1)` coefficient of
`eval (βHenselAssembled …) Q` vanishes. The forward direction is `coeff_succ_eval_βHenselAssembled`;
the reverse is new. Both follow term-by-term from the proven Faà-di-Bruno expansion
`coeff_eval_Q_faaDiBruno`, which lays each such coefficient bare as exactly the residual's sum. -/
theorem faaDiBrunoSuccSumZeroResidual_iff_coeff_succ_eval
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp ↔
      ∀ t : ℕ, PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0 := by
  unfold FaaDiBrunoSuccSumZeroResidual
  constructor
  · intro h t
    rw [coeff_eval_Q_faaDiBruno H x₀ R (βHenselAssembled H x₀ R hHyp) (t + 1)]
    exact h t
  · intro h t
    rw [← coeff_eval_Q_faaDiBruno H x₀ R (βHenselAssembled H x₀ R hHyp) (t + 1)]
    exact h t

/-- **The assembled series is a root of `Q` iff the carved P2 residual holds.**
Combines the proven order-`0` vanishing `coeff_zero_eval_βHenselAssembled` and the
extensionality assembly `assembledSeries_isRoot_of_coeff_succ_eval` with the per-order bridge
`faaDiBrunoSuccSumZeroResidual_iff_coeff_succ_eval`. This packages the whole-series root form of
(P2) as a clean biconditional with the single named residual. -/
theorem eval_βHenselAssembled_eq_zero_iff_residual
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0 ↔
      FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp := by
  rw [faaDiBrunoSuccSumZeroResidual_iff_coeff_succ_eval]
  constructor
  · intro hroot t
    rw [hroot, map_zero]
  · intro h
    exact assembledSeries_isRoot_of_coeff_succ_eval H x₀ R hHyp h

/-- **The assembled numerator series equals the genuine Hensel lift iff the carved P2
residual holds.** The forward direction uses `gammaGenuine_root` (the genuine lift is a
proven root of `Q`); the reverse is the proven uniqueness reduction
`βHenselAssembled_eq_gammaGenuine`. This packages the whole point of (P2) — that the `(A.1)`
recursion reproduces the genuine Hensel coefficients — as a clean biconditional with the
single named residual. -/
theorem βHenselAssembled_eq_gammaGenuine_iff_residual
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp ↔
      FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp := by
  rw [← eval_βHenselAssembled_eq_zero_iff_residual]
  constructor
  · intro heq
    rw [heq]
    exact gammaGenuine_root hHyp
  · intro hroot
    exact βHenselAssembled_eq_gammaGenuine H x₀ R hHyp hroot

/-- **Coefficient-level form: every assembled coefficient is the genuine Hensel coefficient
iff the carved P2 residual holds.** `coeff t (βHenselAssembled …) = αGenuine t` for all `t`
iff `FaaDiBrunoSuccSumZeroResidual`. This is the order-by-order shape downstream Appendix-A
arguments consume; it follows from `βHenselAssembled_eq_gammaGenuine_iff_residual` by
`PowerSeries.ext` (recall `αGenuine t = coeff t (gammaGenuine …)`). The forward direction
(residual ⟹ coefficient match) was already available as
`coeff_βHenselAssembled_eq_αGenuine_of_coeff_succ_eval`; this packages both directions. -/
theorem coeff_βHenselAssembled_eq_αGenuine_iff_residual
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    (∀ t : ℕ, PowerSeries.coeff t (βHenselAssembled H x₀ R hHyp)
        = αGenuine H x₀ R hHyp t) ↔
      FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp := by
  rw [← βHenselAssembled_eq_gammaGenuine_iff_residual]
  constructor
  · intro h
    ext t
    rw [h t]
    simp only [αGenuine]
  · intro h t
    rw [h]
    simp only [αGenuine]

/-- Directional consumer: the analytic root equation implies the carved P2 residual. -/
theorem FaaDiBrunoSuccSumZeroResidual.of_eval_βHenselAssembled_eq_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hroot : Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0) :
    FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp :=
  (eval_βHenselAssembled_eq_zero_iff_residual H x₀ R hHyp).1 hroot

/-- Directional consumer: the carved P2 residual gives the analytic root equation. -/
theorem eval_βHenselAssembled_eq_zero_of_residual
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp) :
    Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0 :=
  (eval_βHenselAssembled_eq_zero_iff_residual H x₀ R hHyp).2 hzero

/-- Lift-identity consumer from the analytic assembled-root form. -/
theorem βHensel_lift_identity_of_eval_βHenselAssembled_eq_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hroot : Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = αGenuine H x₀ R hHyp t
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) :=
  βHensel_lift_identity_of_assembledSeries_isRoot H x₀ R hHyp hroot t

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.faaDiBrunoSuccSumZeroResidual_iff_coeff_succ_eval
#print axioms BCIKS20.HenselNumerator.eval_βHenselAssembled_eq_zero_iff_residual
#print axioms BCIKS20.HenselNumerator.βHenselAssembled_eq_gammaGenuine_iff_residual
#print axioms BCIKS20.HenselNumerator.coeff_βHenselAssembled_eq_αGenuine_iff_residual
#print axioms BCIKS20.HenselNumerator.FaaDiBrunoSuccSumZeroResidual.of_eval_βHenselAssembled_eq_zero
#print axioms BCIKS20.HenselNumerator.eval_βHenselAssembled_eq_zero_of_residual
#print axioms BCIKS20.HenselNumerator.βHensel_lift_identity_of_eval_βHenselAssembled_eq_zero
