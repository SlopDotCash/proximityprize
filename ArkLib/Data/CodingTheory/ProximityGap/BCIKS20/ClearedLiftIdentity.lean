/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ClearedRecursion

/-!
# The cleared lift identity — `βHenselC` assembled series and the (A.4) identity (#357 route a)

The cleared-recursion re-foundation of the Claim-5.10 kill chain at the ORIGINAL non-monic
factor: this file mirrors the landed uncleared block
(`βHenselAssembled` / `βHenselAssembled_constantCoeff` / `βHenselAssembled_eq_gammaGenuine` /
`βHensel_lift_identity_of_assembledSeries_isRoot`, `HenselNumerator.lean`), substituting the
paper-faithful W-cleared recursion `βHenselC` (`ClearedRecursion.lean`) for the divergent
un-cleared `βHensel` (finding 14).

* `βHenselAssembledC` — the assembled numerator series of `βHenselC`: the `t`-th coefficient
  is the (A.4) normalized numerator `embedding (βHenselC … t) / (W^{t+1}·ξ^{2t−1})`.
* `LiftIdentityAtC` — the cleared per-`t` lift identity
  `embedding (βHenselC … t) = αGenuine t · W^{t+1} · ξ̂^{2t−1}`.
* `liftIdentityAtC_zero` — the base case `t = 0`, PROVEN (from `βHenselC_zero`, identical to
  the uncleared base since the recursions agree at `0`).
* `βHenselAssembledC_constantCoeff` — `constantCoeff (βHenselAssembledC …) = α₀`.
* `βHenselAssembledC_eq_gammaGenuine` — uniqueness reduction: GIVEN the root fact
  `eval (βHenselAssembledC …) Q = 0`, the assembled series IS the genuine Hensel root.
* `liftIdentityAtC_of_assembledSeries_isRoot` — the full per-`t` cleared lift identity from
  the single root hypothesis, by clearing the (nonzero, `den_ne_zero`) denominator.

The root hypothesis `hroot` is the named interim residual of the route-(a) lane
(`assembledSeriesC_isRoot`, the paper's A.1/A.4 faithfulness) — carried explicitly, never
axiom-laundered.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654 — Appendix A (A.1), (A.4).
-/

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)]
  [Fact (0 < H.natDegree)]

/-- The cleared base case embeds to the genuine function-field variable `T`: identical to the
uncleared base (`embeddingOf𝒪Into𝕃_βHensel_zero`), since `βHenselC 0 = mk X = βHensel 0`. -/
theorem embeddingOf𝒪Into𝕃_βHenselC_zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    embeddingOf𝒪Into𝕃 H (βHenselC (H := H) x₀ R hHyp 0) = functionFieldT (H := H) := by
  rw [βHenselC_zero, embeddingOf𝒪Into𝕃_mk, liftBivariate_X]

/-- **The assembled numerator series of `βHenselC`.**  The `t`-th coefficient is the (A.4)
*normalized* numerator `embedding (βHenselC … t) / (W^{t+1}·ξ^{2t−1})`.  By construction, the
cleared lift identity at `t` holds iff this series' `t`-th coefficient equals `αGenuine t`; so
proving the identity for all `t` is exactly proving `βHenselAssembledC = gammaGenuine`.
Mirror of the landed `βHenselAssembled` at the cleared recursion. -/
noncomputable def βHenselAssembledC (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : PowerSeries (𝕃 H) :=
  PowerSeries.mk (fun t =>
    embeddingOf𝒪Into𝕃 H (βHenselC (H := H) x₀ R hHyp t)
      / ((liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)))

/-- **The cleared per-`t` lift identity** (the cleared analogue of
`S5Genuine.LiftIdentityAt`): `embedding (βHenselC … t) = αGenuine t · W^{t+1} · ξ̂^{2t−1}`.
In `ℕ`-truncated subtraction `2*t − 1` realises the paper's `e_t = max(0, 2t−1)` exactly. -/
def LiftIdentityAtC (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) : Prop :=
  embeddingOf𝒪Into𝕃 H (βHenselC (H := H) x₀ R hHyp t)
    = αGenuine H x₀ R hHyp t
        * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
        * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)

/-- **The cleared base case `t = 0` — PROVEN, axiom-clean.**  The cleared lift identity at
`t = 0`: `embedding (βHenselC … 0) = αGenuine 0 · W^{1} · ξ^{0} = (T/W)·W = T`. -/
theorem liftIdentityAtC_zero (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    LiftIdentityAtC x₀ R hHyp 0 := by
  rw [LiftIdentityAtC, embeddingOf𝒪Into𝕃_βHenselC_zero, αGenuine_zero, α₀]
  simp only [Nat.mul_zero, Nat.zero_sub, pow_zero, mul_one, zero_add, pow_one]
  rw [div_mul_cancel₀ _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))]

/-- **Order-0 of the cleared assembled series — PROVEN, axiom-clean.**
`constantCoeff (βHenselAssembledC …) = α₀`: the `t = 0` coefficient is
`embedding (βHenselC … 0) / (W^{0+1}·ξ^{0}) = T / W = α₀`. -/
theorem βHenselAssembledC_constantCoeff (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    PowerSeries.constantCoeff (βHenselAssembledC x₀ R hHyp) = α₀ H := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, βHenselAssembledC,
    PowerSeries.coeff_mk, embeddingOf𝒪Into𝕃_βHenselC_zero]
  simp only [Nat.mul_zero, Nat.zero_sub, pow_zero, mul_one, zero_add, pow_one]
  rw [α₀]

/-- **The cleared assembled series is the genuine root, GIVEN it is a root of `Q` (PROVEN
reduction, axiom-clean).**  By `gammaGenuine_unique`, any root of `Q` whose constant
coefficient is `α₀` equals `gammaGenuine`.  The constant-coefficient side is the proven base
case `βHenselAssembledC_constantCoeff`; the root side is supplied as `hroot` — the single
named residual of the route-(a) lane (`assembledSeriesC_isRoot`). -/
theorem βHenselAssembledC_eq_gammaGenuine (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hroot : Polynomial.eval (βHenselAssembledC x₀ R hHyp) (Q x₀ R H) = 0) :
    βHenselAssembledC x₀ R hHyp = gammaGenuine x₀ R H hHyp :=
  gammaGenuine_unique hHyp (βHenselAssembledC_constantCoeff x₀ R hHyp) hroot

/-- **The full cleared lift identity, GIVEN the assembled series is a root (PROVEN reduction,
axiom-clean).**  Once `βHenselAssembledC` is identified with `gammaGenuine`
(`βHenselAssembledC_eq_gammaGenuine`), its `t`-th coefficient *is* `αGenuine t`, and clearing
the (nonzero, `den_ne_zero` — monicity-FREE) denominator yields `LiftIdentityAtC` at
**every** `t` from the single root hypothesis. -/
theorem liftIdentityAtC_of_assembledSeries_isRoot (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hroot : Polynomial.eval (βHenselAssembledC x₀ R hHyp) (Q x₀ R H) = 0) (t : ℕ) :
    LiftIdentityAtC x₀ R hHyp t := by
  have hcoeff : αGenuine H x₀ R hHyp t
      = embeddingOf𝒪Into𝕃 H (βHenselC (H := H) x₀ R hHyp t)
          / ((liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
              * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) := by
    rw [αGenuine, ← βHenselAssembledC_eq_gammaGenuine x₀ R hHyp hroot, βHenselAssembledC,
      PowerSeries.coeff_mk]
  rw [LiftIdentityAtC, hcoeff, mul_assoc, div_mul_cancel₀ _ (den_ne_zero H x₀ R hHyp t)]

end BCIKS20.HenselNumerator

/-! ## Axiom audit -/
#print axioms BCIKS20.HenselNumerator.embeddingOf𝒪Into𝕃_βHenselC_zero
#print axioms BCIKS20.HenselNumerator.liftIdentityAtC_zero
#print axioms BCIKS20.HenselNumerator.βHenselAssembledC_constantCoeff
#print axioms BCIKS20.HenselNumerator.βHenselAssembledC_eq_gammaGenuine
#print axioms BCIKS20.HenselNumerator.liftIdentityAtC_of_assembledSeries_isRoot
