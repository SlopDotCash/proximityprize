/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.EndToEnd

/-!
# The affine-pair extraction — heavy branches decode to ONE affine family (#302)

The positive half of the hlin discharge ([BCIKS20] §5 Step 7's output): on a heavy monic
branch, the Vandermonde globalization (`Claim59Vandermonde`) produces ground streams
`a b : ℕ → F` with `αGenuine t = lift (C (a t) + Z·C (b t))`; injectivity of the
`𝒪 ↪ 𝕃` embedding pins the `𝒪`-preimages `aPre t = groundAffine (a t) (b t)`, so the
per-place reading (`π_z_groundAffine`) gives `π_z (aPre t) = a t + z·b t` — combined with
the decoded Taylor reading (`pi_z_aPre_eq_taylor_coeff`), **every matching place decodes to
the SAME affine family**:

`((taylor (C x₀) w).coeff t).eval z = a t + z·b t` for all `t` and all matching `z`.

This is the verbatim affine capture: the decoded surface slices are `v₀ + z·v₁` for the
fixed pair `v₀ = ∑ a t·(X−x₀)^t`, `v₁ = ∑ b t·(X−x₀)^t` — the input shape of the
`Hab25AffineCapture`/dichotomy `hImprove` machinery.

## Main results

* `aPre_eq_groundAffine_of_paperZ_linear` — the `𝒪`-preimage pinning.
* `taylor_coeff_eq_affine_of_heavy` — **the per-place affine decoding**: at every matching
  place, every Taylor coefficient of the decoded slice is `a t + z·b t`.

## References

* [BCIKS20] ePrint 2020/654 — §5.2.7 (Step 7 / Claim 5.9 output).
* [Hab25] ePrint 2025/2110 — Claim 1.
-/

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open BCIKS20.Claim59Lagrange
open BCIKS20.Claim510Kill BCIKS20.Claim510Supply BCIKS20.Claim510Agreement
open BCIKS20.ZLinearClosureAudit
open ProximityPrize.BCIKS20.GammaGenuine

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace BCIKS20.Claim510AffinePair

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable {x₀ : F} {R : F[X][X][Y]}

/-- **The `𝒪`-preimage pinning.**  If `αGenuine t` is on the ground-affine line (the
Claim 5.9 output), the `𝒪`-preimage `aPre t` IS the ground-affine element — by injectivity
of the `𝒪 ↪ 𝕃` embedding through the monic lift identity. -/
theorem aPre_eq_groundAffine_of_paperZ_linear
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    {a b : ℕ → F}
    (hlin : ∀ t, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H)
          (Polynomial.C (a t) + Polynomial.X * Polynomial.C (b t)))
    (t : ℕ) :
    aPre H x₀ R hHyp hlc t = groundAffine H (a t) (b t) := by
  have hH : 0 < H.natDegree := Fact.out
  refine embeddingOf𝒪Into𝕃_injective hH ?_
  -- embed both sides against `ξ̂^{2t−1}` through the lift identity
  have hlift := Claim510Weld.liftIdentity_of_monic H x₀ R hHyp hlc t
  rw [S5Genuine.LiftIdentityAt] at hlift
  have hO : embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = embeddingOf𝒪Into𝕃 H (aPre H x₀ R hHyp hlc t)
        * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) := by
    conv_lhs => rw [betaHensel_eq_aPre_mul_xi_pow H x₀ R hHyp hlc t]
    rw [map_mul, map_pow]
  rw [hO, hlc, map_one, one_pow, mul_one] at hlift
  have hξ : (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) ≠ 0 :=
    pow_ne_zero _ (embeddingOf𝒪Into𝕃_ξ_ne_zero H x₀ R hHyp)
  have heq : embeddingOf𝒪Into𝕃 H (aPre H x₀ R hHyp hlc t)
      = αGenuine H x₀ R hHyp t := mul_right_cancel₀ hξ hlift
  rw [heq, hlin t, embed_groundAffine]

/-- **The per-place affine decoding** ([BCIKS20] Step 7's output, verbatim): on a heavy
monic branch, EVERY matching place decodes to the SAME affine family — every Taylor
coefficient of the decoded slice reads `a t + z·b t`. -/
theorem taylor_coeff_eq_affine_of_heavy
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {a b : ℕ → F}
    (hlin : ∀ t, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H)
          (Polynomial.C (a t) + Polynomial.X * Polynomial.C (b t)))
    {w : F[X][Y]}
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hR : R.Separable)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (t : ℕ) :
    ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).eval z = a t + z * b t := by
  rw [← pi_z_aPre_eq_taylor_coeff hHyp hξ hlc z root hx hdvd hbase hR t,
    aPre_eq_groundAffine_of_paperZ_linear hHyp hlc hlin t, π_z_groundAffine]

end BCIKS20.Claim510AffinePair

/-! ## Axiom audit -/
#print axioms BCIKS20.Claim510AffinePair.aPre_eq_groundAffine_of_paperZ_linear
#print axioms BCIKS20.Claim510AffinePair.taylor_coeff_eq_affine_of_heavy
