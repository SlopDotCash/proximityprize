/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.MpFinFromLocalSeries
import ArkLib.ToMathlib.BetaToCurveCoeffPolys

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries

namespace ArkLib

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- A power series with vanishing tail IS (the coercion of) its truncation. -/
theorem powerSeries_eq_coe_trunc_of_tail_zero {s : PowerSeries F} {n : ℕ}
    (h : ∀ t, n ≤ t → PowerSeries.coeff t s = 0) :
    s = ((PowerSeries.trunc n s : Polynomial F) : PowerSeries F) := by
  ext t
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with ht
  · rfl
  · exact h t (le_of_not_gt ht)

/-- **`localSeries` coefficients vanish where `αFromBeta` vanishes** — `αFromBeta t = 0` forces
`βHensel t = 0` (the embedding is injective and the denominator is nonzero), hence the
`π_z`-reading vanishes. -/
theorem coeff_localSeries_eq_zero_of_alphaFromBeta_eq_zero {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) (t : ℕ)
    (hα : BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0) :
    PowerSeries.coeff t (localSeries hHyp z root hx) = 0 := by
  -- α = emb(betaRec)/(W^{t+1}·emb ξ^{e_t}) = 0 with nonzero denominator ⟹ emb(betaRec) = 0
  have hβ0 : betaRec x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0 := by
    unfold BetaToCurveCoeffPolys.αFromBeta at hα
    rw [div_eq_zero_iff] at hα
    rcases hα with hnum | hden
    · exact embeddingOf𝒪Into𝕃_injective (Fact.out) (by rw [hnum, map_zero])
    · exfalso
      have hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
        liftToFunctionField_leadingCoeff_ne_zero (H := H)
      have hξL : embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) ≠ 0 := emb_ξ_ne_zero hHyp hξ
      exact (mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ hξL)) hden
  -- transfer to βHensel and conclude via the read-off
  have hβH : BCIKS20.HenselNumerator.βHensel H x₀ R hHyp t = 0 := by
    rw [← BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel]
    exact hβ0
  have hread := coeff_localSeries_mul hHyp z root hx t
  rw [hβH, map_zero] at hread
  exact (mul_eq_zero.mp hread).resolve_right (pow_ne_zero _ hx)

/-- **The `hQroot`-class root fact for the truncation:** when `αFromBeta` vanishes from `n` on,
`localSeries` IS its degree-`< n` truncation, so the truncation (the decoded polynomial) is a
root of the specialized matching polynomial. -/
theorem trunc_localSeries_isRoot_of_alphaFromBeta_vanishing {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {n : ℕ}
    (hvanish : ∀ t, n ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0) :
    ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z root hx))).IsRoot
      ((PowerSeries.trunc n (localSeries hHyp z root hx) : Polynomial F) : PowerSeries F) := by
  have heq : localSeries hHyp z root hx
      = ((PowerSeries.trunc n (localSeries hHyp z root hx) : Polynomial F) : PowerSeries F) :=
    powerSeries_eq_coe_trunc_of_tail_zero (fun t ht =>
      coeff_localSeries_eq_zero_of_alphaFromBeta_eq_zero hHyp hξ z root hx t (hvanish t ht))
  rw [← heq]
  exact localSeries_isRoot_of_monic hHyp hξ hlc z root hx

end ArkLib

#print axioms ArkLib.powerSeries_eq_coe_trunc_of_tail_zero
#print axioms ArkLib.coeff_localSeries_eq_zero_of_alphaFromBeta_eq_zero
#print axioms ArkLib.trunc_localSeries_isRoot_of_alphaFromBeta_vanishing
