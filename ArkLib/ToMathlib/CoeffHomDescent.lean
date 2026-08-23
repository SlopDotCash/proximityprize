/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.LocalizationEmbedding
import ArkLib.ToMathlib.EmbeddingCoefficientCommutation
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.GammaGenuine

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries

namespace ArkLib

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The localization-valued coefficient lift `F[X] →+* Localization.Away ξ`
(constant-embed into `𝒪 H`, then localize). -/
noncomputable def locLift {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    F[X] →+* Localization.Away (ξ x₀ R H hHyp) :=
  (algebraMap (𝒪 H) (Localization.Away (ξ x₀ R H hHyp))).comp
    ((Ideal.Quotient.mk (Ideal.span {H_tilde' H})).comp (Polynomial.C : F[X] →+* F[X][Y]))

/-- **The localization-valued `coeffHom`** — the canonical `Localization.Away ξ`-preimage of
`GammaGenuine.coeffHom` (step-(4) descent object): Taylor-recenter, lift coefficients via
`locLift`, read as a power series. -/
noncomputable def coeffHom_loc (x₀ : F) {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    F[X][Y] →+* (Localization.Away (ξ x₀ R H hHyp))⟦X⟧ :=
  (Polynomial.coeToPowerSeries.ringHom).comp <|
    (Polynomial.mapRingHom (locLift hHyp)).comp
      (Polynomial.taylorAlgHom (Polynomial.C x₀)).toRingHom

/-- Coefficient formula for `coeffHom_loc` (mirror of `coeff_coeffHom`). -/
theorem coeff_coeffHom_loc (x₀ : F) {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (p : F[X][Y]) (n : ℕ) :
    PowerSeries.coeff n (coeffHom_loc x₀ hHyp p) =
      locLift hHyp ((Polynomial.taylor (Polynomial.C x₀) p).coeff n) := by
  rw [coeffHom_loc]
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Polynomial.taylorAlgHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeff_coe, Polynomial.coe_mapRingHom, Polynomial.coeff_map]

/-- **The descent commutation square (step 4 core):** mapping the localization-valued
coefficient hom along `embLoc` recovers the `𝕃`-valued `coeffHom`. Coefficient-wise via
`embLoc_comp` + `emb_mk_C`. -/
theorem map_embLoc_coeffHom_loc (x₀ : F) {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (p : F[X][Y]) :
    PowerSeries.map (embLoc hHyp hξ) (coeffHom_loc x₀ hHyp p)
      = ProximityPrize.BCIKS20.GammaGenuine.coeffHom x₀ H p := by
  ext n
  rw [PowerSeries.coeff_map, coeff_coeffHom_loc, ProximityPrize.BCIKS20.GammaGenuine.coeff_coeffHom]
  unfold locLift
  rw [RingHom.comp_apply, RingHom.comp_apply]
  rw [embLoc_comp]
  exact BCIKS20.HenselNumerator.emb_mk_C _

end ArkLib

#print axioms ArkLib.coeffHom_loc
#print axioms ArkLib.coeff_coeffHom_loc
#print axioms ArkLib.map_embLoc_coeffHom_loc
