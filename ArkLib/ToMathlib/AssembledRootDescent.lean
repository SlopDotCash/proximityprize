/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.CoeffHomDescent
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.MonicFaaDiBrunoMatchAlt

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries

namespace ArkLib

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The localization-valued preimage of the assembled Hensel series (monic case `W = 1`):
coefficients `mk'(βHensel t, ξ^{2t−1})`. -/
noncomputable def assembledLoc {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    PowerSeries (Localization.Away (ξ x₀ R H hHyp)) :=
  PowerSeries.mk fun t =>
    IsLocalization.mk' _ (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp t)
      (⟨(ξ x₀ R H hHyp) ^ (2 * t - 1), 2 * t - 1, rfl⟩ :
        Submonoid.powers (ξ x₀ R H hHyp))

/-- `embLoc` maps the localization preimage onto the assembled `𝕃`-series (monic `W = 1`). -/
theorem map_embLoc_assembledLoc {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1) :
    PowerSeries.map (embLoc hHyp hξ) (assembledLoc hHyp)
      = BCIKS20.HenselNumerator.βHenselAssembled H x₀ R hHyp := by
  ext t
  rw [PowerSeries.coeff_map]
  unfold assembledLoc BCIKS20.HenselNumerator.βHenselAssembled
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  unfold embLoc Localization.awayLift IsLocalization.Away.lift
  rw [IsLocalization.lift_mk'_spec]
  rw [hlc, map_one, one_pow, one_mul, map_pow]
  have hξL : embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) ≠ 0 := emb_ξ_ne_zero hHyp hξ
  field_simp

/-- **The descended monic root (step-4 assembly):** the localization preimage of the assembled
series is a root of the localization preimage of `Q`. Descends the proven 𝕃-root through the
injective `embLoc` using the commutation square. -/
theorem assembledLoc_isRoot_of_monic {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1) :
    Polynomial.eval (assembledLoc hHyp) (R.map (coeffHom_loc x₀ hHyp)) = 0 := by
  apply PowerSeries.map_injective (embLoc hHyp hξ) (embLoc_injective hHyp hξ)
  rw [map_zero]
  have hsquare : (PowerSeries.map (embLoc hHyp hξ)).comp (coeffHom_loc x₀ hHyp)
      = ProximityPrize.BCIKS20.GammaGenuine.coeffHom x₀ H :=
    RingHom.ext (map_embLoc_coeffHom_loc x₀ hHyp hξ)
  calc (PowerSeries.map (embLoc hHyp hξ))
        (Polynomial.eval (assembledLoc hHyp) (R.map (coeffHom_loc x₀ hHyp)))
      = (PowerSeries.map (embLoc hHyp hξ))
          (Polynomial.eval₂ (coeffHom_loc x₀ hHyp) (assembledLoc hHyp) R) := by
        rw [Polynomial.eval_map]
    _ = Polynomial.eval₂
          ((PowerSeries.map (embLoc hHyp hξ)).comp (coeffHom_loc x₀ hHyp))
          (PowerSeries.map (embLoc hHyp hξ) (assembledLoc hHyp)) R := by
        rw [Polynomial.hom_eval₂]
    _ = Polynomial.eval₂ (ProximityPrize.BCIKS20.GammaGenuine.coeffHom x₀ H)
          (BCIKS20.HenselNumerator.βHenselAssembled H x₀ R hHyp) R := by
        rw [hsquare, map_embLoc_assembledLoc hHyp hξ hlc]
    _ = Polynomial.eval (BCIKS20.HenselNumerator.βHenselAssembled H x₀ R hHyp)
          (R.map (ProximityPrize.BCIKS20.GammaGenuine.coeffHom x₀ H)) := by
        rw [Polynomial.eval_map]
    _ = 0 := BCIKS20.HenselNumerator.assembledSeries_isRoot_of_monic (H := H) x₀ R hHyp hlc

end ArkLib

#print axioms ArkLib.map_embLoc_assembledLoc
#print axioms ArkLib.assembledLoc_isRoot_of_monic
