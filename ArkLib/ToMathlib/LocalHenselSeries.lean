/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.AssembledRootDescent

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries

namespace ArkLib

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The local Hensel-root series at the place `z` (step 5):** the `π̂_z`-image of the
localization preimage of the assembled series — an `F`-power series. -/
noncomputable def localSeries {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) : PowerSeries F :=
  PowerSeries.map (π_hat_z hHyp z root hx) (assembledLoc hHyp)

/-- **The local root fact (step-5 transport):** the local series is a root of the
`π̂_z`-specialized polynomial. Forward ring-hom transport of `assembledLoc_isRoot_of_monic`
(no injectivity needed). -/
theorem localSeries_isRoot_of_monic {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) :
    Polynomial.eval (localSeries hHyp z root hx)
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z root hx))) = 0 := by
  calc Polynomial.eval (localSeries hHyp z root hx)
        ((R.map (coeffHom_loc x₀ hHyp)).map (PowerSeries.map (π_hat_z hHyp z root hx)))
      = Polynomial.eval₂ (PowerSeries.map (π_hat_z hHyp z root hx))
          (localSeries hHyp z root hx) (R.map (coeffHom_loc x₀ hHyp)) := by
        rw [Polynomial.eval_map]
    _ = (PowerSeries.map (π_hat_z hHyp z root hx))
          (Polynomial.eval (assembledLoc hHyp) (R.map (coeffHom_loc x₀ hHyp))) := by
        conv_rhs => rw [← Polynomial.eval₂_id
          (x := assembledLoc hHyp) (p := R.map (coeffHom_loc x₀ hHyp))]
        rw [Polynomial.hom_eval₂, RingHom.comp_id]
        rfl
    _ = 0 := by rw [assembledLoc_isRoot_of_monic hHyp hξ hlc, map_zero]

/-- **The coefficient read-off (step-5 read-off):** the `t`-th coefficient of the local series
satisfies the multiplied-out L12 identity `coeff t · x^{2t−1} = π_z(βHensel t)` — exactly the
`bridgeData_of_mul_form` supplier shape (monic: `w = 1`). -/
theorem coeff_localSeries_mul {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) (t : ℕ) :
    PowerSeries.coeff t (localSeries hHyp z root hx)
        * ((π_z z root) (ξ x₀ R H hHyp)) ^ (2 * t - 1)
      = (π_z z root) (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp t) := by
  -- localization clearing identity, transported by the ring hom π̂_z
  have hms := IsLocalization.mk'_spec (Localization.Away (ξ x₀ R H hHyp))
    (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp t)
    (⟨(ξ x₀ R H hHyp) ^ (2 * t - 1), 2 * t - 1, rfl⟩ :
      Submonoid.powers (ξ x₀ R H hHyp))
  have hπ := congrArg (π_hat_z hHyp z root hx) hms
  rw [map_mul, π_hat_z_comp, π_hat_z_comp,
    show (((⟨(ξ x₀ R H hHyp) ^ (2 * t - 1), 2 * t - 1, rfl⟩ :
        Submonoid.powers (ξ x₀ R H hHyp)) : 𝒪 H)) = (ξ x₀ R H hHyp) ^ (2 * t - 1)
      from rfl,
    map_pow] at hπ
  unfold localSeries assembledLoc
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  exact hπ

end ArkLib

#print axioms ArkLib.localSeries_isRoot_of_monic
#print axioms ArkLib.coeff_localSeries_mul
