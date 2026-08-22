/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.LocalSeriesBaseRationalReading
import ArkLib.ToMathlib.CurveFamilyZLinear

/-!
# Issue #304 — the per-place reading at `T`-affine (Claim 5.9) orders

`LocalSeriesBaseRationalReading` derived the per-place coefficient reading at *base-rational*
orders (`αGenuine t = lift cₜ`).  But base-rationality fails at order 0 whenever `d_H ≥ 2`
(`α₀ = T/W` has `T`-content), and the honest Claim-5.9 shape — proven **unconditionally for
`d_H ≤ 2`** in `ZLinearRatFuncDegreeOne`, and the windowed residual shape for `d_H ≥ 3` — is the
**`T`-affine** per-coefficient form `αGenuine t = lift c₀ᵗ + T · lift c₁ᵗ`.

This file generalizes the whole reading chain to that shape:

* `βHensel_eq_mk_T_affine_mul_ξ_pow_of_zLinear` — the `𝒪`-descent: at a `T`-affine order the
  `(A.1)` numerator factors as `βHensel t = mk (C c₀ᵗ + C c₁ᵗ · T) · ξ^{2t−1}` (monic case;
  the embedding is injective and the lift identity supplies the `𝕃`-side).
* `π_z_T_affine` / `π_z_βHensel_of_zLinear` — the place reading: `π_z ∘ mk` of a `T`-affine
  representative is `c₀(z) + t_z · c₁(z)` — the polynomial readings **at the branch value**
  `t_z = root.1`.
* `coeff_localSeries_of_zLinear` — the local-series coefficient at a `T`-affine order is
  `c₀ᵗ(z) + t_z · c₁ᵗ(z)`.
* `trunc_localSeries_of_zLinear` — the truncated local series is the **two-family curve
  reading**: `trunc N (localSeries z) = (∑_{t<n} C (c₀ᵗ(z))·Xᵗ) + t_z • (∑_{t<n} C (c₁ᵗ(z))·Xᵗ)`
  — exactly the `CurveFamilyZLinear.CurvePlaceReading` payload shape, with the branch value as
  the reading of `T`.

With these, the `d_H ≤ 2` regime needs **no residual at all** on the reading front (the
`T`-affine form is unconditional there), and for `d_H ≥ 3` the reading front is closed to the
windowed Claim-5.9 residual.  The remaining step to `CurveFamilyData` is branch rationality
(`hbranch` of `curveFamilyData_of_placeReading`) — the honest `R3` residual.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Claim 5.9), Appendix A.3–A.4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityGap Code NNReal Finset Function
open ProximityPrize.BCIKS20.GammaGenuine BCIKS20.HenselNumerator
open scoped BigOperators ENNReal

namespace ArkLib

namespace TAffineReading

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## Part 1 — the `𝒪`-descent at a `T`-affine order -/

/-- The embedding of a `T`-affine `𝒪`-class is the `T`-affine combination of the lifts. -/
theorem emb_mk_T_affine (c₀ c₁ : F[X]) :
    embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        (Polynomial.C c₀ + Polynomial.C c₁ * Polynomial.X))
      = liftToFunctionField (H := H) c₀
        + liftToFunctionField (H := H) c₁ * functionFieldT (H := H) := by
  rw [embeddingOf𝒪Into𝕃_mk, map_add, map_mul, liftBivariate_X]
  rfl

/-- **`𝒪`-descent of the `T`-affine (Claim 5.9) form (monic).**  If
`αGenuine t = lift c₀ + T · lift c₁`, then the `(A.1)` numerator factors in `𝒪 H` as
`βHensel t = mk (C c₀ + C c₁ · T) · ξ^{2t−1}`. -/
theorem βHensel_eq_mk_T_affine_mul_ξ_pow_of_zLinear {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) {t : ℕ} {c₀ c₁ : F[X]}
    (hzl : αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H) c₀
        + liftToFunctionField (H := H) c₁ * functionFieldT (H := H)) :
    βHensel H x₀ R hHyp t
      = Ideal.Quotient.mk (Ideal.span {H_tilde' H})
          (Polynomial.C c₀ + Polynomial.C c₁ * Polynomial.X)
          * (ξ x₀ R H hHyp) ^ (2 * t - 1) := by
  apply embeddingOf𝒪Into𝕃_injective (Fact.out)
  rw [map_mul, map_pow, emb_mk_T_affine,
    βHensel_lift_identity_of_monic H x₀ R hHyp hlc t, hzl, hlc, map_one, one_pow, mul_one]

/-! ## Part 2 — the place reading -/

/-- The place reading of a `T`-affine class is the polynomial readings at the branch value:
`π_z (mk (C c₀ + C c₁ · T)) = c₀(z) + c₁(z) · t_z`. -/
theorem π_z_T_affine (z : F) (root : rationalRoot (H_tilde' H) z) (c₀ c₁ : F[X]) :
    (π_z z root) (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        (Polynomial.C c₀ + Polynomial.C c₁ * Polynomial.X))
      = c₀.eval z + c₁.eval z * root.1 := by
  rw [π_z_mk, Polynomial.evalEval_add, Polynomial.evalEval_mul, Polynomial.evalEval_C,
    Polynomial.evalEval_C, Polynomial.evalEval_X]

/-- **The place reading of the `(A.1)` numerator at a `T`-affine order:**
`π_z (βHensel t) = (c₀(z) + c₁(z)·t_z) · π_z(ξ)^{2t−1}`. -/
theorem π_z_βHensel_of_zLinear {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z) {t : ℕ} {c₀ c₁ : F[X]}
    (hzl : αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H) c₀
        + liftToFunctionField (H := H) c₁ * functionFieldT (H := H)) :
    (π_z z root) (βHensel H x₀ R hHyp t)
      = (c₀.eval z + c₁.eval z * root.1) * ((π_z z root) (ξ x₀ R H hHyp)) ^ (2 * t - 1) := by
  rw [βHensel_eq_mk_T_affine_mul_ξ_pow_of_zLinear hHyp hlc hzl, map_mul, map_pow, π_z_T_affine]

/-- **The local-series coefficient at a `T`-affine order:**
`coeff t (localSeries z) = c₀ᵗ(z) + c₁ᵗ(z) · t_z`. -/
theorem coeff_localSeries_of_zLinear {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {t : ℕ} {c₀ c₁ : F[X]}
    (hzl : αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H) c₀
        + liftToFunctionField (H := H) c₁ * functionFieldT (H := H)) :
    PowerSeries.coeff t (localSeries hHyp z root hx)
      = c₀.eval z + c₁.eval z * root.1 := by
  have h := coeff_localSeries_mul hHyp z root hx t
  rw [π_z_βHensel_of_zLinear hHyp hlc z root hzl] at h
  exact mul_right_cancel₀ (pow_ne_zero _ hx) h

/-! ## Part 3 — the truncated two-family curve reading -/

/-- **The truncated local series at `T`-affine orders is the two-family curve reading**:
`trunc N (localSeries z) = (∑_{t<n} C (c₀ᵗ(z))·Xᵗ) + t_z • (∑_{t<n} C (c₁ᵗ(z))·Xᵗ)` —
the `CurvePlaceReading` payload shape, with the tail `[n, N)` vanishing. -/
theorem trunc_localSeries_of_zLinear {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {n N : ℕ} (hnN : n ≤ N)
    {c₀ c₁ : ℕ → F[X]}
    (hzl : ∀ t < n, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H) (c₀ t)
        + liftToFunctionField (H := H) (c₁ t) * functionFieldT (H := H))
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0) :
    (PowerSeries.trunc N (localSeries hHyp z root hx) : Polynomial F)
      = (∑ t ∈ Finset.range n, Polynomial.C ((c₀ t).eval z) * Polynomial.X ^ t)
        + root.1 • (∑ t ∈ Finset.range n, Polynomial.C ((c₁ t).eval z) * Polynomial.X ^ t) := by
  ext j
  rw [PowerSeries.coeff_trunc, Polynomial.coeff_add, Polynomial.coeff_smul,
    coeff_sum_C_mul_X_pow, coeff_sum_C_mul_X_pow]
  split_ifs with hj hjn hjn
  · -- j < N, j < n: the T-affine reading
    rw [coeff_localSeries_of_zLinear hHyp hlc z root hx (hzl j hjn), smul_eq_mul]
    ring
  · -- j < N, n ≤ j: the tail
    rw [smul_zero, add_zero]
    have hξ : ξ x₀ R H hHyp ≠ 0 := fun h0 => hx (by rw [h0, map_zero])
    refine coeff_localSeries_eq_zero_of_alphaFromBeta_eq_zero hHyp hξ z root hx j ?_
    rw [BetaRecGenuineBridge.alphaFromBeta_BcoeffSigned_eq_αGenuine_of_monic x₀ R hHyp hlc j]
    exact htail j (le_of_not_gt hjn)
  · -- N ≤ j < n: impossible
    omega
  · -- N ≤ j, n ≤ j
    rw [smul_zero, add_zero]

end TAffineReading

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.TAffineReading.emb_mk_T_affine
#print axioms ArkLib.TAffineReading.βHensel_eq_mk_T_affine_mul_ξ_pow_of_zLinear
#print axioms ArkLib.TAffineReading.π_z_T_affine
#print axioms ArkLib.TAffineReading.π_z_βHensel_of_zLinear
#print axioms ArkLib.TAffineReading.coeff_localSeries_of_zLinear
#print axioms ArkLib.TAffineReading.trunc_localSeries_of_zLinear
