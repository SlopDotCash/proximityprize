/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.HenselSeriesCoeff
import ArkLib.Data.Polynomial.RationalFunctions

/-!
# The genuine Hensel-lifted root `γ` of [BCIKS20] App. A.4 (the P2 instantiation)

`RationalFunctions.lean` defines `ClaimA2.γ` as
`PowerSeries.subst (mk subst) (mk α)` where the substituted series is `C (-x₀) + X` and the
coefficient series `α` is built on the *vacuous* numerator `β = 0` (see the honesty notes at
`β_regular` and in `GammaSubstObstruction.lean`). That `γ` is therefore **not** the genuine
Hensel-lift root: it is degenerate for `x₀ ≠ 0` (the substitution fails `HasSubst`) and carries no
functional relation to `R`.

This file produces the **genuine** object directly, from first principles, via the
application-shaped Hensel theorem `HenselSeriesCoeff.exists_powerSeries_root_seriesCoeff`. The
mathematical content is exactly the frontier the placeholder `βHensel_lift_identity` was meant to
fill: a power series `γ : (𝕃 H)⟦X⟧` (the local variable `X` is the recentered `X' = X − x₀`) with

* `constantCoeff γ = α₀ := T / W` (the base root of `H` in `𝕃 H`), and
* `Polynomial.eval γ Q = 0`, i.e. the genuine relation `R(X, γ, Z) = 0` in `(𝕃 H)⟦X⟧`.

## The construction (the X-recentered Y-polynomial of `R`)

`R : F[X][X][Y] = Polynomial (Polynomial (Polynomial F))` has, from outer to inner, the layers
`Y` (the algebraic variable we solve for), `X` (the lift / local variable, specialized at `x₀` to
read off the order-0 data), and `Z` (the function-field variable, mapped into `𝕃 H` by
`liftToFunctionField`). The Y-coefficient `R.coeff i : F[X][Y]` is bivariate in `(X, Z)`.

For each `i` we build the `i`-th coefficient series of `Q` by

1. **recentering the `X`-layer** at `x₀`: `Polynomial.taylor (C x₀) (R.coeff i)` (a `HasSubst`-free
   polynomial Taylor shift — exactly the faithful fix of `GammaSubstObstruction.lean`), then
2. **lifting the `Z`-coefficients** into `𝕃 H` via `Polynomial.map liftToFunctionField`, treating
   the recentered `X` as the *power-series variable* via `Polynomial.coeToPowerSeries.ringHom`.

The composite is the ring hom `coeffHom x₀ : F[X][Y] →+* (𝕃 H)⟦X⟧`, and
`Q := R.map (coeffHom x₀) : Polynomial ((𝕃 H)⟦X⟧)`. Because each step is a `RingHom`, `Q` is the
genuine Y-polynomial with power-series coefficients required by the Hensel theorem.

## The order-0 data

The order-0 reduction `Q₀ = Q.map constantCoeff` is `(Bivariate.evalX (C x₀) R).map
liftToFunctionField`, because `constantCoeff` reads the `X = x₀` constant term (Taylor coeff 0 =
evaluation at `x₀`). Hence:

* `eval α₀ Q₀ = eval₂ liftToFunctionField α₀ (evalX (C x₀) R) = 0`, from `Hypotheses.dvd_evalX`
  (`H ∣ evalX (C x₀) R`) and the base-root lemma
  `eval₂_liftToFunctionField_div_leadingCoeff_H_eq_zero` (`H(α₀) = 0`); and
* `IsUnit (eval α₀ (derivative Q₀))`, because `eval α₀ (derivative Q₀) = ζ R x₀ H ≠ 0` by
  `Separable.eval₂_derivative_ne_zero` applied to `Hypotheses.separable_evalX`, and a nonzero
  element of the field `𝕃 H` is a unit.

Feeding this simple root `α₀` to the Hensel theorem yields `gammaGenuine` with the two advertised
properties, and (stretch) a uniqueness statement among roots sharing `α₀`.
-/

namespace ProximityPrize.BCIKS20.GammaGenuine

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

variable {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]

/-! ## The base root `α₀ = T / W` and its naming -/

/-- The base root `α₀ = T / W ∈ 𝕃 H` of `H`: the image of the polynomial variable `T`,
divided by the (lifted) leading coefficient `W` of `H`. This is the order-0 datum that the
Hensel lift extends to a power series in the local variable `X`. -/
noncomputable def α₀ (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)] : 𝕃 H :=
  functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff

/-- `H` vanishes at `α₀` in the function field (the base root). -/
theorem eval₂_H_α₀ : Polynomial.eval₂ liftToFunctionField (α₀ H) H = 0 :=
  eval₂_liftToFunctionField_div_leadingCoeff_H_eq_zero (H := H)

/-! ## The X-recentered coefficient ring hom and the genuine `Q` -/

/-- The per-`Y`-coefficient ring hom `F[X][Y] → (𝕃 H)⟦X⟧`: recenter the `X`-layer at `x₀`
(`taylorAlgHom (C x₀)`), lift the `Z`-coefficients into `𝕃 H` (`map liftToFunctionField`), and
read the recentered `X` as the power-series variable (`coeToPowerSeries.ringHom`). -/
noncomputable def coeffHom (x₀ : F) (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)] :
    F[X][Y] →+* (𝕃 H)⟦X⟧ :=
  (Polynomial.coeToPowerSeries.ringHom).comp <|
    (Polynomial.mapRingHom (liftToFunctionField (H := H))).comp
      (Polynomial.taylorAlgHom (Polynomial.C x₀)).toRingHom

/-- The genuine `X`-recentered `Y`-polynomial of `R`, with power-series coefficients in the local
variable `X = X' = X − x₀`. -/
noncomputable def Q (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] : Polynomial ((𝕃 H)⟦X⟧) :=
  R.map (coeffHom x₀ H)

/-- The `i`-th coefficient of `coeffHom x₀ H p`, read at order `n`, is the lift of the `n`-th
`X`-Taylor coefficient (a `Z`-polynomial) of `p`. -/
theorem coeff_coeffHom (x₀ : F) (p : F[X][Y]) (n : ℕ) :
    PowerSeries.coeff n (coeffHom x₀ H p) =
      liftToFunctionField (H := H) ((Polynomial.taylor (Polynomial.C x₀) p).coeff n) := by
  rw [coeffHom]
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Polynomial.taylorAlgHom_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe,
    Polynomial.coe_mapRingHom, Polynomial.coeff_map]

/-- The constant coefficient of `coeffHom x₀ H p` is the lift of `p` evaluated at `X = x₀`. -/
theorem constantCoeff_coeffHom (x₀ : F) (p : F[X][Y]) :
    PowerSeries.constantCoeff (coeffHom x₀ H p) =
      liftToFunctionField (H := H) (p.eval (Polynomial.C x₀)) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coeffHom,
    Polynomial.taylor_coeff_zero]

/-! ## The order-0 reduction `Q₀ = (evalX (C x₀) R) lifted` -/

/-- `Q₀ := Q.map constantCoeff` is the lift of the `X`-specialization `R(x₀, Y, Z)`. -/
theorem Q₀_eq (x₀ : F) (R : F[X][X][Y]) :
    ProximityPrize.HenselSeriesCoeff.Q₀ (Q x₀ R H) =
      (Bivariate.evalX (Polynomial.C x₀) R).map (liftToFunctionField (H := H)) := by
  ext i
  rw [ProximityPrize.HenselSeriesCoeff.coeff_Q₀, Q, Polynomial.coeff_map,
    constantCoeff_coeffHom, Polynomial.coeff_map, Bivariate.evalX_eq_map,
    Polynomial.coeff_map, Polynomial.coe_evalRingHom]

/-- Evaluating the order-0 reduction `Q₀` at `α₀` is `eval₂ liftToFunctionField α₀` of the
`X`-specialization `R(x₀, Y, Z)`. -/
theorem eval_α₀_Q₀ (x₀ : F) (R : F[X][X][Y]) :
    Polynomial.eval (α₀ H) (ProximityPrize.HenselSeriesCoeff.Q₀ (Q x₀ R H)) =
      Polynomial.eval₂ (liftToFunctionField (H := H)) (α₀ H)
        (Bivariate.evalX (Polynomial.C x₀) R) := by
  rw [Q₀_eq, Polynomial.eval_map]

/-- The derivative of the order-0 reduction `Q₀`, evaluated at `α₀`, is exactly `ζ R x₀ H`. -/
theorem eval_α₀_derivative_Q₀ (x₀ : F) (R : F[X][X][Y]) :
    Polynomial.eval (α₀ H) (Polynomial.derivative (ProximityPrize.HenselSeriesCoeff.Q₀ (Q x₀ R H)))
      = ζ R x₀ H := by
  rw [Q₀_eq, Polynomial.derivative_map, Polynomial.eval_map, ζ, evalX_derivative_comm, α₀]

/-! ## The order-0 root data: `α₀` is a simple root of `Q₀` -/

/-- **Order-0 vanishing.** `α₀` is a root of `Q₀`. From `H ∣ evalX (C x₀) R`
(`Hypotheses.dvd_evalX`) and `H(α₀) = 0` (the base-root lemma): writing
`evalX (C x₀) R = H * g`, the product `eval₂ α₀ (H * g) = (eval₂ α₀ H) * (eval₂ α₀ g) = 0`. -/
theorem eval_α₀_Q₀_eq_zero {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    Polynomial.eval (α₀ H) (ProximityPrize.HenselSeriesCoeff.Q₀ (Q x₀ R H)) = 0 := by
  rw [eval_α₀_Q₀]
  obtain ⟨g, hg⟩ := hHyp.dvd_evalX
  rw [hg, Polynomial.eval₂_mul, eval₂_H_α₀, zero_mul]

/-- **Order-0 simplicity.** `eval α₀ (derivative Q₀) = ζ R x₀ H ≠ 0`, hence is a unit in the
field `𝕃 H`. Nonvanishing is `Separable.eval₂_derivative_ne_zero` applied to
`Hypotheses.separable_evalX` at the root `α₀` of `evalX (C x₀) R`. -/
theorem isUnit_eval_α₀_derivative_Q₀ {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    IsUnit (Polynomial.eval (α₀ H)
      (Polynomial.derivative (ProximityPrize.HenselSeriesCoeff.Q₀ (Q x₀ R H)))) := by
  rw [isUnit_iff_ne_zero]
  -- `eval α₀ (derivative Q₀) = eval₂ α₀ (derivative (evalX (C x₀) R))`.
  rw [Q₀_eq, Polynomial.derivative_map, Polynomial.eval_map]
  -- The base root: `eval₂ α₀ (evalX (C x₀) R) = 0`, since `H ∣ evalX (C x₀) R` and `H(α₀) = 0`.
  have hroot : Polynomial.eval₂ (liftToFunctionField (H := H)) (α₀ H)
      (Bivariate.evalX (Polynomial.C x₀) R) = 0 := by
    obtain ⟨g, hg⟩ := hHyp.dvd_evalX
    rw [hg, Polynomial.eval₂_mul, eval₂_H_α₀, zero_mul]
  exact hHyp.separable_evalX.eval₂_derivative_ne_zero (liftToFunctionField (H := H)) hroot

/-! ## MAIN: the genuine Hensel-lifted root `γ` -/

/-- **The genuine Hensel-lifted root.** `gammaGenuine x₀ R H hHyp : (𝕃 H)⟦X⟧` is the power series
in the local variable `X = X − x₀` obtained by Hensel-lifting the simple root `α₀` of the
`X`-specialization `R(x₀, Y, Z)`. This is the genuine object of [BCIKS20] App. A.4, replacing the
degenerate `ClaimA2.γ` built on the `β = 0` placeholder. -/
noncomputable def gammaGenuine (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) : (𝕃 H)⟦X⟧ :=
  (ProximityPrize.HenselSeriesCoeff.exists_powerSeries_root_seriesCoeff
    (eval_α₀_Q₀_eq_zero hHyp) (isUnit_eval_α₀_derivative_Q₀ hHyp)).choose

/-- The genuine root lifts `α₀`: its constant coefficient (`X = x₀`) is `α₀`. -/
theorem gammaGenuine_constantCoeff {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    PowerSeries.constantCoeff (gammaGenuine x₀ R H hHyp) = α₀ H :=
  (ProximityPrize.HenselSeriesCoeff.exists_powerSeries_root_seriesCoeff
    (eval_α₀_Q₀_eq_zero hHyp) (isUnit_eval_α₀_derivative_Q₀ hHyp)).choose_spec.1

/-- **The genuine relation `R(X, γ, Z) = 0`.** `gammaGenuine` is a genuine root of the
`X`-recentered `Y`-polynomial `Q`. -/
theorem gammaGenuine_root {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    Polynomial.eval (gammaGenuine x₀ R H hHyp) (Q x₀ R H) = 0 :=
  (ProximityPrize.HenselSeriesCoeff.exists_powerSeries_root_seriesCoeff
    (eval_α₀_Q₀_eq_zero hHyp) (isUnit_eval_α₀_derivative_Q₀ hHyp)).choose_spec.2

/-! ## Coefficient-level consumers -/

/-- Every coefficient of the genuine root equation vanishes. This is the coefficient-level
form downstream Appendix-A arguments need when proving identities order by order. -/
theorem coeff_gammaGenuine_root {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) (t : ℕ) :
    PowerSeries.coeff t (Polynomial.eval (gammaGenuine x₀ R H hHyp) (Q x₀ R H)) = 0 := by
  rw [gammaGenuine_root hHyp]
  simp

/-! ## Uniqueness among roots sharing `α₀` -/

/-- **Uniqueness.** Any root `γ'` of `Q` whose constant coefficient is `α₀` equals
`gammaGenuine`. This is `HenselSeriesCoeff.root_unique_seriesCoeff` specialized to the simple
root `α₀` of `Q₀`. -/
theorem gammaGenuine_unique {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    {γ' : (𝕃 H)⟦X⟧} (hc : PowerSeries.constantCoeff γ' = α₀ H)
    (hroot : Polynomial.eval γ' (Q x₀ R H) = 0) :
    γ' = gammaGenuine x₀ R H hHyp := by
  refine ProximityPrize.HenselSeriesCoeff.root_unique_seriesCoeff (Q := Q x₀ R H) ?_ ?_ hroot
    (gammaGenuine_root hHyp)
  · rw [hc, gammaGenuine_constantCoeff hHyp]
  · rw [hc]; exact isUnit_eval_α₀_derivative_Q₀ hHyp

/-- Any other root with the same order-0 datum has the same coefficients as `gammaGenuine`. -/
theorem coeff_eq_gammaGenuine_of_root {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    {γ' : (𝕃 H)⟦X⟧} (hc : PowerSeries.constantCoeff γ' = α₀ H)
    (hroot : Polynomial.eval γ' (Q x₀ R H) = 0) (t : ℕ) :
    PowerSeries.coeff t γ' = PowerSeries.coeff t (gammaGenuine x₀ R H hHyp) := by
  rw [gammaGenuine_unique hHyp hc hroot]

end ProximityPrize.BCIKS20.GammaGenuine
