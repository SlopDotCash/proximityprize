/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RestrictedFaaDiBrunoExtract
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchRoot
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.WPowerInjective

/-!
# BCIKS20 Appendix A.4 — the order-zero P2 carved core is mis-normalized for non-monic `H`

The carved P2 residual `RestrictedFaaDiBrunoMatch` (the single named combinatorial core of the
(P2) lift identity, tracked by issue #139 ⟺ the #9 P2 half, and asserted by the
`restrictedFaaDiBrunoMatch_residual` axiom) is **not unconditionally true**. This file isolates a
genuine *refutation* of its order-zero component for non-monic `H`.

## The defect

The in-tree reduction chain (all `hHyp.dvd_evalX`-free) proves, under only `2 ≤ R.natDegree`:

via `restrictedMatchAt_zero_iff_eval₂WDivTarget` then the target definition:
```
RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0
  ↔ RestrictedMatchAtZeroEval₂WDivTarget H x₀ R
  ↔ ( eval₂ lift (T/W) p  =  eval₂ lift T p / W ^ R.natDegree )
```
with `p = evalX (C x₀) (Δ_X¹ R)` the order-1 `X`-Taylor coefficient and
`W = liftToFunctionField H.leadingCoeff`.

The recursion-side normalization clears by the **full** `W ^ R.natDegree`, but the order-1 numerator
`p` has actual `Y`-degree `natDegreeY p`, which may be strictly smaller. When `p` is a nonzero
`Y`-**constant** (`natDegreeY p = 0`) the target collapses to `lift c = lift c / W ^ R.natDegree`,
i.e. `W ^ R.natDegree = 1` — **false** for non-monic `H` (`W` is not a root of unity, so
`W ^ R.natDegree ≠ 1` for `R.natDegree ≥ 1`).

## Why this regime is reachable (non-vacuity)

`ClaimA2.Hypotheses x₀ R H` constrains only the **0th** `X`-Taylor coefficient
`g = evalX (C x₀) R` (`dvd_evalX : H ∣ g` and `separable_evalX : g.Separable`). It places **no**
constraint on the order-1 coefficient `p = evalX (C x₀) (Δ_X¹ R)`. Concretely, taking
`R = g(Y) + (X − x₀)·C c + (X − x₀)²·(…)` with `g = H·(Y − a)` separable gives `hHyp`, `p = C c`
constant, and `R.natDegree = natDegreeY g ≥ 2`. Hence the refutation below is *non-vacuous*: there
exist `R` satisfying `ClaimA2.Hypotheses` on which the carved order-zero core fails.

## Consequence

`restrictedFaaDiBrunoMatch_residual` (the allowlisted axiom, issue #169) asserts a proposition that
is **false** for non-monic `H`, so it is unsound, not merely unproven. The fix is to re-normalize
the recursion-side `B_coeff` clearing to the actual numerator `Y`-degree (`natDegreeY p`, via the
proven cleared representative `hasseCoeffRepr𝒪_cleared`) rather than the uniform `R.natDegree`.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20AppendixA.ClaimA2

variable {F : Type} [Field F]

/-- Build the order-zero Claim A.2 hypotheses from an explicit specialized polynomial
`g = R(x₀, -, -)`.  This keeps the constrained zero-th coefficient separate from the independent
order-1 Hasse numerator used by the refutation below. -/
theorem Hypotheses.of_evalX_eq {x₀ : F} {R : F[X][X][Y]} {H g : F[X][Y]}
    (hR0 : Bivariate.evalX (Polynomial.C x₀) R = g)
    (hdvd : H ∣ g)
    (hsep : g.Separable) :
    Hypotheses x₀ R H := by
  exact ⟨by simpa [hR0] using hdvd, by simpa [hR0] using hsep⟩

end BCIKS20AppendixA.ClaimA2

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Refutation of the order-zero P2 `eval₂`/W-divisor target for a `Y`-constant numerator.**
If the order-1 `X`-Taylor coefficient `evalX (C x₀) (Δ_X¹ R)` is a nonzero `Y`-constant `C c`, then
the order-zero target `eval₂(T/W) = eval₂(T) / W ^ R.natDegree` collapses (`eval₂_C`) to
`lift c = lift c / W ^ R.natDegree`, which holds iff `W ^ R.natDegree = 1`. For non-monic `H`
(`W ^ R.natDegree ≠ 1`) it is therefore **false**. This isolates the genuine cleared/un-cleared
normalization defect: the recursion clears by the full `R.natDegree` while the numerator's actual
`Y`-degree here is `0`. -/
theorem eval₂WDivTarget_false_of_constant_of_W_pow_ne_one
    (x₀ : F) (R : F[X][X][Y]) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0)
    (hW : liftToFunctionField (H := H) H.leadingCoeff ^ R.natDegree ≠ 1) :
    ¬ RestrictedMatchAtZeroEval₂WDivTarget H x₀ R := by
  unfold RestrictedMatchAtZeroEval₂WDivTarget
  rw [hp, Polynomial.eval₂_C, Polynomial.eval₂_C]
  intro h
  have hWne : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  rw [eq_div_iff (pow_ne_zero R.natDegree hWne)] at h
  -- h : lift c * W ^ R.natDegree = lift c
  have hz : liftToFunctionField (H := H) c
      * (liftToFunctionField (H := H) H.leadingCoeff ^ R.natDegree - 1) = 0 := by
    rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.mp hz with h1 | h2
  · exact hc h1
  · exact hW (sub_eq_zero.mp h2)

omit [Fact (Irreducible H)] in
/-- Coefficient-side source of the lifted `W`-power obstruction.  If the leading coefficient
itself has no `R.natDegree`-th power equal to `1`, then its image `W` in the function field has the
same nontrivial power. -/
theorem liftW_pow_ne_one_of_leadingCoeff_pow_ne_one (n : ℕ)
    (hpow : H.leadingCoeff ^ n ≠ 1) :
    liftToFunctionField (H := H) H.leadingCoeff ^ n ≠ 1 := by
  intro hW
  rw [← map_pow] at hW
  rw [show (1 : 𝕃 H) = liftToFunctionField (H := H) (1 : F[X]) by rw [map_one]] at hW
  exact hpow (BCIKS20.WPow.liftToFunctionField_injective H hW)

/-- Coefficient-side form of `eval₂WDivTarget_false_of_constant_of_W_pow_ne_one`.  This covers
unit-but-not-root-of-unity leading coefficients, such as the concrete witness `H = 2·Y`. -/
theorem eval₂WDivTarget_false_of_constant_of_leadingCoeff_pow_ne_one
    (x₀ : F) (R : F[X][X][Y]) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0)
    (hpow : H.leadingCoeff ^ R.natDegree ≠ 1) :
    ¬ RestrictedMatchAtZeroEval₂WDivTarget H x₀ R :=
  eval₂WDivTarget_false_of_constant_of_W_pow_ne_one H x₀ R c hp hc
    (liftW_pow_ne_one_of_leadingCoeff_pow_ne_one H R.natDegree hpow)

/-- **The carved order-zero P2 core is false for a `Y`-constant order-1 numerator over non-monic
`H`.** Composing the refutation of the `eval₂`/W-divisor target with the proven equivalence
`restrictedMatchAt_zero_iff_eval₂WDivTarget` (which uses only `2 ≤ R.natDegree`, never
`hHyp.dvd_evalX`). Hence `RestrictedFaaDiBrunoMatch` — the carved #139/#9-P2 core, and the content
asserted by the `restrictedFaaDiBrunoMatch_residual` axiom — does **not** hold as stated for
non-monic `H`: see the module docstring for the explicit non-vacuous witness family. -/
theorem restrictedMatchAt_zero_false_of_constant_of_W_pow_ne_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0)
    (hW : liftToFunctionField (H := H) H.leadingCoeff ^ R.natDegree ≠ 1) :
    ¬ RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 := by
  rw [restrictedMatchAt_zero_iff_eval₂WDivTarget H x₀ R hHyp hd]
  exact eval₂WDivTarget_false_of_constant_of_W_pow_ne_one H x₀ R c hp hc hW

/-- Coefficient-side W-power obstruction for the order-zero carved P2 core. -/
theorem restrictedMatchAt_zero_false_of_constant_of_leadingCoeff_pow_ne_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0)
    (hpow : H.leadingCoeff ^ R.natDegree ≠ 1) :
    ¬ RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 := by
  rw [restrictedMatchAt_zero_iff_eval₂WDivTarget H x₀ R hHyp hd]
  exact eval₂WDivTarget_false_of_constant_of_leadingCoeff_pow_ne_one H x₀ R c hp hc hpow

/-- Non-monic corollary of the order-zero obstruction: `W_pow_eq_iff` turns
`W ^ R.natDegree = 1 = W ^ 0` into `R.natDegree = 0`, contradicting `2 ≤ R.natDegree`. -/
theorem restrictedMatchAt_zero_false_of_constant_of_nonmonic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 := by
  refine restrictedMatchAt_zero_false_of_constant_of_W_pow_ne_one H x₀ R hHyp hd c hp hc ?_
  intro hW
  have hpow : (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree
      = (liftToFunctionField (H := H) H.leadingCoeff) ^ 0 := by
    simpa using hW
  have hdeg0 := (BCIKS20.WPow.W_pow_eq_iff H hlc R.natDegree 0).1 hpow
  omega

/-- Specialization-family form of `restrictedMatchAt_zero_false_of_constant_of_nonmonic`.
The Claim A.2 data are supplied by an explicit zero-th specialization `R(x₀, -, -) = g`, while
the obstruction still comes from the independent order-1 Hasse numerator being a nonzero
`Y`-constant. -/
theorem restrictedMatchAt_zero_false_of_constant_of_nonmonic_of_evalX_eq
    (x₀ : F) (R : F[X][X][Y]) (g : F[X][Y])
    (hR0 : Bivariate.evalX (Polynomial.C x₀) R = g)
    (hdvd : H ∣ g)
    (hsep : g.Separable)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ RestrictedFaaDiBrunoMatchAt H x₀ R
        (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep) 0 := by
  exact restrictedMatchAt_zero_false_of_constant_of_nonmonic H x₀ R
    (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep) hd hlc c hp hc

/-- Full-match form of the non-monic order-zero obstruction: since an all-orders
`RestrictedFaaDiBrunoMatch` projects to its zero-th component, the constant-numerator
order-zero refutation rules out the all-orders carved P2 core in the same regime. -/
theorem restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ RestrictedFaaDiBrunoMatch H x₀ R hHyp := by
  intro hmatch
  exact restrictedMatchAt_zero_false_of_constant_of_nonmonic H x₀ R hHyp hd hlc c hp hc
    (RestrictedFaaDiBrunoMatch.at H x₀ R hHyp hmatch 0)

/-- Full-match refutation from the coefficient-side `W`-power obstruction. -/
theorem restrictedFaaDiBrunoMatch_false_of_constant_of_leadingCoeff_pow_ne_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0)
    (hpow : H.leadingCoeff ^ R.natDegree ≠ 1) :
    ¬ RestrictedFaaDiBrunoMatch H x₀ R hHyp := by
  intro hmatch
  exact restrictedMatchAt_zero_false_of_constant_of_leadingCoeff_pow_ne_one H x₀ R hHyp
    hd c hp hc hpow (RestrictedFaaDiBrunoMatch.at H x₀ R hHyp hmatch 0)

/-- Specialization-family full-match form of the non-monic order-zero obstruction.  The
zero-th specialization supplies the Claim A.2 hypotheses, but the all-orders carved P2 core is
already impossible because its zero-th projection contradicts the independent constant numerator. -/
theorem restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic_of_evalX_eq
    (x₀ : F) (R : F[X][X][Y]) (g : F[X][Y])
    (hR0 : Bivariate.evalX (Polynomial.C x₀) R = g)
    (hdvd : H ∣ g)
    (hsep : g.Separable)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ RestrictedFaaDiBrunoMatch H x₀ R
        (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep) := by
  intro hmatch
  exact restrictedMatchAt_zero_false_of_constant_of_nonmonic_of_evalX_eq H x₀ R g hR0
    hdvd hsep hd hlc c hp hc
    (RestrictedFaaDiBrunoMatch.at H x₀ R
      (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep) hmatch 0)

/-- Normalized-partition full-match form of the non-monic order-zero obstruction. Since the
partition residual is equivalent to the carved `RestrictedFaaDiBrunoMatch`, the same constant
order-1 numerator witness rules it out. -/
theorem restrictedFaaDiBrunoPartitionMatch_false_of_constant_of_nonmonic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp := by
  intro hpart
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic H x₀ R hHyp hd hlc c hp hc
    (RestrictedFaaDiBrunoMatch.of_partitionMatch H x₀ R hHyp hpart)

/-- Specialization-family normalized-partition full-match refutation. -/
theorem restrictedFaaDiBrunoPartitionMatch_false_of_constant_of_nonmonic_of_evalX_eq
    (x₀ : F) (R : F[X][X][Y]) (g : F[X][Y])
    (hR0 : Bivariate.evalX (Polynomial.C x₀) R = g)
    (hdvd : H ∣ g)
    (hsep : g.Separable)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ RestrictedFaaDiBrunoPartitionMatch H x₀ R
        (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep) := by
  intro hpart
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic_of_evalX_eq H x₀ R g
    hR0 hdvd hsep hd hlc c hp hc
    (RestrictedFaaDiBrunoMatch.of_partitionMatch H x₀ R
      (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep) hpart)

/-- Fixed-order-family partition residual form of the non-monic order-zero obstruction. -/
theorem forall_partitionMatchAt_false_of_constant_of_nonmonic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ (∀ t : ℕ, RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t) := by
  intro hat
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic H x₀ R hHyp hd hlc c hp hc
    (RestrictedFaaDiBrunoMatch.of_forall_partitionMatchAt H x₀ R hHyp hat)

/-- Specialization-family fixed-order-family partition residual refutation. -/
theorem forall_partitionMatchAt_false_of_constant_of_nonmonic_of_evalX_eq
    (x₀ : F) (R : F[X][X][Y]) (g : F[X][Y])
    (hR0 : Bivariate.evalX (Polynomial.C x₀) R = g)
    (hdvd : H ∣ g)
    (hsep : g.Separable)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ (∀ t : ℕ, RestrictedFaaDiBrunoPartitionMatchAt H x₀ R
        (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep) t) := by
  intro hat
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic_of_evalX_eq H x₀ R g
    hR0 hdvd hsep hd hlc c hp hc
    (RestrictedFaaDiBrunoMatch.of_forall_partitionMatchAt H x₀ R
      (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep) hat)

/-- Legacy successor-residual form of the non-monic order-zero obstruction. -/
theorem faaDiBrunoSuccSumZeroResidual_false_of_constant_of_nonmonic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp := by
  intro hzero
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic H x₀ R hHyp hd hlc c hp hc
    ((restrictedFaaDiBrunoMatch_iff_faaDiBrunoSuccSumZero H x₀ R hHyp).2 hzero)

/-- Legacy successor-residual refutation from the coefficient-side `W`-power obstruction. -/
theorem faaDiBrunoSuccSumZeroResidual_false_of_constant_of_leadingCoeff_pow_ne_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0)
    (hpow : H.leadingCoeff ^ R.natDegree ≠ 1) :
    ¬ FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp := by
  intro hzero
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_leadingCoeff_pow_ne_one
    H x₀ R hHyp hd c hp hc hpow
    ((restrictedFaaDiBrunoMatch_iff_faaDiBrunoSuccSumZero H x₀ R hHyp).2 hzero)

/-- Specialization-family legacy successor-residual refutation. -/
theorem faaDiBrunoSuccSumZeroResidual_false_of_constant_of_nonmonic_of_evalX_eq
    (x₀ : F) (R : F[X][X][Y]) (g : F[X][Y])
    (hR0 : Bivariate.evalX (Polynomial.C x₀) R = g)
    (hdvd : H ∣ g)
    (hsep : g.Separable)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ FaaDiBrunoSuccSumZeroResidual H x₀ R
        (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep) := by
  intro hzero
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic_of_evalX_eq H x₀ R g
    hR0 hdvd hsep hd hlc c hp hc
    ((restrictedFaaDiBrunoMatch_iff_faaDiBrunoSuccSumZero H x₀ R
      (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep)).2 hzero)

/-- Analytic assembled-root form of the non-monic order-zero obstruction. -/
theorem eval_βHenselAssembled_eq_zero_false_of_constant_of_nonmonic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0) := by
  intro hroot
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic H x₀ R hHyp hd hlc c hp hc
    ((restrictedFaaDiBrunoMatch_iff_eval_eq_zero H x₀ R hHyp).2 hroot)

/-- Analytic assembled-root refutation from the coefficient-side `W`-power obstruction. -/
theorem eval_βHenselAssembled_eq_zero_false_of_constant_of_leadingCoeff_pow_ne_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0)
    (hpow : H.leadingCoeff ^ R.natDegree ≠ 1) :
    ¬ (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0) := by
  intro hroot
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_leadingCoeff_pow_ne_one
    H x₀ R hHyp hd c hp hc hpow
    ((restrictedFaaDiBrunoMatch_iff_eval_eq_zero H x₀ R hHyp).2 hroot)

/-- Specialization-family analytic assembled-root refutation. -/
theorem eval_βHenselAssembled_eq_zero_false_of_constant_of_nonmonic_of_evalX_eq
    (x₀ : F) (R : F[X][X][Y]) (g : F[X][Y])
    (hR0 : Bivariate.evalX (Polynomial.C x₀) R = g)
    (hdvd : H ∣ g)
    (hsep : g.Separable)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ (Polynomial.eval (βHenselAssembled H x₀ R
        (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep)) (Q x₀ R H) = 0) := by
  intro hroot
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic_of_evalX_eq H x₀ R g
    hR0 hdvd hsep hd hlc c hp hc
    ((restrictedFaaDiBrunoMatch_iff_eval_eq_zero H x₀ R
      (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep)).2 hroot)

/-- Assembled-equals-genuine form of the non-monic order-zero obstruction. -/
theorem βHenselAssembled_eq_gammaGenuine_false_of_constant_of_nonmonic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp := by
  intro h
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic H x₀ R hHyp hd hlc c hp hc
    ((restrictedFaaDiBrunoMatch_iff_βHenselAssembled_eq_gammaGenuine H x₀ R hHyp).2 h)

/-- Assembled-equals-genuine refutation from the coefficient-side `W`-power obstruction. -/
theorem βHenselAssembled_eq_gammaGenuine_false_of_constant_of_leadingCoeff_pow_ne_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0)
    (hpow : H.leadingCoeff ^ R.natDegree ≠ 1) :
    ¬ βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp := by
  intro h
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_leadingCoeff_pow_ne_one
    H x₀ R hHyp hd c hp hc hpow
    ((restrictedFaaDiBrunoMatch_iff_βHenselAssembled_eq_gammaGenuine H x₀ R hHyp).2 h)

/-- Specialization-family assembled-equals-genuine refutation. -/
theorem βHenselAssembled_eq_gammaGenuine_false_of_constant_of_nonmonic_of_evalX_eq
    (x₀ : F) (R : F[X][X][Y]) (g : F[X][Y])
    (hR0 : Bivariate.evalX (Polynomial.C x₀) R = g)
    (hdvd : H ∣ g)
    (hsep : g.Separable)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ βHenselAssembled H x₀ R (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep)
        = gammaGenuine x₀ R H (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep) := by
  intro h
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic_of_evalX_eq H x₀ R g
    hR0 hdvd hsep hd hlc c hp hc
    ((restrictedFaaDiBrunoMatch_iff_βHenselAssembled_eq_gammaGenuine H x₀ R
      (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep)).2 h)

/-- Coefficient-wise assembled/genuine form of the non-monic order-zero obstruction. -/
theorem coeff_βHenselAssembled_eq_αGenuine_forall_false_of_constant_of_nonmonic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ (∀ t : ℕ, PowerSeries.coeff t (βHenselAssembled H x₀ R hHyp)
        = αGenuine H x₀ R hHyp t) := by
  intro h
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic H x₀ R hHyp hd hlc c hp hc
    ((restrictedFaaDiBrunoMatch_iff_coeff_eq_αGenuine H x₀ R hHyp).2 h)

/-- Coefficient-wise assembled/genuine refutation from the coefficient-side `W`-power
obstruction. -/
theorem coeff_βHenselAssembled_eq_αGenuine_forall_false_of_constant_of_leadingCoeff_pow_ne_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0)
    (hpow : H.leadingCoeff ^ R.natDegree ≠ 1) :
    ¬ (∀ t : ℕ, PowerSeries.coeff t (βHenselAssembled H x₀ R hHyp)
        = αGenuine H x₀ R hHyp t) := by
  intro h
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_leadingCoeff_pow_ne_one
    H x₀ R hHyp hd c hp hc hpow
    ((restrictedFaaDiBrunoMatch_iff_coeff_eq_αGenuine H x₀ R hHyp).2 h)

/-- Specialization-family coefficient-wise assembled/genuine refutation. -/
theorem coeff_βHenselAssembled_eq_αGenuine_forall_false_of_constant_of_nonmonic_of_evalX_eq
    (x₀ : F) (R : F[X][X][Y]) (g : F[X][Y])
    (hR0 : Bivariate.evalX (Polynomial.C x₀) R = g)
    (hdvd : H ∣ g)
    (hsep : g.Separable)
    (hd : 2 ≤ R.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) (c : F[X])
    (hp : Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
        = Polynomial.C c)
    (hc : liftToFunctionField (H := H) c ≠ 0) :
    ¬ (∀ t : ℕ, PowerSeries.coeff t
          (βHenselAssembled H x₀ R (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep))
        = αGenuine H x₀ R (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep) t) := by
  intro h
  exact restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic_of_evalX_eq H x₀ R g
    hR0 hdvd hsep hd hlc c hp hc
    ((restrictedFaaDiBrunoMatch_iff_coeff_eq_αGenuine H x₀ R
      (ClaimA2.Hypotheses.of_evalX_eq hR0 hdvd hsep)).2 h)

end BCIKS20.HenselNumerator

#print axioms BCIKS20AppendixA.ClaimA2.Hypotheses.of_evalX_eq
#print axioms BCIKS20.HenselNumerator.eval₂WDivTarget_false_of_constant_of_W_pow_ne_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.liftW_pow_ne_one_of_leadingCoeff_pow_ne_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.eval₂WDivTarget_false_of_constant_of_leadingCoeff_pow_ne_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_false_of_constant_of_W_pow_ne_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_false_of_constant_of_leadingCoeff_pow_ne_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_false_of_constant_of_nonmonic
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_false_of_constant_of_nonmonic_of_evalX_eq
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoMatch_false_of_constant_of_leadingCoeff_pow_ne_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoMatch_false_of_constant_of_nonmonic_of_evalX_eq
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoPartitionMatch_false_of_constant_of_nonmonic
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoPartitionMatch_false_of_constant_of_nonmonic_of_evalX_eq
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.forall_partitionMatchAt_false_of_constant_of_nonmonic
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.forall_partitionMatchAt_false_of_constant_of_nonmonic_of_evalX_eq
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.faaDiBrunoSuccSumZeroResidual_false_of_constant_of_nonmonic
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.faaDiBrunoSuccSumZeroResidual_false_of_constant_of_leadingCoeff_pow_ne_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.faaDiBrunoSuccSumZeroResidual_false_of_constant_of_nonmonic_of_evalX_eq
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.eval_βHenselAssembled_eq_zero_false_of_constant_of_nonmonic
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.eval_βHenselAssembled_eq_zero_false_of_constant_of_leadingCoeff_pow_ne_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.eval_βHenselAssembled_eq_zero_false_of_constant_of_nonmonic_of_evalX_eq
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.βHenselAssembled_eq_gammaGenuine_false_of_constant_of_nonmonic
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.βHenselAssembled_eq_gammaGenuine_false_of_constant_of_leadingCoeff_pow_ne_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.βHenselAssembled_eq_gammaGenuine_false_of_constant_of_nonmonic_of_evalX_eq
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.coeff_βHenselAssembled_eq_αGenuine_forall_false_of_constant_of_nonmonic
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.coeff_βHenselAssembled_eq_αGenuine_forall_false_of_constant_of_leadingCoeff_pow_ne_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.coeff_βHenselAssembled_eq_αGenuine_forall_false_of_constant_of_nonmonic_of_evalX_eq
