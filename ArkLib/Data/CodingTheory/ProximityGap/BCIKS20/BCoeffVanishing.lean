/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeightDivisibility
import ArkLib.ToMathlib.WeightLambdaCalculus

/-!
# BCoeffVanishing

Module docstring for `BCoeffVanishing.lean`.
-/


open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate
open BCIKS20AppendixA

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

theorem hasseDerivY_eq_zero_of_lt (R : F[X][X][Y]) {s : ℕ} (h : R.natDegree < s) :
    hasseDerivY s R = 0 :=
  Polynomial.hasseDeriv_eq_zero_of_lt_natDegree R s h

theorem B_coeff_eq_zero_of_natDegree_lt (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) {m : ℕ}
    (lam : Nat.Partition m) (h : R.natDegree < sigmaLambda lam) :
    B_coeff H x₀ R i1 lam = 0 := by
  have hX0 : hasseDerivX i1 (0 : F[X][X][Y]) = 0 := by
    simp [hasseDerivX]
  unfold B_coeff hasseCoeffRepr𝒪
  have hE0 : Polynomial.Bivariate.evalX (Polynomial.C x₀) (0 : F[X][X][Y]) = 0 := by
    ext n m
    show (Polynomial.eval (Polynomial.C x₀) ((0 : F[X][X][Y]).coeff n)).coeff _ = 0
    simp
  rw [hasseDerivY_eq_zero_of_lt R h, hX0, hE0]
  simp

/-- **Parameterized `hbξ` reduction**: the ξ weight budget follows from per-coefficient
degree bounds on `ξ_pre` (the honest GS-bundle input shape), via `weight_Λ_le_iff`. -/
theorem xi_weight_le_of_coeff_bounds (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D b : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hcoeff : ∀ n ∈ (ClaimA2.ξ_pre x₀ R H).support,
      n * (D + 1 - Bivariate.natDegreeY H) + ((ClaimA2.ξ_pre x₀ R H).coeff n).natDegree ≤ b) :
    weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D ≤ (WithBot.some b : WithBot ℕ) := by
  refine (weight_Λ_over_𝒪_le_of_mk_eq hDH hH (r := ClaimA2.ξ_pre x₀ R H) rfl).trans ?_
  rw [weight_Λ_le_iff]
  exact hcoeff

/-- **The monic `bW` budget**: when `H` is monic, `W𝒪 H = 1`, so its `Λ`-weight is `≤ 0` —
the trivial `bW = 0` input of `betaRec_weight_le`. -/
theorem W𝒪_weight_le_zero_of_monic (hmonic : H.Monic) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D) :
    weight_Λ_over_𝒪 hH (W𝒪 H) D ≤ (0 : WithBot ℕ) := by
  rw [BCIKS20.HenselNumerator.AlphaWeight.W𝒪_eq_one_of_monic H hmonic]
  exact ArkLib.weight_Λ_over_𝒪_one_le hDH hH

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.B_coeff_eq_zero_of_natDegree_lt
#print axioms BCIKS20.HenselNumerator.xi_weight_le_of_coeff_bounds
#print axioms BCIKS20.HenselNumerator.W𝒪_weight_le_zero_of_monic
