/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.MCAGSWitness
import ArkLib.Data.Polynomial.Bivariate
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Grand Challenge 1 (mcaConjecture) List-Size Bounds: Brute Force Hypotheses

The core open problem for ABF26 Grand Challenge 1 is bounding the Guruswami-Sudan
list size `L.card` beyond the Johnson radius, specifically `L.card ≤ poly(|ι|, 1/ρ)`.
Naive attempts are refuted. Below are 10 red-team hypotheses that attempt to bound the
list size using different structural properties of the domain and the interpolation
polynomials. They are deliberately stated in *bare* form (no `H ≠ 0` or root-membership
side conditions): they are refutation targets, not theorem claims, and the elementary
counterexamples in `GrandChallenge1RefutationProofs.lean` are stated against exactly
these bare forms. See `GrandChallenge1BruteForceRefutations.lean` for the named
refutation targets.

This file also restores three small bivariate helpers (`Bivariate.natDegreeX`,
`Bivariate.hasseDerivX`, `Bivariate.hasseDerivY`) that this chain depended on before
the CompPoly migration renamed `natDegreeX` to `degreeX` and dropped the bivariate
Hasse-derivative wrappers. The Hasse wrappers mirror the (independently verified)
`BCIKS20.HenselNumerator.hasseDerivX/Y` construction one `Polynomial` layer down.
-/

open Polynomial

namespace Polynomial.Bivariate

variable {F : Type} [Semiring F]

/-- The `X`-degree of a bivariate polynomial, as a natural number. Restored alias for
CompPoly's `Polynomial.Bivariate.degreeX` (the CompPoly migration renamed the original
`natDegreeX`); kept as a definition so legacy call sites keep their name. -/
noncomputable def natDegreeX (f : F[X][Y]) : ℕ :=
  degreeX f

@[simp]
theorem natDegreeX_eq_degreeX (f : F[X][Y]) : natDegreeX f = degreeX f := rfl

/-- `Δ_Y^{k}`: the `k`-th Hasse derivative in the outer variable `Y`, i.e. the ordinary
mathlib `Polynomial.hasseDeriv k` applied at the outer layer. -/
noncomputable def hasseDerivY (k : ℕ) (f : F[X][Y]) : F[X][Y] :=
  Polynomial.hasseDeriv k f

/-- `Δ_X^{k}`: the `k`-th Hasse derivative in the inner variable `X`, applied
coefficient-wise: each `Y`-coefficient `a : F[X]` is sent to `Polynomial.hasseDeriv k a`. -/
noncomputable def hasseDerivX (k : ℕ) (f : F[X][Y]) : F[X][Y] :=
  f.sum fun n a => Polynomial.monomial n (Polynomial.hasseDeriv k a)

end Polynomial.Bivariate

open Polynomial.Bivariate ProximityGap MCAGS Code NNReal

namespace GrandChallenge1BruteForce

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

-- Hypothesis 1: Bivariate Resultant Rank Bound
-- The resultant of the GS interpolant H and its Y-derivative limits the number of roots
-- globally over F(X).
def Hyp1_ResultantRankBound (H : F[X][Y]) (L : Finset (ι → F)) : Prop :=
  Polynomial.resultant H (hasseDerivY 1 H) ≠ 0 →
    L.card ≤ (Bivariate.natDegreeX H) * (Bivariate.natDegreeY H)

-- Hypothesis 2: Smooth Curve Intersection (Bezout)
-- If the interpolation curve is geometrically smooth, the number of rational points
-- is tightly bounded by the Hasse-Weil/Bezout bounds, restricting the list size.
def Hyp2_SmoothCurveIntersection (H : F[X][Y]) (L : Finset (ι → F)) : Prop :=
  (∀ x y, evalEval x y H = 0 →
    evalEval x y (hasseDerivX 1 H) ≠ 0 ∨ evalEval x y (hasseDerivY 1 H) ≠ 0) →
  L.card ≤ Bivariate.totalDegree H

-- Hypothesis 3: Punctured Support Sparsity
-- For any sufficiently sparse evaluation domain, the interpolation polynomial factors
-- into low-degree components.
def Hyp3_PuncturedSupportSparsity (domain : ι ↪ F) (L : Finset (ι → F)) : Prop :=
  (Fintype.card ι : ℝ) ≤ (Fintype.card F : ℝ) ^ (1/2 : ℝ) → L.card ≤ Fintype.card ι

-- Hypothesis 4: Derivative Multiplicity Collapse
-- If a root has high multiplicity in H, it must have multiplicity in the Hasse derivatives.
-- (Bare form; the original statement left `domain` and `i` unbound, which never elaborated.)
def Hyp4_DerivativeMultiplicityCollapse (domain : ι ↪ F) (H : F[X][Y]) (u : ι → F) : Prop :=
  ∀ i, evalEval (domain i) (u i) H = 0 → evalEval (domain i) (u i) (hasseDerivY 1 H) = 0

-- Hypothesis 5: Schwartz-Zippel Density Limit
-- The total number of valid list decoding trajectories is bounded by the probability
-- of a random bivariate polynomial vanishing.
def Hyp5_SchwartzZippelDensity (H : F[X][Y]) (L : Finset (ι → F)) : Prop :=
  L.card ≤ Bivariate.totalDegree H * Fintype.card ι

-- Hypothesis 6: Sub-Space Evasion
-- The list elements must lie in a proper linear subspace of the message space if the
-- error exceeds the Johnson radius.
def Hyp6_SubSpaceEvasion (L : Finset (ι → F)) : Prop :=
  ∃ (v : ι → F), v ≠ 0 ∧ ∀ u ∈ L, ∃ (c : F), u = c • v

-- Hypothesis 7: Interpolation Matrix Rank Bound
-- The rank of the GS interpolation matrix strictly bounds the number of Y-roots.
def Hyp7_MatrixRankBound (L : Finset (ι → F)) (k : ℕ) : Prop :=
  L.card ≤ k^2

-- Hypothesis 8: Algebraic Independence of Roots
-- The elements of the list are algebraically independent over the base field.
def Hyp8_AlgebraicIndependence (L : Finset (ι → F)) : Prop :=
  L.card ≤ Fintype.card F

-- Hypothesis 9: Multiplicity Intersection Bound
-- The sum of multiplicities of intersections across the domain is tightly constrained.
def Hyp9_MultiplicityIntersection (H : F[X][Y]) (L : Finset (ι → F)) : Prop :=
  L.card ≤ (Bivariate.natDegreeX H)

-- Hypothesis 10: Affine Variety Dimension
-- The list size is bounded by the dimension data of the affine variety cut out by H.
def Hyp10_AffineVarietyDimension (H : F[X][Y]) (L : Finset (ι → F)) : Prop :=
  L.card ≤ (Bivariate.natDegreeY H)

end GrandChallenge1BruteForce
