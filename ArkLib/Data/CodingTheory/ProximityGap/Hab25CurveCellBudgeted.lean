/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveCellProduction
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSCurveInterpolantZDegree

/-!
# The budgeted (`T`-instantiated) curve-cell bad-card bound (#389, Johnson lane)

`exists_curve_cell_production_total` / `bad_card_le_of_curve_cell_production`
(`Hab25CurveCellProduction.lean`) leave the degenerate-set budget `T` **parametrized**: the caller
must supply `hbadz : ∀ S, (∀ z ∈ S, Q₀ vanishes at z) → S.card ≤ T`.  The docstring there notes the
producer of that budget — the L-ary `Z`-degree-bounded interpolant — was "not in-tree yet".

It is now in-tree: `GuruswamiSudan.OverRatFunc.ZDegree.gs_existence_curve_zDegree_badz`
(`GSCurveInterpolantZDegree.lean`) produces, in one shot, a nonzero interpolant `Q₀` with the
Guruswami–Sudan `Conditions`, a `natDegree` bound, AND the explicit budget
`T = (n · #constraintIndices m) · (gs_degree_bound k n m · (L − 1))`.

This file wires the two together, eliminating the parametrization:

* `bad_card_le_total_budgeted` — there exists a nonzero `Q₀` such that, conditionally only on the
  `hK4` surface-cell bound at the explicit budget `T`, the curve-`mcaEvent` scalar count is
  `≤ (#factors Q₀ + 1) · T`, for every `δ < gs_johnson k n m`.

The sole remaining input is `hK4` (the per-surface-cell bound); the §6 counting budget that the
Hab25 docstring flagged as external is now discharged by construction.  Axiom-clean
(`propext, Classical.choice, Quot.sound`).
-/

open Polynomial Polynomial.Bivariate Finset GuruswamiSudan
open GuruswamiSudan.OverRatFunc
open _root_.ProximityGap Code
open scoped NNReal ENNReal

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **Budgeted curve-cell bad-card bound.**  The degenerate-set budget `T` is SUPPLIED
(no longer parametrized) by the in-tree `gs_existence_curve_zDegree_badz`: there is a nonzero
interpolant `Q₀` for which, conditionally on the `hK4` surface-cell bound at the explicit budget
`T = (n · #constraintIndices m) · (gs_degree_bound k n m · (L − 1))`, the curve-`mcaEvent` scalar
count is `≤ (#factors Q₀ + 1) · T`.  Valid up to the GS/Johnson radius `δ < gs_johnson k n m`. -/
theorem bad_card_le_total_budgeted {n k m L : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀) (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0)
    (hk2 : 2 ≤ k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m) :
    ∃ Q₀ : (F₀[X])[X][Y], Q₀ ≠ 0 ∧
      ((∀ (E : Finset F₀) (P : F₀ → F₀[X]) (R : (F₀[X])[X][Y]),
          R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset →
          (∀ γ ∈ E, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ) →
          (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
          E.card ≤ (n * (constraintIndices m).card) * (gs_degree_bound k n m * (L - 1))) →
        (Finset.univ.filter (fun γ : F₀ =>
          _root_.ProximityGap.mcaEventCurve
            ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ u γ)).card ≤
          ((UniqueFactorizationMonoid.factors Q₀).toFinset.card + 1) *
            ((n * (constraintIndices m).card) * (gs_degree_bound k n m * (L - 1)))) := by
  classical
  obtain ⟨Q₀, hQ₀0, hcond, hdeg, hbadz⟩ :=
    GuruswamiSudan.OverRatFunc.ZDegree.gs_existence_curve_zDegree_badz
      (F := F₀) k m domain (fun j i => u j i) (by omega) (NeZero.ne n) hm
  refine ⟨Q₀, hQ₀0, fun hK4 => ?_⟩
  have hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀)))
      = Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) 1))
          * Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) := by
    rw [map_one, map_one, map_one, one_mul]
  exact bad_card_le_of_curve_cell_production domain u δ _ hcond hrep hQ₀0 hkn hm hδ1 hδJ hbadz hK4

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
