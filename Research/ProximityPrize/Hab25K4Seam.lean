/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.GuruswamiSudan.GSCellProduction
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSInterpolantZDegreeGraded
import Research.ProximityPrize.Hab25JohnsonNumericBridge

/-!
# The K4 ⟹ `JohnsonNumericBound` seam

One theorem: a uniform K4 pinning input (every decoded cell on a single specialized
irreducible factor obeys the size-`T` bound, for every word stack) plus the closed-form
numeric comparison discharge the `JohnsonNumericBound` residual outright, through the
per-stack numeric count `bad_card_le_numeric` of `GSCellProduction.lean`.

This makes the remaining shape of the #302 Johnson MCA chain a single implication:

  K4 (BCIKS20 Steps 5–7 capture)  ⟹  `JohnsonNumericBound`  ⟹  WHIR pair MCA,

with the second arrow already in-tree (`Hab25WhirBridge.lean`). K4 is proven on the
unique-decoding window (`Hab25CaptureKernelUD.lean`); beyond it, it is the single
remaining deep input.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open GuruswamiSudan.OverRatFunc
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **K4 ⟹ `JohnsonNumericBound`.** A uniform K4 pinning input over all word stacks,
plus the numeric comparison for `N = (D/(k−1)+1)·T`, discharge the Hab25 numeric
residual through the per-stack count `bad_card_le_numeric`. -/
theorem johnsonNumericBound_of_K4 {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (η δ : ℝ≥0) (T : ℕ)
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hT0 : n * (GuruswamiSudan.constraintIndices m).card * gs_degree_bound k n m ≤ T)
    (hK4 : ∀ (u : WordStack F₀ (Fin 2) (Fin n)) (E : Finset F₀) (P : F₀ → F₀[X])
      (R : (F₀[X])[X][Y]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T)
    (hNdiv : (((gs_degree_bound k n m / (k - 1) + 1) * T : ℕ) : ℝ) /
        (Fintype.card F₀ : ℝ) ≤ johnsonBoundReal domain k η δ) :
    JohnsonNumericBound domain k η δ :=
  JohnsonNumericBound.of_card_le_nat domain k η δ
    ((gs_degree_bound k n m / (k - 1) + 1) * T) hNdiv
    (fun u => bad_card_le_numeric domain u δ T hk1 hkn hm hδ1 hδJ hT0 (hK4 u))

/-- **The graded per-stack numeric count, modulo K4 only.** `bad_card_le_numeric` with
the graded Z-degree producer (`gs_existence_zDegree_graded_card`): the degenerate-cell
budget is `n·|constraintIndices m|·(D/(k−1))` — **linear in `n`** (the BCIKS20 Claim 5.4
shape), one factor of `n` sharper than the Cramer route, which is what the beyond-window
Johnson numeric edge requires. -/
theorem bad_card_le_numeric_graded {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin 2) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hT0 : n * (GuruswamiSudan.constraintIndices m).card *
      (gs_degree_bound k n m / (k - 1)) ≤ T)
    (hK4 : ∀ (E : Finset F₀) (P : F₀ → F₀[X]) (R : (F₀[X])[X][Y]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T) :
    (Finset.univ.filter (fun γ : F₀ =>
      _root_.ProximityGap.mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
        δ (u 0) (u 1) γ)).card ≤
      (gs_degree_bound k n m / (k - 1) + 1) * T := by
  classical
  -- the graded producer, with its `Conditions` retained for the Y-degree bound
  obtain ⟨Q₀, h0, hcond, hcard⟩ :=
    GuruswamiSudan.OverRatFunc.ZDegree.Graded.gs_existence_zDegree_graded_card
      (F := F₀) k m domain (u 0) (u 1) hk1 (NeZero.ne n) hm
  have hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) (1 : F₀[X]))) *
        Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) := by
    simp
  obtain ⟨Index, Ecell, P, hIdxCard, hcover, hdec, hnone, hbadcell, hfactor⟩ :=
    exists_cell_production domain u δ
      (n * (GuruswamiSudan.constraintIndices m).card * (gs_degree_bound k n m / (k - 1)))
      hcond hrep h0 hkn hm hδ1 hδJ (degenerate_card_bound_of_filter hcard)
  -- the Y-degree of the integer interpolant
  have hnat : natWeightedDegree
      (Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀)))) 1 (k - 1) ≤
      gs_degree_bound k n m := by
    have h := hcond.Q_deg
    rw [weightedDegree_eq_natWeightedDegree] at h
    exact_mod_cast h
  have hdegK : (Q₀.map (Polynomial.mapRingHom
      (algebraMap F₀[X] (RatFunc F₀)))).natDegree ≤ gs_degree_bound k n m / (k - 1) :=
    GuruswamiSudan.natDegree_le_of_natWeightedDegree (by omega) hnat
  have hmapinj : Function.Injective
      (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) := by
    rw [Polynomial.coe_mapRingHom]
    exact Polynomial.map_injective _ (IsFractionRing.injective F₀[X] (RatFunc F₀))
  have hdegQ₀ : Q₀.natDegree ≤ gs_degree_bound k n m / (k - 1) := by
    rwa [Polynomial.natDegree_map_eq_of_injective hmapinj Q₀] at hdegK
  -- count the live cells (`card_le_of_live_factor_cells`), each bounded by `T`
  refine card_le_of_live_factor_cells h0 hdegQ₀ Index Ecell _ hcover
    (fun R hR => ⟨(hfactor R hR).1, fun γ hγ =>
      ⟨((hfactor R hR).2 γ hγ).1, P γ, ((hfactor R hR).2 γ hγ).2⟩⟩) ?_
  intro ij hijIdx
  cases ij with
  | none => exact le_trans hbadcell hT0
  | some R =>
    obtain ⟨hRmem, hsurf⟩ := hfactor R hijIdx
    have hirr : Irreducible R :=
      UniqueFactorizationMonoid.irreducible_of_factor R (Multiset.mem_toFinset.mp hRmem)
    exact hK4 _ P R hirr (hdec _ hijIdx) (fun γ hγ => (hsurf γ hγ).2)

/-- **K4 ⟹ `JohnsonNumericBound`, graded budget.** Same seam as
`johnsonNumericBound_of_K4`, with the degenerate-cell budget linear in `n`. -/
theorem johnsonNumericBound_of_K4_graded {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (η δ : ℝ≥0) (T : ℕ)
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hT0 : n * (GuruswamiSudan.constraintIndices m).card *
      (gs_degree_bound k n m / (k - 1)) ≤ T)
    (hK4 : ∀ (u : WordStack F₀ (Fin 2) (Fin n)) (E : Finset F₀) (P : F₀ → F₀[X])
      (R : (F₀[X])[X][Y]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T)
    (hNdiv : (((gs_degree_bound k n m / (k - 1) + 1) * T : ℕ) : ℝ) /
        (Fintype.card F₀ : ℝ) ≤ johnsonBoundReal domain k η δ) :
    JohnsonNumericBound domain k η δ :=
  JohnsonNumericBound.of_card_le_nat domain k η δ
    ((gs_degree_bound k n m / (k - 1) + 1) * T) hNdiv
    (fun u => bad_card_le_numeric_graded domain u δ T hk1 hkn hm hδ1 hδJ hT0 (hK4 u))

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_K4
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.bad_card_le_numeric_graded
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_K4_graded
