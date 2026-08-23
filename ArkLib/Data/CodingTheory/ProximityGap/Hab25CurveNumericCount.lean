/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSInterpolantZDegreeCurve
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveCapture

/-!
# The `L`-ary per-stack numeric count — modulo `L`-ary K4 only

The general-arity mirror of `bad_card_le_numeric`: composing the curve cell production
(`Hab25CurveCellProduction.lean`), the `L`-ary graded Z-degree producer
(`GSInterpolantZDegreeCurve.lean`), the positive-degree factor count, and an `L`-ary K4
pinning input, every `L`-row word stack has at most

  `(gs_degree_bound k n m / (k−1) + 1) · T`,  `T := n·|cI|·((L−1)·(D/(k−1)))`

bad scalars of `mcaEventCurve`. The K4 input is exactly what
`cell_card_le_of_curve_decode_family_pinning` (`Hab25CurveCapture.lean`) discharges given
the curve pinning — so after this file the **entire `L`-ary chain mirrors the pair chain**:
its sole remaining mathematical input is the `L`-ary pinning past the threshold (the
Steps 5–7 capture at arity `L`, sharing the #138/#139 Hensel kernel with the pair case).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open GuruswamiSudan.OverRatFunc
open _root_.ProximityGap Code
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **The `L`-ary per-stack numeric count, modulo `L`-ary K4 only** (mirrors
`bad_card_le_numeric`). The graded curve producer supplies the interpolant and the
linear-in-`n` degenerate budget; the cells split along `≤ D/(k−1) + 1` classes; the K4
input bounds each nondegenerate class. -/
theorem bad_card_le_numeric_curve {n k m L : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hT0 : n * (GuruswamiSudan.constraintIndices m).card *
      ((L - 1) * (gs_degree_bound k n m / (k - 1))) ≤ T)
    (hK4 : ∀ (E : Finset F₀) (P : F₀ → F₀[X]) (R : (F₀[X])[X][Y]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T) :
    (Finset.univ.filter (fun γ : F₀ =>
      _root_.ProximityGap.mcaEventCurve
        ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ u γ)).card ≤
      (gs_degree_bound k n m / (k - 1) + 1) * T := by
  classical
  -- the `L`-ary graded producer, `Conditions` retained for the Y-degree bound
  obtain ⟨Q₀, h0, hcond, hcard⟩ :=
    GuruswamiSudan.OverRatFunc.ZDegree.Curve.gs_existence_zDegree_curve_card
      (F := F₀) k m domain (fun j i => u j i) hk1 (NeZero.ne n) hm
  have hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) (1 : F₀[X]))) *
        Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) := by
    simp
  obtain ⟨Index, Ecell, P, hIdxCard, hcover, hdec, hnone, hbadcell, hfactor⟩ :=
    exists_curve_cell_production domain u δ
      (n * (GuruswamiSudan.constraintIndices m).card *
        ((L - 1) * (gs_degree_bound k n m / (k - 1))))
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
  -- the nonempty cells inject into {none} ∪ positive-degree factors
  set posF : Finset ((F₀[X])[X][Y]) :=
    (UniqueFactorizationMonoid.factors Q₀).toFinset.filter
      (fun q => 1 ≤ q.natDegree) with hposF
  set Index' : Finset (Option ((F₀[X])[X][Y])) :=
    Index.filter (fun ij => (Ecell ij).Nonempty) with hIndex'
  have hsub' : Index' ⊆ insert none (posF.image some) := by
    intro ij hij
    obtain ⟨hijIdx, hne⟩ := Finset.mem_filter.mp hij
    cases ij with
    | none => exact Finset.mem_insert_self _ _
    | some R =>
      refine Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ?_)
      obtain ⟨hRmem, hsurf⟩ := hfactor R hijIdx
      obtain ⟨γ, hγ⟩ := hne
      obtain ⟨hz, hdvd⟩ := hsurf γ hγ
      have hRdvd : R ∣ Q₀ :=
        UniqueFactorizationMonoid.dvd_of_mem_factors (Multiset.mem_toFinset.mp hRmem)
      have hRγ0 : R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 := by
        intro hzero
        apply hz
        obtain ⟨c, hc⟩ := hRdvd
        rw [hc, Polynomial.map_mul, hzero, zero_mul]
      have h1le : 1 ≤ (R.map (Polynomial.mapRingHom
          (Polynomial.evalRingHom γ))).natDegree := by
        have hd := Polynomial.natDegree_le_of_dvd hdvd hRγ0
        simpa using hd
      exact Finset.mem_filter.mpr
        ⟨hRmem, le_trans h1le (Polynomial.natDegree_map_le)⟩
  have hIdx'card : Index'.card ≤ gs_degree_bound k n m / (k - 1) + 1 := by
    refine le_trans (Finset.card_le_card hsub') ?_
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h1 := Finset.card_image_le (s := posF) (f := Option.some)
    have h2 : posF.card ≤ Q₀.natDegree := card_posDegree_factors_le h0
    omega
  -- every nonempty cell obeys the `T` bound
  have hcellT : ∀ ij ∈ Index', (Ecell ij).card ≤ T := by
    intro ij hij
    obtain ⟨hijIdx, _⟩ := Finset.mem_filter.mp hij
    cases ij with
    | none => exact le_trans hbadcell hT0
    | some R =>
      obtain ⟨hRmem, hsurf⟩ := hfactor R hijIdx
      have hirr : Irreducible R :=
        UniqueFactorizationMonoid.irreducible_of_factor R (Multiset.mem_toFinset.mp hRmem)
      exact hK4 _ P R hirr (hdec _ hijIdx) (fun γ hγ => (hsurf γ hγ).2)
  -- assemble through the nonempty cells only
  have hcover' : (Finset.univ.filter (fun γ : F₀ =>
      _root_.ProximityGap.mcaEventCurve
        ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ u γ)) ⊆
      Index'.biUnion Ecell := by
    intro γ hγ
    obtain ⟨ij, hij, hγcell⟩ := Finset.mem_biUnion.mp (hcover hγ)
    exact Finset.mem_biUnion.mpr
      ⟨ij, Finset.mem_filter.mpr ⟨hij, ⟨γ, hγcell⟩⟩, hγcell⟩
  calc (Finset.univ.filter (fun γ : F₀ =>
        _root_.ProximityGap.mcaEventCurve
          ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ u γ)).card
      ≤ (Index'.biUnion Ecell).card := Finset.card_le_card hcover'
    _ ≤ ∑ ij ∈ Index', (Ecell ij).card := Finset.card_biUnion_le
    _ ≤ Index'.card * T := by
        have h := Finset.sum_le_card_nsmul Index' (fun ij => (Ecell ij).card) T hcellT
        simpa [smul_eq_mul] using h
    _ ≤ (gs_degree_bound k n m / (k - 1) + 1) * T :=
        Nat.mul_le_mul_right T hIdx'card

/-- **The `L`-ary count with the K4 input in curve-pinning form**: the K4 obligation is
restated through `cell_card_le_of_curve_decode_family_pinning` — what remains is exactly
the existence of the pinning curve past the threshold (the `L`-ary Steps 5–7 capture). -/
theorem bad_card_le_numeric_curve_of_pinning {n k m L : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hT0 : n * (GuruswamiSudan.constraintIndices m).card *
      ((L - 1) * (gs_degree_bound k n m / (k - 1))) ≤ T)
    (hTn : Fintype.card (Fin n) * (L - 1) ≤ T)
    (hpin : ∀ (E : Finset F₀) (P : F₀ → F₀[X]) (R : (F₀[X])[X][Y]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      T < E.card →
      ∃ a : Fin L → F₀[X], (∀ j, (a j).natDegree < k) ∧
        ∀ γ ∈ E, P γ = ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) * a j) :
    (Finset.univ.filter (fun γ : F₀ =>
      _root_.ProximityGap.mcaEventCurve
        ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ u γ)).card ≤
      (gs_degree_bound k n m / (k - 1) + 1) * T := by
  refine bad_card_le_numeric_curve domain u δ T hk1 hkn hm hδ1 hδJ hT0 ?_
  intro E P R hirr hdec hdvd
  exact cell_card_le_of_curve_decode_family_pinning E T P hTn hdec
    (hpin E P R hirr hdec hdvd)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms bad_card_le_numeric_curve
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms bad_card_le_numeric_curve_of_pinning
