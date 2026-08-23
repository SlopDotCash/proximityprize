/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSCellProduction
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonCountWiring
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureKernelUD
import ArkLib.Data.CodingTheory.ProximityGap.Hab25AffineCapture
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSInterpolantZDegreeTight
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonBoundRealLower
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Bundle

/-!
# Cells to dichotomy bundles — the GS production wired into the Johnson endgame

`exists_cell_production_total` (in-tree, no production hypothesis) decomposes each word
stack's bad scalars into a degenerate cell (explicitly bounded) plus per-irreducible-factor
cells with uniform decode families.  This file converts that cell structure into a
`Hab25JohnsonDichotomyData` bundle — the residual shape of the dichotomy funnel — given
exactly one per-cell input: **each factor cell is small or admits an improving affine
pair** ([Hab25] Claim 1, the K4/Hensel dichotomy).

The degenerate cell takes the small branch outright (its explicit bound is below the
threshold `T` by hypothesis); factor cells take whichever branch the per-cell input
provides.  The bundle's proven counting theorem (`disagree_card_le`) then bounds the
stack's bad scalars by `ℓ · max T n` with `ℓ = |Index|` — narrowing the dichotomy-funnel
obligation of `Hab25JohnsonDischarge` to the per-cell Hensel dichotomy in the cell
vocabulary the GS lane actually produces.

## References

* [Hab25] U. Haböck, *A note on mutual correlated agreement for Reed–Solomon codes*,
  ePrint 2025/2110.
* [BCIKS20] ePrint 2020/654, §5 (Claim 5.7 cells; Steps 5–7 dichotomy).
-/

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open Polynomial Polynomial.Bivariate GuruswamiSudan.OverRatFunc
open _root_.ProximityGap Code
open scoped NNReal ENNReal

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

open Classical in
/-- **Cells to dichotomy bundle.**  The in-tree cell production, together with the
per-factor-cell dichotomy (small or improving pair — [Hab25] Claim 1), yields a
`Hab25JohnsonDichotomyData` bundle whose disagreement set is exactly the stack's bad
scalars and whose threshold is `T`. -/
theorem exists_dichotomyData_of_cell_improvement
    {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (η δ : ℝ≥0) (hη : 0 < η) (hδr : InJohnsonRange domain k η δ)
    (u : WordStack F₀ (Fin 2) (Fin n))
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (T : ℕ)
    (hT : n * (GuruswamiSudan.constraintIndices m).card * gs_degree_bound k n m ≤ T)
    (himpr : ∀ (R : (F₀[X])[X][Y]) (E : Finset F₀) (P : F₀ → F₀[X]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T ∨ ∃ d₀ d₁ : Fin n → F₀, ∀ z ∈ E,
        ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0) :
    ∃ A : Hab25JohnsonDichotomyData domain k η δ hη hδr,
      A.Edis = Finset.univ.filter (fun γ : F₀ =>
        mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ (u 0) (u 1) γ) ∧
      A.T = T := by
  obtain ⟨Q₀, Index, Ecell, P, hQ₀, hcard, hcover, hdecode, hnone, hnonecard, hfactor⟩ :=
    exists_cell_production_total domain u δ hk1 hkn hm hδ1 hδJ
  refine ⟨⟨Option ((F₀[X])[X][Y]), inferInstance, Index, Index.card, T,
    le_refl _,
    Finset.univ.filter (fun γ : F₀ =>
      mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ (u 0) (u 1) γ),
    Ecell, hcover, ?_⟩, rfl, rfl⟩
  intro ij hij
  match ij with
  | none =>
      exact Or.inl (le_trans hnonecard hT)
  | some R =>
      obtain ⟨hRfac, hRdata⟩ := hfactor R hij
      have hRirr : Irreducible R :=
        UniqueFactorizationMonoid.irreducible_of_factor R
          (Multiset.mem_toFinset.mp hRfac)
      exact himpr R (Ecell (some R)) P hRirr
        (fun γ hγ => hdecode (some R) hij γ hγ)
        (fun γ hγ => (hRdata γ hγ).2)

open Classical in
/-- **The per-stack count from cells.**  Under the per-cell dichotomy, the stack's bad
scalars are bounded by `ℓ · max T n` for the bundle produced from the cell structure —
the dichotomy counting theorem instantiated at the GS cells. -/
theorem badCount_le_of_cell_improvement
    {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (η δ : ℝ≥0) (hη : 0 < η) (hδr : InJohnsonRange domain k η δ)
    (u : WordStack F₀ (Fin 2) (Fin n))
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (T : ℕ)
    (hT : n * (GuruswamiSudan.constraintIndices m).card * gs_degree_bound k n m ≤ T)
    (himpr : ∀ (R : (F₀[X])[X][Y]) (E : Finset F₀) (P : F₀ → F₀[X]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T ∨ ∃ d₀ d₁ : Fin n → F₀, ∀ z ∈ E,
        ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0) :
    ∃ ℓ : ℕ,
      (Finset.univ.filter (fun γ : F₀ =>
        mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ (u 0) (u 1) γ)).card
        ≤ ℓ * max T (Fintype.card (Fin n)) := by
  obtain ⟨A, hEdis, hAT⟩ := exists_dichotomyData_of_cell_improvement domain η δ hη hδr u
    hk1 hkn hm hδ1 hδJ T hT himpr
  refine ⟨A.ℓ, ?_⟩
  have h := A.disagree_card_le
  rw [hEdis, hAT] at h
  exact h

/-- **The per-cell dichotomy, discharged on the 3-intersection window.**  On
`2·n + k ≤ 3·t` the per-cell input of `exists_dichotomyData_of_cell_improvement` holds
outright: singleton cells take the small branch (`T ≥ 1`); cells with two or more scalars
are affinely pinned by the antecedent-free window pencil
(`exists_pencil_of_decode_family_window`), each member is then affine-captured at the
pencil pair (`McaDecode.affineCaptured`), and capture yields the improvement
(`affineCaptured_improve`) at the uniform difference words. -/
theorem cell_improvement_of_window
    {n k : ℕ} [NeZero n] {domain : Fin n ↪ F₀} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} (hk : 0 < k)
    (hwin : 2 * Fintype.card (Fin n) + k
      ≤ 3 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊)
    {T : ℕ} (hT : 1 ≤ T) :
    ∀ (R : (F₀[X])[X][Y]) (E : Finset F₀) (P : F₀ → F₀[X]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T ∨ ∃ d₀ d₁ : Fin n → F₀, ∀ z ∈ E,
        ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0 := by
  intro R E P _ hdec _
  by_cases h2 : 1 < E.card
  · right
    obtain ⟨v₀, v₁, hd0, hd1, hPaff⟩ :=
      exists_pencil_of_decode_family_window hk E P hdec hwin h2
    refine ⟨fun i => v₀.eval (domain i) - u 0 i,
      fun i => v₁.eval (domain i) - u 1 i, fun z hz => ?_⟩
    obtain ⟨d, hdP⟩ := hdec z hz
    have hcap : AffineCaptured domain k δ u z (v₀, v₁) :=
      d.affineCaptured (by rw [hdP]; exact hPaff z hz)
    exact affineCaptured_improve hd0 hd1 hcap
  · exact Or.inl (le_trans (by omega) hT)

open Classical in
/-- **The dichotomy bundle on the window, hypothesis-free.**  On the 3-intersection
window, every word stack admits a `Hab25JohnsonDichotomyData` bundle from the in-tree GS
cell production — the full [BCIKS20] §5 pipeline (interpolation → cells → pencil →
capture → improvement) executed end-to-end with no production hypothesis. -/
theorem exists_dichotomyData_of_window
    {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (η δ : ℝ≥0) (hη : 0 < η) (hδr : InJohnsonRange domain k η δ)
    (u : WordStack F₀ (Fin 2) (Fin n))
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hwin : 2 * Fintype.card (Fin n) + k
      ≤ 3 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊)
    (T : ℕ) (hT1 : 1 ≤ T)
    (hT : n * (GuruswamiSudan.constraintIndices m).card * gs_degree_bound k n m ≤ T) :
    ∃ A : Hab25JohnsonDichotomyData domain k η δ hη hδr,
      A.Edis = Finset.univ.filter (fun γ : F₀ =>
        mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ (u 0) (u 1) γ) ∧
      A.T = T :=
  exists_dichotomyData_of_cell_improvement domain η δ hη hδr u hk1 hkn hm hδ1 hδJ T hT
    (cell_improvement_of_window (lt_trans Nat.zero_lt_one hk1) hwin hT1)

/-- **K4 smallness on the window.**  On the 3-intersection window, every decode-family
cell is small outright (`≤ n ≤ T`): a pinned cell's members are all affine-captured at
the window pencil, so the cell embeds in an improving set, which `factorImprove_card_le_n`
bounds by `n`.  This discharges the `hK4` input of `bad_card_le_numeric`. -/
theorem hK4_of_window
    {n k : ℕ} [NeZero n] {domain : Fin n ↪ F₀} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} (hk : 0 < k)
    (hwin : 2 * Fintype.card (Fin n) + k
      ≤ 3 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊)
    {T : ℕ} (hTn : n ≤ T) :
    ∀ (E : Finset F₀) (P : F₀ → F₀[X]) (R : (F₀[X])[X][Y]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T := by
  intro E P R _ hdec _
  by_cases h2 : 1 < E.card
  · obtain ⟨v₀, v₁, hd0, hd1, hPaff⟩ :=
      exists_pencil_of_decode_family_window hk E P hdec hwin h2
    have himp : ∀ z ∈ E,
        ∃ x ∈ disagreeSet (fun i => v₀.eval (domain i) - u 0 i)
          (fun i => v₁.eval (domain i) - u 1 i),
        affineGap (fun i => v₀.eval (domain i) - u 0 i)
          (fun i => v₁.eval (domain i) - u 1 i) z x = 0 := by
      intro z hz
      obtain ⟨d, hdP⟩ := hdec z hz
      exact affineCaptured_improve hd0 hd1
        (d.affineCaptured (by rw [hdP]; exact hPaff z hz))
    have hcard := factorImprove_card_le_n
      (fun i => v₀.eval (domain i) - u 0 i)
      (fun i => v₁.eval (domain i) - u 1 i) E himp
    exact le_trans (by simpa using hcard) hTn
  · have h1 : E.card ≤ 1 := by omega
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    omega

open Classical in
/-- **The uniform per-stack numeric count on the window** — `bad_card_le_numeric` with its
`hK4` input discharged by the window pencil: every stack's bad scalars number at most
`(D/(k-1) + 1) · T`, with no production hypothesis. -/
theorem bad_card_le_numeric_of_window
    {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin 2) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hwin : 2 * Fintype.card (Fin n) + k
      ≤ 3 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊)
    (hTn : n ≤ T)
    (hT0 : n * (GuruswamiSudan.constraintIndices m).card * gs_degree_bound k n m ≤ T) :
    (Finset.univ.filter (fun γ : F₀ =>
      mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
        δ (u 0) (u 1) γ)).card ≤
      (gs_degree_bound k n m / (k - 1) + 1) * T :=
  bad_card_le_numeric domain u δ T hk1 hkn hm hδ1 hδJ hT0
    (fun E P R hR hdec hdvd =>
      hK4_of_window (lt_trans Nat.zero_lt_one hk1) hwin hTn E P R hR hdec hdvd)

open Classical in
/-- **The window numeric instance via the full pipeline.**  On the 3-intersection window,
`JohnsonNumericBound` holds through the complete GS machinery — interpolation, cells,
pencil, capture, count — with the explicit budget `B = (D/(k-1)+1)·T`, given only the
arithmetic side condition `B/|F| ≤ johnsonBoundReal`. -/
theorem johnsonNumericBound_of_window_numeric
    {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (η δ : ℝ≥0) (T : ℕ)
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hwin : 2 * Fintype.card (Fin n) + k
      ≤ 3 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊)
    (hTn : n ≤ T)
    (hT0 : n * (GuruswamiSudan.constraintIndices m).card * gs_degree_bound k n m ≤ T)
    (harith : (((gs_degree_bound k n m / (k - 1) + 1) * T : ℕ) : ℝ≥0∞)
        / (Fintype.card F₀ : ℝ≥0∞)
      ≤ ENNReal.ofReal (johnsonBoundReal domain k η δ)) :
    JohnsonNumericBound domain k η δ :=
  johnsonNumericBound_of_badCount_le domain k η δ
    ((gs_degree_bound k n m / (k - 1) + 1) * T)
    (fun u => bad_card_le_numeric_of_window domain u δ T hk1 hkn hm hδ1 hδJ hwin hTn hT0)
    harith


open Classical in
/-- **The total cell production at the tight Z-degree budget** — `exists_cell_production`
fed by the tight producer (`gs_existence_over_ratfunc_zDegree_card_div`): identical cell
structure, degenerate budget improved to `n·|c|·(D/(k-1))` (linear in `n`), the constant
the Johnson arithmetic can absorb. -/
theorem exists_cell_production_total_div {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin 2) (Fin n)) (δ : ℝ≥0)
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m) :
    ∃ (Q₀ : (F₀[X])[X][Y]) (Index : Finset (Option ((F₀[X])[X][Y])))
      (Ecell : Option ((F₀[X])[X][Y]) → Finset F₀) (P : F₀ → F₀[X]),
      Q₀ ≠ 0 ∧
      Index.card ≤ (UniqueFactorizationMonoid.factors Q₀).toFinset.card + 1 ∧
      (Finset.univ.filter (fun γ : F₀ =>
        mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
          δ (u 0) (u 1) γ)) ⊆ Index.biUnion Ecell ∧
      (∀ ij ∈ Index, ∀ γ ∈ Ecell ij,
        ∃ d : McaDecode domain k δ u γ, d.P = P γ) ∧
      none ∈ Index ∧
      (Ecell none).card ≤
        n * (GuruswamiSudan.constraintIndices m).card * (gs_degree_bound k n m / (k - 1)) ∧
      (∀ R : (F₀[X])[X][Y], some R ∈ Index →
        R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset ∧
        ∀ γ ∈ Ecell (some R),
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
          (Polynomial.X - Polynomial.C (P γ)) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) := by
  obtain ⟨Q₀, h0, hcond, hcard⟩ :=
    GuruswamiSudan.OverRatFunc.ZDegree.gs_existence_over_ratfunc_zDegree_card_div
      (F := F₀) k m domain (u 0) (u 1) hk1 (NeZero.ne n) hm
  have hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) (1 : F₀[X]))) *
        Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) := by
    simp
  obtain ⟨Index, Ecell, P, h1, h2, h3, h4, h5, h6⟩ :=
    exists_cell_production domain u δ
      (n * (GuruswamiSudan.constraintIndices m).card * (gs_degree_bound k n m / (k - 1)))
      hcond hrep h0 hkn hm hδ1 hδJ (degenerate_card_bound_of_filter hcard)
  exact ⟨Q₀, Index, Ecell, P, h0, h1, h2, h3, h4, h5, h6⟩

open Classical in
/-- **The dichotomy bundle on the window at the tight budget** — `T` need only dominate
`n·|c|·(D/(k-1))` (and `1`), the scale the Johnson arithmetic absorbs. -/
theorem exists_dichotomyData_of_window_div
    {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (η δ : ℝ≥0) (hη : 0 < η) (hδr : InJohnsonRange domain k η δ)
    (u : WordStack F₀ (Fin 2) (Fin n))
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hwin : 2 * Fintype.card (Fin n) + k
      ≤ 3 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊)
    (T : ℕ) (hT1 : 1 ≤ T)
    (hT : n * (GuruswamiSudan.constraintIndices m).card
      * (gs_degree_bound k n m / (k - 1)) ≤ T) :
    ∃ A : Hab25JohnsonDichotomyData domain k η δ hη hδr,
      A.Edis = Finset.univ.filter (fun γ : F₀ =>
        mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ (u 0) (u 1) γ) ∧
      A.T = T := by
  obtain ⟨Q₀, Index, Ecell, P, hQ₀, hcard, hcover, hdecode, hnone, hnonecard, hfactor⟩ :=
    exists_cell_production_total_div domain u δ hk1 hkn hm hδ1 hδJ
  refine ⟨⟨Option ((F₀[X])[X][Y]), inferInstance, Index, Index.card, T,
    le_refl _,
    Finset.univ.filter (fun γ : F₀ =>
      mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ (u 0) (u 1) γ),
    Ecell, hcover, ?_⟩, rfl, rfl⟩
  intro ij hij
  match ij with
  | none =>
      exact Or.inl (le_trans hnonecard hT)
  | some R =>
      obtain ⟨hRfac, hRdata⟩ := hfactor R hij
      have hRirr : Irreducible R :=
        UniqueFactorizationMonoid.irreducible_of_factor R
          (Multiset.mem_toFinset.mp hRfac)
      exact cell_improvement_of_window (lt_trans Nat.zero_lt_one hk1) hwin hT1
        R (Ecell (some R)) P hRirr
        (fun γ hγ => hdecode (some R) hij γ hγ)
        (fun γ hγ => (hRdata γ hγ).2)


open Classical in
/-- **The tight uniform numeric count on the window.**  Every stack's bad scalars number
at most `(D/(k-1) + 1) · T` with `T` at the tight degenerate budget: the factor cells are
small by the window pencil (`hK4_of_window`), the degenerate cell by the tight Z-degree
budget, and the live index is bounded by the interpolant's `Y`-degree `D/(k-1)` (positive-
degree distinct factors, `card_posDegree_factors_le`) plus one. -/
theorem badCount_le_numeric_tight_of_window
    {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin 2) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hwin : 2 * Fintype.card (Fin n) + k
      ≤ 3 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊)
    (hTn : n ≤ T)
    (hT : n * (GuruswamiSudan.constraintIndices m).card
      * (gs_degree_bound k n m / (k - 1)) ≤ T) :
    (Finset.univ.filter (fun γ : F₀ =>
      mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
        δ (u 0) (u 1) γ)).card
      ≤ (gs_degree_bound k n m / (k - 1) + 1) * T := by
  classical
  obtain ⟨Q₀, h0, hcond, hcard⟩ :=
    GuruswamiSudan.OverRatFunc.ZDegree.gs_existence_over_ratfunc_zDegree_card_div
      (F := F₀) k m domain (u 0) (u 1) hk1 (NeZero.ne n) hm
  have hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) (1 : F₀[X]))) *
        Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) := by
    simp
  obtain ⟨Index, Ecell, P, hIdx, hcover, hdec, hnone, hnonecard, hfactor⟩ :=
    exists_cell_production domain u δ
      (n * (GuruswamiSudan.constraintIndices m).card * (gs_degree_bound k n m / (k - 1)))
      hcond hrep h0 hkn hm hδ1 hδJ (degenerate_card_bound_of_filter hcard)
  -- the interpolant's Y-degree is at most `D/(k-1)`
  have hφinj : Function.Injective
      (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) :=
    Polynomial.map_injective _ (IsFractionRing.injective F₀[X] (RatFunc F₀))
  have hydeg : Q₀.natDegree ≤ gs_degree_bound k n m / (k - 1) := by
    have hnat : Polynomial.Bivariate.natWeightedDegree
        (Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀)))) 1 (k - 1)
        ≤ gs_degree_bound k n m := by
      have h := hcond.Q_deg
      rw [Polynomial.Bivariate.weightedDegree_eq_natWeightedDegree] at h
      exact_mod_cast h
    have h1 := GuruswamiSudan.natDegree_le_of_natWeightedDegree (by omega) hnat
    rwa [Polynomial.natDegree_map_eq_of_injective hφinj] at h1
  -- the live index: degenerate cell plus nonempty factor cells
  set Index' : Finset (Option ((F₀[X])[X][Y])) :=
    Index.filter (fun ij => ij = none ∨ (Ecell ij).Nonempty) with hI'
  have hcover' : (Finset.univ.filter (fun γ : F₀ =>
      mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
        δ (u 0) (u 1) γ)) ⊆ Index'.biUnion Ecell := by
    intro γ hγ
    obtain ⟨ij, hij, hγcell⟩ := Finset.mem_biUnion.mp (hcover hγ)
    exact Finset.mem_biUnion.mpr
      ⟨ij, Finset.mem_filter.mpr ⟨hij, Or.inr ⟨γ, hγcell⟩⟩, hγcell⟩
  have hI'card : Index'.card ≤ gs_degree_bound k n m / (k - 1) + 1 := by
    have hsub : Index' ⊆ insert none
        (((UniqueFactorizationMonoid.factors Q₀).toFinset.filter
          (fun q => 1 ≤ q.natDegree)).image some) := by
      intro ij hij
      obtain ⟨hijIdx, hcase⟩ := Finset.mem_filter.mp hij
      match ij with
      | none => exact Finset.mem_insert_self _ _
      | some R =>
        rcases hcase with h | hne
        · exact absurd h (by simp)
        · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨R, ?_, rfl⟩)
          obtain ⟨hRfac, hRdata⟩ := hfactor R hijIdx
          refine Finset.mem_filter.mpr ⟨hRfac, ?_⟩
          obtain ⟨γ, hγ⟩ := hne
          obtain ⟨hQγ, hdvdγ⟩ := hRdata γ hγ
          have hRdvd : R ∣ Q₀ :=
            UniqueFactorizationMonoid.dvd_of_mem_factors (Multiset.mem_toFinset.mp hRfac)
          have hRγ0 : R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 := by
            intro habs
            obtain ⟨S, hS⟩ := hRdvd
            apply hQγ
            rw [hS, Polynomial.map_mul, habs, zero_mul]
          have h1 := Polynomial.natDegree_le_of_dvd hdvdγ hRγ0
          rw [Polynomial.natDegree_X_sub_C] at h1
          exact le_trans h1 (Polynomial.natDegree_map_le)
    calc Index'.card
        ≤ (insert none
            (((UniqueFactorizationMonoid.factors Q₀).toFinset.filter
              (fun q => 1 ≤ q.natDegree)).image some)).card :=
          Finset.card_le_card hsub
      _ ≤ (((UniqueFactorizationMonoid.factors Q₀).toFinset.filter
              (fun q => 1 ≤ q.natDegree)).image some).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ ((UniqueFactorizationMonoid.factors Q₀).toFinset.filter
              (fun q => 1 ≤ q.natDegree)).card + 1 :=
          Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ Q₀.natDegree + 1 := Nat.add_le_add_right (card_posDegree_factors_le h0) 1
      _ ≤ gs_degree_bound k n m / (k - 1) + 1 := Nat.add_le_add_right hydeg 1
  -- every live cell is small
  have hcell : ∀ ij ∈ Index', (Ecell ij).card ≤ T := by
    intro ij hij
    have hijIdx := (Finset.mem_filter.mp hij).1
    match ij with
    | none => exact le_trans hnonecard hT
    | some R =>
        obtain ⟨hRfac, hRdata⟩ := hfactor R hijIdx
        have hRirr : Irreducible R :=
          UniqueFactorizationMonoid.irreducible_of_factor R
            (Multiset.mem_toFinset.mp hRfac)
        exact hK4_of_window (lt_trans Nat.zero_lt_one hk1) hwin hTn
          (Ecell (some R)) P R hRirr
          (fun γ hγ => hdec (some R) hijIdx γ hγ)
          (fun γ hγ => (hRdata γ hγ).2)
  calc (Finset.univ.filter (fun γ : F₀ =>
        mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
          δ (u 0) (u 1) γ)).card
      ≤ (Index'.biUnion Ecell).card := Finset.card_le_card hcover'
    _ ≤ ∑ ij ∈ Index', (Ecell ij).card := Finset.card_biUnion_le
    _ ≤ ∑ _ij ∈ Index', T := Finset.sum_le_sum hcell
    _ = Index'.card * T := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (gs_degree_bound k n m / (k - 1) + 1) * T := Nat.mul_le_mul_right T hI'card

open Classical in
/-- **The tight window numeric edge.**  `JohnsonNumericBound` through the complete GS
machinery at the satisfiable budget `B = (D/(k-1)+1)·T` with `T` at the tight degenerate
scale — the day-25 sweep places `B/|F|` inside `johnsonBoundReal` at every scale. -/
theorem johnsonNumericBound_of_window_numeric_tight
    {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (η δ : ℝ≥0) (T : ℕ)
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hwin : 2 * Fintype.card (Fin n) + k
      ≤ 3 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊)
    (hTn : n ≤ T)
    (hT : n * (GuruswamiSudan.constraintIndices m).card
      * (gs_degree_bound k n m / (k - 1)) ≤ T)
    (harith : (((gs_degree_bound k n m / (k - 1) + 1) * T : ℕ) : ℝ≥0∞)
        / (Fintype.card F₀ : ℝ≥0∞)
      ≤ ENNReal.ofReal (johnsonBoundReal domain k η δ)) :
    JohnsonNumericBound domain k η δ :=
  johnsonNumericBound_of_badCount_le domain k η δ
    ((gs_degree_bound k n m / (k - 1) + 1) * T)
    (fun u => badCount_le_numeric_tight_of_window domain u δ T hk1 hkn hm hδ1 hδJ
      hwin hTn hT)
    harith


open Classical in
/-- **The window instance, fully closed.**  On the 3-intersection window with `2 ≤ k`,
`k + 1 ≤ n`, and multiplicity `12 ≤ m` below the Johnson multiplicity, the numeric edge
holds with NO side conditions: the count comes from the complete GS pipeline at the tight
budget, and the arithmetic from `harith_tight_closed`. -/
theorem johnsonNumericBound_of_window_closed
    {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀) (η δ : ℝ≥0)
    (hk2 : 2 ≤ k) (hkn : k + 1 ≤ n) (hm12 : 12 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hwin : 2 * Fintype.card (Fin n) + k
      ≤ 3 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊)
    (hmle : (m : ℝ) ≤
      max (⌈((((k : ℝ) / Fintype.card (Fin n) + 1 / Fintype.card (Fin n)))
          ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3) :
    JohnsonNumericBound domain k η δ := by
  have hk1 : 1 < k := lt_of_lt_of_le one_lt_two hk2
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm12
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  refine johnsonNumericBound_of_window_numeric_tight domain η δ
    (max (n * (GuruswamiSudan.constraintIndices m).card
      * (gs_degree_bound k n m / (k - 1))) n)
    hk1 (by omega) hm1 hδ1 hδJ hwin (le_max_right _ _) (le_max_left _ _) ?_
  have h := ProximityGapArithWrapper.harith_tight_closed domain k m η δ hk2
    (by rw [hcard]; omega) hm12 (by rw [hcard] at hmle ⊢; exact hmle)
  rw [hcard] at h
  exact h


open Classical in
/-- **The tight numeric count from the per-cell disjunct** — day-22's dichotomy route
merged with day-28's live-index bound: under `himpr` (small-or-improving, the
[Hab25] Claim 1 shape), every stack's bad scalars number at most
`(D/(k-1)+1) · max T n`. -/
theorem badCount_le_numeric_tight_of_himpr
    {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin 2) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hT0 : n * (GuruswamiSudan.constraintIndices m).card
      * (gs_degree_bound k n m / (k - 1)) ≤ T)
    (himpr : ∀ (R : (F₀[X])[X][Y]) (E : Finset F₀) (P : F₀ → F₀[X]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T ∨ ∃ d₀ d₁ : Fin n → F₀, ∀ z ∈ E,
        ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0) :
    (Finset.univ.filter (fun γ : F₀ =>
      mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
        δ (u 0) (u 1) γ)).card
      ≤ (gs_degree_bound k n m / (k - 1) + 1) * max T (Fintype.card (Fin n)) := by
  classical
  obtain ⟨Q₀, h0, hcond, hcard⟩ :=
    GuruswamiSudan.OverRatFunc.ZDegree.gs_existence_over_ratfunc_zDegree_card_div
      (F := F₀) k m domain (u 0) (u 1) hk1 (NeZero.ne n) hm
  have hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) (1 : F₀[X]))) *
        Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) := by
    simp
  obtain ⟨Index, Ecell, P, hIdx, hcover, hdec, hnone, hnonecard, hfactor⟩ :=
    exists_cell_production domain u δ
      (n * (GuruswamiSudan.constraintIndices m).card * (gs_degree_bound k n m / (k - 1)))
      hcond hrep h0 hkn hm hδ1 hδJ (degenerate_card_bound_of_filter hcard)
  have hφinj : Function.Injective
      (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) :=
    Polynomial.map_injective _ (IsFractionRing.injective F₀[X] (RatFunc F₀))
  have hydeg : Q₀.natDegree ≤ gs_degree_bound k n m / (k - 1) := by
    have hnat : Polynomial.Bivariate.natWeightedDegree
        (Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀)))) 1 (k - 1)
        ≤ gs_degree_bound k n m := by
      have h := hcond.Q_deg
      rw [Polynomial.Bivariate.weightedDegree_eq_natWeightedDegree] at h
      exact_mod_cast h
    have h1 := GuruswamiSudan.natDegree_le_of_natWeightedDegree (by omega) hnat
    rwa [Polynomial.natDegree_map_eq_of_injective hφinj] at h1
  set Index' : Finset (Option ((F₀[X])[X][Y])) :=
    Index.filter (fun ij => ij = none ∨ (Ecell ij).Nonempty) with hI'
  have hcover' : (Finset.univ.filter (fun γ : F₀ =>
      mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
        δ (u 0) (u 1) γ)) ⊆ Index'.biUnion Ecell := by
    intro γ hγ
    obtain ⟨ij, hij, hγcell⟩ := Finset.mem_biUnion.mp (hcover hγ)
    exact Finset.mem_biUnion.mpr
      ⟨ij, Finset.mem_filter.mpr ⟨hij, Or.inr ⟨γ, hγcell⟩⟩, hγcell⟩
  have hI'card : Index'.card ≤ gs_degree_bound k n m / (k - 1) + 1 := by
    have hsub : Index' ⊆ insert none
        (((UniqueFactorizationMonoid.factors Q₀).toFinset.filter
          (fun q => 1 ≤ q.natDegree)).image some) := by
      intro ij hij
      obtain ⟨hijIdx, hcase⟩ := Finset.mem_filter.mp hij
      match ij with
      | none => exact Finset.mem_insert_self _ _
      | some R =>
        rcases hcase with h | hne
        · exact absurd h (by simp)
        · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨R, ?_, rfl⟩)
          obtain ⟨hRfac, hRdata⟩ := hfactor R hijIdx
          refine Finset.mem_filter.mpr ⟨hRfac, ?_⟩
          obtain ⟨γ, hγ⟩ := hne
          obtain ⟨hQγ, hdvdγ⟩ := hRdata γ hγ
          have hRdvd : R ∣ Q₀ :=
            UniqueFactorizationMonoid.dvd_of_mem_factors (Multiset.mem_toFinset.mp hRfac)
          have hRγ0 : R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 := by
            intro habs
            obtain ⟨S, hS⟩ := hRdvd
            apply hQγ
            rw [hS, Polynomial.map_mul, habs, zero_mul]
          have h1 := Polynomial.natDegree_le_of_dvd hdvdγ hRγ0
          rw [Polynomial.natDegree_X_sub_C] at h1
          exact le_trans h1 (Polynomial.natDegree_map_le)
    calc Index'.card
        ≤ (insert none
            (((UniqueFactorizationMonoid.factors Q₀).toFinset.filter
              (fun q => 1 ≤ q.natDegree)).image some)).card :=
          Finset.card_le_card hsub
      _ ≤ (((UniqueFactorizationMonoid.factors Q₀).toFinset.filter
              (fun q => 1 ≤ q.natDegree)).image some).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ ((UniqueFactorizationMonoid.factors Q₀).toFinset.filter
              (fun q => 1 ≤ q.natDegree)).card + 1 :=
          Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ Q₀.natDegree + 1 := Nat.add_le_add_right (card_posDegree_factors_le h0) 1
      _ ≤ gs_degree_bound k n m / (k - 1) + 1 := Nat.add_le_add_right hydeg 1
  have hcell : ∀ ij ∈ Index', (Ecell ij).card ≤ max T (Fintype.card (Fin n)) := by
    intro ij hij
    have hijIdx := (Finset.mem_filter.mp hij).1
    match ij with
    | none => exact le_trans (le_trans hnonecard hT0) (le_max_left _ _)
    | some R =>
        obtain ⟨hRfac, hRdata⟩ := hfactor R hijIdx
        have hRirr : Irreducible R :=
          UniqueFactorizationMonoid.irreducible_of_factor R
            (Multiset.mem_toFinset.mp hRfac)
        rcases himpr R (Ecell (some R)) P hRirr
          (fun γ hγ => hdec (some R) hijIdx γ hγ)
          (fun γ hγ => (hRdata γ hγ).2) with hsmall | ⟨d₀, d₁, himp⟩
        · exact le_trans hsmall (le_max_left _ _)
        · exact le_trans (factorImprove_card_le_n d₀ d₁ (Ecell (some R)) himp)
            (le_max_right _ _)
  calc (Finset.univ.filter (fun γ : F₀ =>
        mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
          δ (u 0) (u 1) γ)).card
      ≤ (Index'.biUnion Ecell).card := Finset.card_le_card hcover'
    _ ≤ ∑ ij ∈ Index', (Ecell ij).card := Finset.card_biUnion_le
    _ ≤ ∑ _ij ∈ Index', max T (Fintype.card (Fin n)) := Finset.sum_le_sum hcell
    _ = Index'.card * max T (Fintype.card (Fin n)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (gs_degree_bound k n m / (k - 1) + 1) * max T (Fintype.card (Fin n)) :=
        Nat.mul_le_mul_right _ hI'card

open Classical in
/-- **Per-pair factor data from the GS cells.**  The in-tree GS cell production already
provides the factor index family, cover, decode family, degenerate cell, and per-factor
divisibility surface.  Given the single remaining per-cell small-or-improving disjunct
(`himpr`), this packages those cells into the current `PerPairFactorData` consumer shape
with the tight live-index bound `D/(k-1)+1`. -/
theorem exists_perPairFactorData_of_cell_improvement
    {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin 2) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hT0 : n * (GuruswamiSudan.constraintIndices m).card
      * (gs_degree_bound k n m / (k - 1)) ≤ T)
    (himpr : ∀ (R : (F₀[X])[X][Y]) (E : Finset F₀) (P : F₀ → F₀[X]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T ∨ ∃ d₀ d₁ : Fin n → F₀, ∀ z ∈ E,
        ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0) :
    Nonempty (BCIKS20.Claim510Bundle.PerPairFactorData domain k δ u
      (gs_degree_bound k n m / (k - 1) + 1) T) := by
  classical
  obtain ⟨Q₀, h0, hcond, hcard⟩ :=
    GuruswamiSudan.OverRatFunc.ZDegree.gs_existence_over_ratfunc_zDegree_card_div
      (F := F₀) k m domain (u 0) (u 1) hk1 (NeZero.ne n) hm
  have hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) (1 : F₀[X]))) *
        Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) := by
    simp
  obtain ⟨Index, Ecell, P, _hIdx, hcover, hdec, _hnone, hnonecard, hfactor⟩ :=
    exists_cell_production domain u δ
      (n * (GuruswamiSudan.constraintIndices m).card * (gs_degree_bound k n m / (k - 1)))
      hcond hrep h0 hkn hm hδ1 hδJ (degenerate_card_bound_of_filter hcard)
  have hφinj : Function.Injective
      (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) :=
    Polynomial.map_injective _ (IsFractionRing.injective F₀[X] (RatFunc F₀))
  have hydeg : Q₀.natDegree ≤ gs_degree_bound k n m / (k - 1) := by
    have hnat : Polynomial.Bivariate.natWeightedDegree
        (Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀)))) 1 (k - 1)
        ≤ gs_degree_bound k n m := by
      have h := hcond.Q_deg
      rw [Polynomial.Bivariate.weightedDegree_eq_natWeightedDegree] at h
      exact_mod_cast h
    have h1 := GuruswamiSudan.natDegree_le_of_natWeightedDegree (by omega) hnat
    rwa [Polynomial.natDegree_map_eq_of_injective hφinj] at h1
  set Index' : Finset (Option ((F₀[X])[X][Y])) :=
    Index.filter (fun ij => ij = none ∨ (Ecell ij).Nonempty) with hI'
  have hcover' : (Finset.univ.filter (fun γ : F₀ =>
      mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀)))
        δ (u 0) (u 1) γ)) ⊆ Index'.biUnion Ecell := by
    intro γ hγ
    obtain ⟨ij, hij, hγcell⟩ := Finset.mem_biUnion.mp (hcover hγ)
    exact Finset.mem_biUnion.mpr
      ⟨ij, Finset.mem_filter.mpr ⟨hij, Or.inr ⟨γ, hγcell⟩⟩, hγcell⟩
  have hI'card : Index'.card ≤ gs_degree_bound k n m / (k - 1) + 1 := by
    have hsub : Index' ⊆ insert none
        (((UniqueFactorizationMonoid.factors Q₀).toFinset.filter
          (fun q => 1 ≤ q.natDegree)).image some) := by
      intro ij hij
      obtain ⟨hijIdx, hcase⟩ := Finset.mem_filter.mp hij
      match ij with
      | none => exact Finset.mem_insert_self _ _
      | some R =>
        rcases hcase with h | hne
        · exact absurd h (by simp)
        · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨R, ?_, rfl⟩)
          obtain ⟨hRfac, hRdata⟩ := hfactor R hijIdx
          refine Finset.mem_filter.mpr ⟨hRfac, ?_⟩
          obtain ⟨γ, hγ⟩ := hne
          obtain ⟨hQγ, hdvdγ⟩ := hRdata γ hγ
          have hRdvd : R ∣ Q₀ :=
            UniqueFactorizationMonoid.dvd_of_mem_factors (Multiset.mem_toFinset.mp hRfac)
          have hRγ0 : R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 := by
            intro habs
            obtain ⟨S, hS⟩ := hRdvd
            apply hQγ
            rw [hS, Polynomial.map_mul, habs, zero_mul]
          have h1 := Polynomial.natDegree_le_of_dvd hdvdγ hRγ0
          rw [Polynomial.natDegree_X_sub_C] at h1
          exact le_trans h1 (Polynomial.natDegree_map_le)
    calc Index'.card
        ≤ (insert none
            (((UniqueFactorizationMonoid.factors Q₀).toFinset.filter
              (fun q => 1 ≤ q.natDegree)).image some)).card :=
          Finset.card_le_card hsub
      _ ≤ (((UniqueFactorizationMonoid.factors Q₀).toFinset.filter
              (fun q => 1 ≤ q.natDegree)).image some).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ ((UniqueFactorizationMonoid.factors Q₀).toFinset.filter
              (fun q => 1 ≤ q.natDegree)).card + 1 :=
          Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ Q₀.natDegree + 1 := Nat.add_le_add_right (card_posDegree_factors_le h0) 1
      _ ≤ gs_degree_bound k n m / (k - 1) + 1 := Nat.add_le_add_right hydeg 1
  refine ⟨⟨Option ((F₀[X])[X][Y]), inferInstance, Index', hI'card, Ecell, hcover', ?_⟩⟩
  intro ij hij
  have hijIdx := (Finset.mem_filter.mp hij).1
  match ij with
  | none =>
      exact Or.inl (le_trans hnonecard hT0)
  | some R =>
      obtain ⟨hRfac, hRdata⟩ := hfactor R hijIdx
      have hRirr : Irreducible R :=
        UniqueFactorizationMonoid.irreducible_of_factor R
          (Multiset.mem_toFinset.mp hRfac)
      exact himpr R (Ecell (some R)) P hRirr
        (fun γ hγ => hdec (some R) hijIdx γ hγ)
        (fun γ hγ => (hRdata γ hγ).2)

open Classical in
/-- **The gate-shaped conditional.**  Modulo the single per-cell disjunct production
(the [BCIKS20] Claim 5.7 assembly), the numeric edge holds at the canonical tight
parameters with the arithmetic fully discharged — the unconditional
`johnsonNumericBound_holds` is this theorem with `himpr` replaced by the assembly. -/
theorem johnsonNumericBound_holds_of_himpr
    {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀) (η δ : ℝ≥0)
    (hk2 : 2 ≤ k) (hkn : k + 1 ≤ n) (hm12 : 12 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hmle : (m : ℝ) ≤
      max (⌈((((k : ℝ) / Fintype.card (Fin n) + 1 / Fintype.card (Fin n)))
          ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3)
    (himpr : ∀ (u : WordStack F₀ (Fin 2) (Fin n))
      (R : (F₀[X])[X][Y]) (E : Finset F₀) (P : F₀ → F₀[X]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ max (n * (GuruswamiSudan.constraintIndices m).card
          * (gs_degree_bound k n m / (k - 1))) n
        ∨ ∃ d₀ d₁ : Fin n → F₀, ∀ z ∈ E,
          ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0) :
    JohnsonNumericBound domain k η δ := by
  have hk1 : 1 < k := lt_of_lt_of_le one_lt_two hk2
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm12
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  set T : ℕ := max (n * (GuruswamiSudan.constraintIndices m).card
    * (gs_degree_bound k n m / (k - 1))) n with hTdef
  refine johnsonNumericBound_of_badCount_le domain k η δ
    ((gs_degree_bound k n m / (k - 1) + 1) * T) (fun u => ?_) ?_
  · have h := badCount_le_numeric_tight_of_himpr domain u δ T hk1 (by omega) hm1
      hδ1 hδJ (le_max_left _ _) (himpr u)
    have hTn : max T (Fintype.card (Fin n)) = T := by
      rw [max_eq_left]
      rw [hcard]
      exact le_max_right _ _
    rwa [hTn] at h
  · have h := ProximityGapArithWrapper.harith_tight_closed domain k m η δ hk2
      (by rw [hcard]; omega) hm12 (by rw [hcard] at hmle ⊢; exact hmle)
    rw [hcard] at h
    exact h

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.exists_dichotomyData_of_cell_improvement
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.badCount_le_of_cell_improvement
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.cell_improvement_of_window
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.exists_dichotomyData_of_window
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.hK4_of_window
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.bad_card_le_numeric_of_window
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_window_numeric
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.exists_cell_production_total_div
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.exists_dichotomyData_of_window_div
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.badCount_le_numeric_tight_of_window
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_window_numeric_tight
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_window_closed
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.badCount_le_numeric_tight_of_himpr
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.exists_perPairFactorData_of_cell_improvement
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_holds_of_himpr
