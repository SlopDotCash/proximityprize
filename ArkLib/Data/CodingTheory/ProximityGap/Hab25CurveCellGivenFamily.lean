/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveCellProduction
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveCellStrictExtraction

/-!
# Cell cover and heavy-cell attribution for a GIVEN decode family (#304, SK4 brick)

`exists_curve_cell_production` decomposes the bad scalars into cells for a decode family
of its OWN choosing.  The share-form residual (`StrictCoeffPolysShareResidual`) quantifies
over an ARBITRARY decoded family `P`, so the production shape cannot feed it directly.
This file closes that gap at the `McaDecodeCurve` interface:

* `exists_curve_cell_cover_of_given_family` — the cell decomposition for a GIVEN scalar
  set `G` and a GIVEN family `P` witnessed by decodes (`d.P = P γ`): `≤ #factors(Q₀) + 1`
  cells covering `G`, each cell inside `G`, one degenerate cell of size `≤ T`, and a
  single irreducible factor of `Q₀` per remaining cell with
  `(X − C (P γ)) ∣ R|_{Z:=γ}` — for THIS `P`.  The chosen-family production is the special
  case `G := bad`, `P := the chosen decodes`; the proof is the same attribution argument
  (`mcaDecodeCurve_matching_dvd` + prime-into-product factor assignment), with the choice
  step deleted.
* `exists_heavy_factor_cell_of_given_family` — composed with the SK2 pigeonhole
  (`exists_heavy_factor_cell`): whenever `T < |G|`, some irreducible factor `R` of `Q₀`
  carries a `1/#factors(Q₀)` share of `G`:
  `|G| ≤ T + #factors(Q₀)·|G′|` with `G′ ⊆ G` and the per-`γ` divisibility for the GIVEN
  family on all of `G′`.

This is the `∀ P` attribution package the share producer needs: what remains between this
and `StrictCoeffPolysShareResidual` is the per-rich-cell surface supply
(`(Y − C w) ∣ R` with degree bounds — the S10-converse lane), the heavy-coordinate
matching sets, and the `L`-ary Z-degree-bounded interpolant budget for `T`.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open GuruswamiSudan.OverRatFunc
open _root_.ProximityGap Code
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **The cell decomposition for a GIVEN decode family.**  Mirror of
`exists_curve_cell_production` with the scalar set `G` and the decoded family `P` given as
inputs (each `γ ∈ G` witnessed by a decode with `d.P = P γ`): the cells cover `G`, live
inside `G`, the degenerate cell has size `≤ T`, and each factor cell carries one
irreducible factor of `Q₀` dividing at the GIVEN family's values. -/
theorem exists_curve_cell_cover_of_given_family {n k m L : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (curveFold (fun j i => u j i)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hQ₀0 : Q₀ ≠ 0)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hbadz : ∀ S : Finset F₀,
      (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
      S.card ≤ T)
    (G : Finset F₀) (P : F₀ → F₀[X])
    (hPdec : ∀ γ ∈ G, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ) :
    ∃ (Index : Finset (Option ((F₀[X])[X][Y])))
      (Ecell : Option ((F₀[X])[X][Y]) → Finset F₀),
      Index.card ≤ (UniqueFactorizationMonoid.factors Q₀).toFinset.card + 1 ∧
      (∀ γ ∈ G, ∃ ij ∈ Index, γ ∈ Ecell ij) ∧
      (∀ ij, Ecell ij ⊆ G) ∧
      none ∈ Index ∧ (Ecell none).card ≤ T ∧
      (∀ R : (F₀[X])[X][Y], some R ∈ Index →
        R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset ∧
        ∀ γ ∈ Ecell (some R),
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
          (Polynomial.X - Polynomial.C (P γ)) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) := by
  classical
  -- the factor assignment for the non-degenerate scalars, at the GIVEN family
  have hassign : ∀ γ ∈ G,
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 →
      ∃ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
        (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
    intro γ hγ hz
    obtain ⟨d, hd⟩ := hPdec γ hγ
    have hdvd : (Polynomial.X - Polynomial.C (P γ)) ∣
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
      rw [← hd]
      exact mcaDecodeCurve_matching_dvd domain hQ hrep hkn hm hδ1 hδJ d hz
    obtain ⟨R, hRmem, hRd⟩ :=
      exists_integral_factor_assignment_multiset hQ₀0 γ (P γ) hdvd
    exact ⟨R, Multiset.mem_toFinset.mpr hRmem, hRd⟩
  -- the cells: `none` is the degenerate cell, `some R` the factor cells
  have hex2 : ∀ γ : F₀, ∃ ij : Option ((F₀[X])[X][Y]),
      ((γ ∈ G ∧ Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0) →
        ∃ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset, ij = some R ∧
          (Polynomial.X - Polynomial.C (P γ)) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) ∧
      (¬ (γ ∈ G ∧ Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0) →
        ij = none) := by
    intro γ
    by_cases h : γ ∈ G ∧
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0
    · obtain ⟨R, hR, hdvd⟩ := hassign γ h.1 h.2
      exact ⟨some R, fun _ => ⟨R, hR, rfl, hdvd⟩, fun hc => absurd h hc⟩
    · exact ⟨none, fun hc => absurd hc h, fun _ => rfl⟩
  choose assign hassignpos hassignneg using hex2
  set Index : Finset (Option ((F₀[X])[X][Y])) :=
    insert none ((UniqueFactorizationMonoid.factors Q₀).toFinset.image some) with hIndex
  set Ecell : Option ((F₀[X])[X][Y]) → Finset F₀ :=
    fun ij => G.filter (fun γ => assign γ = ij) with hEcell
  refine ⟨Index, Ecell, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- index count
    simp only [hIndex]
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h := Finset.card_image_le
      (s := (UniqueFactorizationMonoid.factors Q₀).toFinset) (f := Option.some)
    omega
  · -- cover
    intro γ hγ
    refine ⟨assign γ, ?_, ?_⟩
    · simp only [hIndex]
      by_cases h : γ ∈ G ∧
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0
      · obtain ⟨R, hR, hEq, _⟩ := hassignpos γ h
        rw [hEq]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hR)
      · rw [hassignneg γ h]
        exact Finset.mem_insert_self _ _
    · exact Finset.mem_filter.mpr ⟨hγ, rfl⟩
  · -- every cell lives inside `G`
    intro ij
    exact Finset.filter_subset _ _
  · -- the degenerate cell is indexed
    simp only [hIndex]
    exact Finset.mem_insert_self _ _
  · -- the degenerate cell is small: its members specialize `Q₀` to zero
    refine hbadz (Ecell none) ?_
    intro γ hγ
    have hγ' : γ ∈ G.filter (fun γ' => assign γ' = none) := hγ
    obtain ⟨hγG, hass⟩ := Finset.mem_filter.mp hγ'
    by_contra hz
    obtain ⟨R, _, hEq, _⟩ := hassignpos γ ⟨hγG, hz⟩
    rw [hass] at hEq
    exact absurd hEq.symm (Option.some_ne_none _)
  · -- every factor cell carries its irreducible factor of `Q₀`, nondegenerately
    intro R hRIndex
    simp only [hIndex, Finset.mem_insert] at hRIndex
    rcases hRIndex with h | h
    · exact absurd h (Option.some_ne_none R)
    · obtain ⟨R', hR', hEq⟩ := Finset.mem_image.mp h
      obtain rfl : R' = R := Option.some.inj hEq
      refine ⟨hR', ?_⟩
      intro γ hγ
      have hγ' : γ ∈ G.filter (fun γ' => assign γ' = some R') := hγ
      obtain ⟨hγG, hass⟩ := Finset.mem_filter.mp hγ'
      by_cases hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0
      · obtain ⟨R'', hR'', hEq2, hdvd⟩ := hassignpos γ ⟨hγG, hz⟩
        rw [hass] at hEq2
        exact ⟨hz, by rwa [← Option.some.inj hEq2] at hdvd⟩
      · rw [hassignneg γ (fun hc => hz hc.2)] at hass
        exact absurd hass.symm (Option.some_ne_none _)

omit [DecidableEq F₀] in
/-- Instance-free (membership-form) wrapper of the SK2 cell pigeonhole
`exists_heavy_factor_cell`. -/
theorem exists_heavy_factor_cell_mem {Idx : Type} (G : Finset F₀)
    (Index : Finset (Option Idx)) (Ecell : Option Idx → Finset F₀) {ℓ T : ℕ}
    (hIdx : Index.card ≤ ℓ + 1) (hnone : none ∈ Index)
    (hcover : ∀ γ ∈ G, ∃ ij ∈ Index, γ ∈ Ecell ij)
    (hnoneCard : (Ecell none).card ≤ T) (hbig : T < G.card) :
    ∃ R : Idx, some R ∈ Index ∧ G.card ≤ T + ℓ * (Ecell (some R)).card := by
  classical
  refine BCIKS20.CurveCellStrictExtraction.exists_heavy_factor_cell G Index Ecell
    hIdx hnone ?_ hnoneCard hbig
  intro γ hγ
  obtain ⟨ij, h1, h2⟩ := hcover γ hγ
  exact Finset.mem_biUnion.mpr ⟨ij, h1, h2⟩

/-- **The heavy-cell attribution for a GIVEN decode family** (the `∀ P` share package):
whenever `T < |G|`, some irreducible factor `R` of `Q₀` carries a `1/#factors(Q₀)` share
of `G` — a subset `G′ ⊆ G` with `|G| ≤ T + #factors(Q₀)·|G′|` on which the GIVEN family
divides `R`'s specializations.  This is exactly the input shape of the SK1/SK2 strict
extraction (`strict_coeffPolys_of_cell`) and the conclusion shape of
`StrictCoeffPolysShareResidual` (share `ℓ = #factors(Q₀)`, budget `T`). -/
theorem exists_heavy_factor_cell_of_given_family {n k m L : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (curveFold (fun j i => u j i)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hQ₀0 : Q₀ ≠ 0)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hbadz : ∀ S : Finset F₀,
      (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
      S.card ≤ T)
    (G : Finset F₀) (P : F₀ → F₀[X])
    (hPdec : ∀ γ ∈ G, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ)
    (hbig : T < G.card) :
    ∃ R : (F₀[X])[X][Y],
      R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset ∧
      Irreducible R ∧
      ∃ G' : Finset F₀,
        G' ⊆ G ∧
        G.card ≤ T + (UniqueFactorizationMonoid.factors Q₀).toFinset.card * G'.card ∧
        ∀ γ ∈ G',
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
          (Polynomial.X - Polynomial.C (P γ)) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
  classical
  obtain ⟨Index, Ecell, hcardI, hcover, hsubG, hnone, hbadcell, hfactor⟩ :=
    exists_curve_cell_cover_of_given_family domain u δ T hQ hrep hQ₀0 hkn hm hδ1 hδJ
      hbadz G P hPdec
  obtain ⟨R, hRIdx, hRcount⟩ :=
    exists_heavy_factor_cell_mem G Index Ecell hcardI hnone hcover hbadcell hbig
  obtain ⟨hRmem, hRdvd⟩ := hfactor R hRIdx
  exact ⟨R, hRmem,
    UniqueFactorizationMonoid.irreducible_of_factor R
      (Multiset.mem_toFinset.mp hRmem),
    Ecell (some R), hsubG _, hRcount, hRdvd⟩

/-- **Given-family heavy cell + global branch ⇒ strict coefficient-polynomial share.**
This is the direct SK4-to-SK1 weld: SK4 supplies one heavy factor cell for the given
decode family `P`; if the selected factor carries the global `branchOfCurveTuple` divisor
and the selected cell has the fold-agreement mass required by SK1, then that share already
carries the coefficient-polynomial family demanded by the Prop-5.5/share surface.

The theorem deliberately keeps the branch construction, heavy-coordinate supplier, and
degenerate-budget producer as hypotheses. -/
theorem strict_coeffPolys_of_given_family_heavy_global_branch {n k m L : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    (hk : 0 < k) (hL : 0 < L) (hLk : L - 1 ≤ k)
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (curveFold (fun j i => u j i)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hQ₀0 : Q₀ ≠ 0)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hbadz : ∀ S : Finset F₀,
      (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
      S.card ≤ T)
    (G : Finset F₀) (P : F₀ → F₀[X])
    (hPdec : ∀ γ ∈ G, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ)
    (hbig : T < G.card)
    (Tset : (F₀[X])[X][Y] → Finset (Fin n))
    (hTcard : ∀ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      (Tset R).card = k)
    (hbranch : ∀ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      (Polynomial.X - Polynomial.C
        (branchOfCurveTuple (fun j : Fin L => lagrangeCurveTuple domain u (Tset R) j))) ∣
          R)
    (hEbig : ∀ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      ∀ E : Finset F₀, E ⊆ G →
        (∀ γ ∈ E,
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
            (Polynomial.X - Polynomial.C (P γ)) ∣
              R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
        max (L - 1) k < E.card)
    (hagree : ∀ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      ∀ E : Finset F₀, E ⊆ G →
        (∀ γ ∈ E,
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
            (Polynomial.X - Polynomial.C (P γ)) ∣
              R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
        ∀ t ∈ Tset R, ∀ z ∈ E,
          (P z).eval (domain t) = (foldSectionAt u t).eval z) :
    ∃ G' : Finset F₀,
      G' ⊆ G ∧
      G.card ≤ T + (UniqueFactorizationMonoid.factors Q₀).toFinset.card * G'.card ∧
      ∃ B : ℕ → F₀[X],
        (∀ j, (B j).natDegree < k + 1) ∧
        ∀ γ ∈ G', ∀ j, (P γ).coeff j = (B j).eval γ := by
  classical
  obtain ⟨R, hRmem, hRirr, G', hG'sub, hcount, hRdvd⟩ :=
    exists_heavy_factor_cell_of_given_family domain u δ T hQ hrep hQ₀0 hkn hm hδ1 hδJ
      hbadz G P hPdec hbig
  let w : F₀[X][Y] :=
    branchOfCurveTuple (fun j : Fin L => lagrangeCurveTuple domain u (Tset R) j)
  have hwdvd : (Polynomial.X - Polynomial.C w) ∣ R := by
    simpa [w] using hbranch R hRmem
  have hB : ∀ i, (w.coeff i).natDegree ≤ L - 1 := by
    intro i
    have h := branchOfCurveTuple_coeff_natDegree_lt hL
      (fun j : Fin L => lagrangeCurveTuple domain u (Tset R) j) i
    simp [w] at h ⊢
    omega
  have hwdeg : w.natDegree < (Tset R).card := by
    have ha : ∀ j : Fin L,
        (lagrangeCurveTuple domain u (Tset R) j).natDegree < k := fun j =>
      lagrangeCurveTuple_natDegree_lt hk domain u (hTcard R hRmem) j
    have hpHat := branchOfCurveTuple_natDegree_lt hk ha
    rw [hTcard R hRmem]
    simpa [w] using hpHat
  obtain ⟨B, hBdeg, hBmatch⟩ :=
    BCIKS20.CurveCellStrictExtraction.strict_coeffPolys_of_cell
      (domain := domain) (u := u) hRirr hwdvd hLk hB G' P
      (fun γ hγ => (hRdvd γ hγ).2) (Tset R) hwdeg
      (fun _t => G') (fun _t _ht => subset_rfl)
      (fun _t _ht => hEbig R hRmem G' hG'sub hRdvd)
      (fun t ht z hz => hagree R hRmem G' hG'sub hRdvd t ht z hz)
  exact ⟨G', hG'sub, hcount, B, hBdeg, hBmatch⟩

/-- **Given-family heavy cell + coordinate upgrade ⇒ strict coefficient-polynomial share.**
This packages the next layer above `strict_coeffPolys_of_given_family_heavy_global_branch`:
once SK4 chooses the heavy factor cell, a `CoordinateUpgrade` on that selected cell supplies
both the global `branchOfCurveTuple` divisor (via `global_branch_of_coordinate_upgrade`) and
the fold-section agreement shape (via `foldSectionAt_eval`).  The remaining hypotheses are
exactly the numeric size/budget conditions needed for those two steps. -/
theorem strict_coeffPolys_of_given_family_coordinate_upgrade {n k m L : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    (hk : 0 < k) (hL : 0 < L) (hLk : L - 1 ≤ k)
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (curveFold (fun j i => u j i)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hQ₀0 : Q₀ ≠ 0)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hbadz : ∀ S : Finset F₀,
      (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
      S.card ≤ T)
    (G : Finset F₀) (P : F₀ → F₀[X])
    (hPdec : ∀ γ ∈ G, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ)
    (hbig : T < G.card)
    (Tset : (F₀[X])[X][Y] → Finset (Fin n))
    (hTcard : ∀ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      (Tset R).card = k)
    (BR : (F₀[X])[X][Y] → ℕ)
    (hRB : ∀ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      ∀ b a : ℕ, ((R.coeff b).coeff a).natDegree ≤ BR R)
    (hbranchBig : ∀ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      ∀ E : Finset F₀, E ⊆ G →
        (∀ γ ∈ E,
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
            (Polynomial.X - Polynomial.C (P γ)) ∣
              R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
        BR R + R.natDegree * (L - 1) < E.card)
    (hEbig : ∀ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      ∀ E : Finset F₀, E ⊆ G →
        (∀ γ ∈ E,
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
            (Polynomial.X - Polynomial.C (P γ)) ∣
              R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
        max (L - 1) k < E.card)
    (hUpgrade : ∀ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      ∀ E : Finset F₀, E ⊆ G →
        (∀ γ ∈ E,
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
            (Polynomial.X - Polynomial.C (P γ)) ∣
              R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
        CoordinateUpgrade domain u E P (Tset R)) :
    ∃ G' : Finset F₀,
      G' ⊆ G ∧
      G.card ≤ T + (UniqueFactorizationMonoid.factors Q₀).toFinset.card * G'.card ∧
      ∃ B : ℕ → F₀[X],
        (∀ j, (B j).natDegree < k + 1) ∧
        ∀ γ ∈ G', ∀ j, (P γ).coeff j = (B j).eval γ := by
  classical
  obtain ⟨R, hRmem, hRirr, G', hG'sub, hcount, hRdvd⟩ :=
    exists_heavy_factor_cell_of_given_family domain u δ T hQ hrep hQ₀0 hkn hm hδ1 hδJ
      hbadz G P hPdec hbig
  have hdegP : ∀ γ ∈ G', (P γ).degree < (k : ℕ) := by
    intro γ hγ
    obtain ⟨d, hd⟩ := hPdec γ (hG'sub hγ)
    rw [← hd]
    exact d.hdeg
  have hupg : CoordinateUpgrade domain u G' P (Tset R) :=
    hUpgrade R hRmem G' hG'sub hRdvd
  let w : F₀[X][Y] :=
    branchOfCurveTuple (fun j : Fin L => lagrangeCurveTuple domain u (Tset R) j)
  have hwdvd : (Polynomial.X - Polynomial.C w) ∣ R := by
    simpa [w] using global_branch_of_coordinate_upgrade hk hL R (hRB R hRmem) G' P
      (Tset R) (hTcard R hRmem) hdegP (fun γ hγ => (hRdvd γ hγ).2) hupg
      (hbranchBig R hRmem G' hG'sub hRdvd)
  have hB : ∀ i, (w.coeff i).natDegree ≤ L - 1 := by
    intro i
    have h := branchOfCurveTuple_coeff_natDegree_lt hL
      (fun j : Fin L => lagrangeCurveTuple domain u (Tset R) j) i
    simp [w] at h ⊢
    omega
  have hwdeg : w.natDegree < (Tset R).card := by
    have ha : ∀ j : Fin L,
        (lagrangeCurveTuple domain u (Tset R) j).natDegree < k := fun j =>
      lagrangeCurveTuple_natDegree_lt hk domain u (hTcard R hRmem) j
    have hpHat := branchOfCurveTuple_natDegree_lt hk ha
    rw [hTcard R hRmem]
    simpa [w] using hpHat
  have hagree : ∀ t ∈ Tset R, ∀ z ∈ G',
      (P z).eval (domain t) = (foldSectionAt u t).eval z := by
    intro t ht z hz
    rw [foldSectionAt_eval]
    exact hupg z hz t ht
  obtain ⟨B, hBdeg, hBmatch⟩ :=
    BCIKS20.CurveCellStrictExtraction.strict_coeffPolys_of_cell
      (domain := domain) (u := u) hRirr hwdvd hLk hB G' P
      (fun γ hγ => (hRdvd γ hγ).2) (Tset R) hwdeg
      (fun _t => G') (fun _t _ht => subset_rfl)
      (fun _t _ht => hEbig R hRmem G' hG'sub hRdvd)
      (fun t ht z hz => hagree t ht z hz)
  exact ⟨G', hG'sub, hcount, B, hBdeg, hBmatch⟩

/-- **Given-family coordinate-upgrade extraction with the sharp fold-degree bound.**
This is the `deg(B j) < L` variant of
`strict_coeffPolys_of_given_family_coordinate_upgrade`.  It follows the same SK4 selected
heavy cell, but invokes `strict_coeffPolys_of_cell_degree_lt_L`, so the coefficient
polynomials are bounded by the fold length instead of the decoded RS degree. -/
theorem strict_coeffPolys_of_given_family_coordinate_upgrade_degree_lt_L {n k m L : ℕ}
    [NeZero n]
    (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    (hk : 0 < k) (hL : 0 < L)
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (curveFold (fun j i => u j i)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hQ₀0 : Q₀ ≠ 0)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hbadz : ∀ S : Finset F₀,
      (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
      S.card ≤ T)
    (G : Finset F₀) (P : F₀ → F₀[X])
    (hPdec : ∀ γ ∈ G, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ)
    (hbig : T < G.card)
    (Tset : (F₀[X])[X][Y] → Finset (Fin n))
    (hTcard : ∀ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      (Tset R).card = k)
    (BR : (F₀[X])[X][Y] → ℕ)
    (hRB : ∀ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      ∀ b a : ℕ, ((R.coeff b).coeff a).natDegree ≤ BR R)
    (hbranchBig : ∀ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      ∀ E : Finset F₀, E ⊆ G →
        (∀ γ ∈ E,
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
            (Polynomial.X - Polynomial.C (P γ)) ∣
              R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
        BR R + R.natDegree * (L - 1) < E.card)
    (hEbig : ∀ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      ∀ E : Finset F₀, E ⊆ G →
        (∀ γ ∈ E,
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
            (Polynomial.X - Polynomial.C (P γ)) ∣
              R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
        max (L - 1) k < E.card)
    (hUpgrade : ∀ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      ∀ E : Finset F₀, E ⊆ G →
        (∀ γ ∈ E,
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
            (Polynomial.X - Polynomial.C (P γ)) ∣
              R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
        CoordinateUpgrade domain u E P (Tset R)) :
    ∃ G' : Finset F₀,
      G' ⊆ G ∧
      G.card ≤ T + (UniqueFactorizationMonoid.factors Q₀).toFinset.card * G'.card ∧
      ∃ B : ℕ → F₀[X],
        (∀ j, (B j).natDegree < L) ∧
        ∀ γ ∈ G', ∀ j, (P γ).coeff j = (B j).eval γ := by
  classical
  obtain ⟨R, hRmem, hRirr, G', hG'sub, hcount, hRdvd⟩ :=
    exists_heavy_factor_cell_of_given_family domain u δ T hQ hrep hQ₀0 hkn hm hδ1 hδJ
      hbadz G P hPdec hbig
  have hdegP : ∀ γ ∈ G', (P γ).degree < (k : ℕ) := by
    intro γ hγ
    obtain ⟨d, hd⟩ := hPdec γ (hG'sub hγ)
    rw [← hd]
    exact d.hdeg
  have hupg : CoordinateUpgrade domain u G' P (Tset R) :=
    hUpgrade R hRmem G' hG'sub hRdvd
  let w : F₀[X][Y] :=
    branchOfCurveTuple (fun j : Fin L => lagrangeCurveTuple domain u (Tset R) j)
  have hwdvd : (Polynomial.X - Polynomial.C w) ∣ R := by
    simpa [w] using global_branch_of_coordinate_upgrade hk hL R (hRB R hRmem) G' P
      (Tset R) (hTcard R hRmem) hdegP (fun γ hγ => (hRdvd γ hγ).2) hupg
      (hbranchBig R hRmem G' hG'sub hRdvd)
  have hB : ∀ i, (w.coeff i).natDegree ≤ L - 1 := by
    intro i
    have h := branchOfCurveTuple_coeff_natDegree_lt hL
      (fun j : Fin L => lagrangeCurveTuple domain u (Tset R) j) i
    simp [w] at h ⊢
    omega
  have hwdeg : w.natDegree < (Tset R).card := by
    have ha : ∀ j : Fin L,
        (lagrangeCurveTuple domain u (Tset R) j).natDegree < k := fun j =>
      lagrangeCurveTuple_natDegree_lt hk domain u (hTcard R hRmem) j
    have hpHat := branchOfCurveTuple_natDegree_lt hk ha
    rw [hTcard R hRmem]
    simpa [w] using hpHat
  have hagree : ∀ t ∈ Tset R, ∀ z ∈ G',
      (P z).eval (domain t) = (foldSectionAt u t).eval z := by
    intro t ht z hz
    rw [foldSectionAt_eval]
    exact hupg z hz t ht
  obtain ⟨B, hBdeg, hBmatch⟩ :=
    BCIKS20.CurveCellStrictExtraction.strict_coeffPolys_of_cell_degree_lt_L
      (domain := domain) (u := u) hL hRirr hwdvd hB G' P
      (fun γ hγ => (hRdvd γ hγ).2) (Tset R) hwdeg
      (fun _t => G') (fun _t _ht => subset_rfl)
      (fun _t _ht => by
        have hcell := hEbig R hRmem G' hG'sub hRdvd
        have hLcell : L - 1 < G'.card :=
          lt_of_le_of_lt (Nat.le_max_left (L - 1) k) hcell
        simpa [max_self] using hLcell)
      (fun t ht z hz => hagree t ht z hz)
  exact ⟨G', hG'sub, hcount, B, hBdeg, hBmatch⟩

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_curve_cell_cover_of_given_family
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_heavy_factor_cell_mem
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_heavy_factor_cell_of_given_family
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms strict_coeffPolys_of_given_family_heavy_global_branch
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms strict_coeffPolys_of_given_family_coordinate_upgrade
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms strict_coeffPolys_of_given_family_coordinate_upgrade_degree_lt_L
