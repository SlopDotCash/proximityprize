/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveBudgetDischarge

/-!
# The uniform `(ℓ, T)` share budget (#304, the bookkeeping brick closed)

`exists_heavy_factor_cell_on_decoded_set_budgeted` exposed the share `ℓ` as
`#factors(Q₀)` — interpolant-dependent, so unusable as a parameter of a single
`StrictCoeffPolysResidualShare ℓ T` instance.  This file makes both constants uniform:

* `card_posYDegree_factors_le` — distinct irreducible factors of positive `Y`-degree
  number at most `deg_Y Q₀`: their product divides `Q₀` (distinct factors divide the
  factors-product, associated to `Q₀`), and degrees add;
* every CATCHING factor has `deg_Y ≥ 1` (its specialization is nonzero and divisible by
  the monic linear `X − C (P γ)`), so restricting the pigeonhole to the nonempty cells
  bounds the share by `deg_Y Q₀ ≤ gs_degree_bound k n m` (the producer's new
  `Q₀.natDegree` leg);
* **`exists_heavy_factor_cell_uniform`** — the capstone: under `¬ jointAgreement` and
  the Johnson-radius hypotheses, any decoded family on a scalar set beating the explicit
  budget `B = n·|constraintIndices m|·(gs_degree_bound·(L−1))` admits an irreducible `R`
  and `G′ ⊆ G` with
  `|G| ≤ B + gs_degree_bound·|G′|` — share and budget BOTH explicit in `(n, k, m, L)`
  alone.  This is exactly the `(ℓ, T) = (gs_degree_bound k n m, B)` instance shape of
  `StrictCoeffPolysResidualShare`.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open GuruswamiSudan GuruswamiSudan.OverRatFunc GuruswamiSudan.OverRatFunc.ZDegree
open _root_.ProximityGap Code
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

noncomputable local instance poly3DecidableEq : DecidableEq ((F₀[X])[X][Y]) :=
  Classical.decEq _

/-- **Distinct positive-degree irreducible factors are at most `deg_Y`-many**: their
product divides the factors-product (distinct elements of the multiset), which is
associated to `Q₀`, and degrees add over the product. -/
theorem card_posYDegree_factors_le {R : Type} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [decEq : DecidableEq (Polynomial R)]
    {Q₀ : Polynomial R} (hQ₀ : Q₀ ≠ 0) :
    ((UniqueFactorizationMonoid.factors Q₀).toFinset.filter
      (fun S => 1 ≤ S.natDegree)).card ≤ Q₀.natDegree := by
  classical
  set Cat := (UniqueFactorizationMonoid.factors Q₀).toFinset.filter
    (fun S => 1 ≤ S.natDegree) with hCat
  have hne : ∀ S ∈ Cat, S ≠ 0 := by
    intro S hS
    exact (UniqueFactorizationMonoid.irreducible_of_factor S
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hS).1)).ne_zero
  have hdvd : (∏ S ∈ Cat, S) ∣ Q₀ := by
    have h1 : (∏ S ∈ Cat, S) ∣
        ∏ S ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset, S :=
      Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    have h2 : (∏ S ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset, S) ∣
        (UniqueFactorizationMonoid.factors Q₀).prod := by
      simpa using Multiset.toFinset_prod_dvd_prod
        (UniqueFactorizationMonoid.factors Q₀)
    exact h1.trans (h2.trans
      (UniqueFactorizationMonoid.factors_prod hQ₀).dvd)
  have hprod0 : (∏ S ∈ Cat, S) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  calc Cat.card = ∑ _S ∈ Cat, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ S ∈ Cat, S.natDegree :=
        Finset.sum_le_sum (fun S hS => (Finset.mem_filter.mp hS).2)
    _ = (∏ S ∈ Cat, S).natDegree := (Polynomial.natDegree_prod _ _ hne).symm
    _ ≤ Q₀.natDegree := Polynomial.natDegree_le_of_dvd hdvd hQ₀

/-- A catching factor has positive `Y`-degree: its specialization is nonzero and
divisible by the monic linear `X − C p`. -/
theorem one_le_natDegree_of_catching {R : (F₀[X])[X][Y]} {γ : F₀} {p : F₀[X]}
    (hz : R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0)
    (hdvd : (Polynomial.X - Polynomial.C p) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) :
    1 ≤ R.natDegree := by
  by_contra h
  push Not at h
  interval_cases hR : R.natDegree
  · -- R is a Y-constant; its map is a Y-constant, divisible by a degree-1 monic
    have hC := Polynomial.natDegree_eq_zero.mp hR
    obtain ⟨c, hc⟩ := hC
    rw [← hc, Polynomial.map_C] at hz hdvd
    have hdeg := Polynomial.natDegree_le_of_dvd hdvd hz
    rw [Polynomial.natDegree_C] at hdeg
    have hmonic : (Polynomial.X - Polynomial.C p).Monic := Polynomial.monic_X_sub_C p
    have : (Polynomial.X - Polynomial.C p).natDegree = 1 := Polynomial.natDegree_X_sub_C p
    omega

set_option backward.isDefEq.respectTransparency false in
/-- **The uniform `(ℓ, T)` heavy-cell attribution (#304, bookkeeping brick closed).**
Share and budget both explicit in `(n, k, m, L)`:
`ℓ = gs_degree_bound k n m`, `T = n·|constraintIndices m|·(gs_degree_bound·(L−1))`. -/
theorem exists_heavy_factor_cell_uniform {n k m L : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0)
    (hk2 : 2 ≤ k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (G : Finset F₀) (P : F₀ → F₀[X])
    (hP : ∀ γ ∈ G, (P γ).natDegree < k ∧
      δᵣ(∑ j : Fin L, (γ ^ (j : ℕ)) • u j, (P γ).eval ∘ domain) ≤ δ)
    (hnja : ¬ jointAgreement
      (C := (ReedSolomon.code domain k : Set (Fin n → F₀))) (δ := δ) (W := u))
    (hbig : (n * (constraintIndices m).card) * (gs_degree_bound k n m * (L - 1)) <
      G.card) :
    ∃ R : (F₀[X])[X][Y],
      Irreducible R ∧
      ∃ G' : Finset F₀,
        G' ⊆ G ∧
        G.card ≤
          (n * (constraintIndices m).card) * (gs_degree_bound k n m * (L - 1)) +
          gs_degree_bound k n m * G'.card ∧
        ∀ γ ∈ G',
          (Polynomial.X - Polynomial.C (P γ)) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
  classical
  -- the producer with the Y-degree leg
  obtain ⟨Q₀, hQ₀0, hcond, hYdeg, hbadz⟩ :=
    gs_existence_curve_zDegree_badz (F := F₀) (n := n) (L := L) k m domain
      (fun j i => u j i) (by omega) (NeZero.ne n) hm
  have hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) (1 : F₀[X]))) *
        (Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀)))) := by
    rw [map_one, Polynomial.C_1, Polynomial.C_1, one_mul]
  set B : ℕ := (n * (constraintIndices m).card) * (gs_degree_bound k n m * (L - 1))
    with hB
  -- the ∀P cell cover at the explicit budget
  obtain ⟨Index, Ecell, hcardI, hcover, hsubG, hnone, hbadcell, hfactor⟩ :=
    exists_curve_cell_cover_of_given_family domain u δ B hcond hrep hQ₀0 hkn hm
      hδ1 hδJ hbadz G P (fun γ hγ =>
        exists_mcaDecodeCurve_of_close_of_not_jointAgreement domain u δ γ (P γ)
          (hP γ hγ).1 (hP γ hγ).2 hnja)
  -- restrict to the catching cells: the `none` cell plus the nonempty factor cells
  set Index' : Finset (Option ((F₀[X])[X][Y])) :=
    Index.filter (fun ij => ij = none ∨ (Ecell ij).Nonempty) with hIndex'
  set Cat : Finset ((F₀[X])[X][Y]) :=
    (UniqueFactorizationMonoid.factors Q₀).toFinset.filter
      (fun S => 1 ≤ S.natDegree) with hCatdef
  -- every nonempty factor cell's factor is catching, hence in `Cat`
  have hCatmem : ∀ R : (F₀[X])[X][Y], some R ∈ Index' → R ∈ Cat ∨ (Ecell (some R)) = ∅ := by
    intro R hR
    obtain ⟨hRIdx, hRor⟩ := Finset.mem_filter.mp hR
    rcases hRor with h | ⟨γ, hγ⟩
    · exact absurd h (Option.some_ne_none R)
    · obtain ⟨hRmem, hRdvd⟩ := hfactor R hRIdx
      have hRfac : R ∈ UniqueFactorizationMonoid.factors Q₀ := by
        simpa only [Multiset.mem_toFinset] using hRmem
      obtain ⟨hz, hdvd⟩ := hRdvd γ hγ
      have hzR : R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 := by
        intro h0
        obtain ⟨c, hc⟩ := Multiset.dvd_prod hRfac
        apply hz
        have hQdvd : R ∣ Q₀ :=
          dvd_trans (Multiset.dvd_prod hRfac)
            (UniqueFactorizationMonoid.factors_prod hQ₀0).dvd
        obtain ⟨c', hc'⟩ := hQdvd
        rw [hc', Polynomial.map_mul, h0, zero_mul]
      have hdvdR : (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := hdvd
      exact Or.inl (Finset.mem_filter.mpr
        ⟨by simpa only [Multiset.mem_toFinset] using hRfac,
          one_le_natDegree_of_catching hzR hdvdR⟩)
  -- |Index'| ≤ |Cat| + 1 via the injection some⁻¹ into `Cat` (empty cells dropped below)
  -- run the pigeonhole on the SUB-index of genuinely nonempty cells
  have hcover' : ∀ γ ∈ G, ∃ ij ∈ Index', γ ∈ Ecell ij := by
    intro γ hγ
    obtain ⟨ij, hij, hmem⟩ := hcover γ hγ
    exact ⟨ij, Finset.mem_filter.mpr ⟨hij, Or.inr ⟨γ, hmem⟩⟩, hmem⟩
  have hnone' : none ∈ Index' :=
    Finset.mem_filter.mpr ⟨hnone, Or.inl rfl⟩
  have hIdx' : Index'.card ≤ Cat.card + 1 := by
    have hsub : Index' ⊆ insert none (Cat.image some) := by
      intro ij hij
      cases ij with
      | none => exact Finset.mem_insert_self _ _
      | some R =>
        rcases hCatmem R hij with hC | hE
        · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hC)
        · -- empty cell with `some R ∈ Index'` contradicts the filter
          obtain ⟨-, hRor⟩ := Finset.mem_filter.mp hij
          rcases hRor with h | hne
          · exact absurd h (Option.some_ne_none R)
          · rw [hE] at hne
            exact absurd hne (by simp)
    refine (Finset.card_le_card hsub).trans ?_
    refine (Finset.card_insert_le _ _).trans ?_
    have := Finset.card_image_le (s := Cat) (f := Option.some)
    omega
  obtain ⟨R, hRIdx', hRcount⟩ :=
    exists_heavy_factor_cell_mem (ℓ := Cat.card) G Index' Ecell hIdx' hnone'
      hcover' hbadcell hbig
  -- the heavy factor's data
  have hRIdx : some R ∈ Index := (Finset.mem_filter.mp hRIdx').1
  obtain ⟨hRmem, hRdvd⟩ := hfactor R hRIdx
  have hRfac : R ∈ UniqueFactorizationMonoid.factors Q₀ := by
    simpa only [Multiset.mem_toFinset] using hRmem
  -- the catching count is at most the Y-degree, which is at most the degree bound
  have hCatle : Cat.card ≤ gs_degree_bound k n m :=
    le_trans (by
      simpa only [hCatdef] using
        card_posYDegree_factors_le (decEq := poly3DecidableEq) hQ₀0) hYdeg
  refine ⟨R, UniqueFactorizationMonoid.irreducible_of_factor R
    hRfac, Ecell (some R), hsubG _, ?_, ?_⟩
  · calc G.card ≤ B + Cat.card * (Ecell (some R)).card := hRcount
      _ ≤ B + gs_degree_bound k n m * (Ecell (some R)).card :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hCatle) _
  · intro γ hγ
    exact (hRdvd γ hγ).2

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms card_posYDegree_factors_le
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms one_le_natDegree_of_catching
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_heavy_factor_cell_uniform
