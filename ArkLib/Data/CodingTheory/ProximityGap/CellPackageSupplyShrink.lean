/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonPackageSupply

/-!
#389 residual `cellpackage-supply`.

Goal: shrink the surface of `CellPackage.ofSurfaceRoot` (the smart constructor of the
Johnson-lane residual `CellPackageSupply`).  The constructor currently takes FOUR legs
that are *identical predicates* to legs already supplied on a larger truncation set:

  hbaseA : ∀ j, ∀ z ∈ matchingSet j, (w.eval (C x₀)).eval z = (root z).1
  hsepA  : ∀ j, ∀ z ∈ matchingSet j, (... separability at z ...)
  hbase₀ : ∀ z ∈ S₀,               (w.eval (C x₀)).eval z = (root z).1
  hsep₀  : ∀ z ∈ S₀,               (... separability at z ...)

while it ALSO takes, over `truncSet ⊇ everything used by the htail truncation chain`:

  hbaseT : ∀ z ∈ truncSet, (w.eval (C x₀)).eval z = (root z).1
  hsepT  : ∀ z ∈ truncSet, (... separability at z ...)

The predicates `hbaseA/hbase₀` vs `hbaseT` are SYNTACTICALLY the same (same `root`), and
likewise `hsepA/hsep₀` vs `hsepT` (same `root`, same `pi_z_xi_ne_zero_of_monic` proof
term).  So if every matching set and the heavy set sit inside `truncSet`, those four legs
are DERIVABLE from `hbaseT/hsepT` by pure membership monotonicity.

This file proves `CellPackage.ofSurfaceRootShared`, a strictly-smaller-surface constructor
that drops `hbaseA, hsepA, hbase₀, hsep₀` in favour of two inclusion hypotheses
`hmatchSub : ∀ j, matchingSet j ⊆ truncSet` and `hS₀sub : S₀ ⊆ truncSet`.  This is a
genuine reduction of the named residual `CellPackageSupply`: a single base/separability
certificate over `truncSet` now feeds the entire package.
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped NNReal ENNReal
open ArkLib

namespace BCIKS20.CellPencilJohnson

variable {F₀ : Type} [Field F₀]

/-- **Shrunk-surface smart constructor.**  Drops the four redundant base/separability legs
on the matching sets and the heavy set (`hbaseA, hsepA, hbase₀, hsep₀`) in favour of two
inclusion hypotheses placing those loci inside `truncSet`; the legs are then derived from
`hbaseT, hsepT` by membership monotonicity.  This strictly reduces the residual surface of
`CellPackageSupply`: one base + one separability certificate over `truncSet` now suffices. -/
noncomputable def CellPackage.ofSurfaceRootShared [Fintype F₀] [DecidableEq F₀] {n : ℕ}
    [NeZero n] {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F₀) (hHyp : Hypotheses x₀ R H) (hmonic : H.Monic)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F₀[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly
      = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
    (root : (z : F₀) → rationalRoot (H_tilde' H) z)
    {w : F₀[X][Y]} (hwdeg : w.natDegree < n)
    (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    {truncSet : Finset F₀}
    (hbaseT : ∀ z ∈ truncSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepT : ∀ z ∈ truncSet,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    {disc : F₀[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F₀, disc.eval z ≠ 0 → z ∈ truncSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F₀)
    (e : Fin n → F₀) (he : Function.Injective e) (u₀ u₁ : Fin n → F₀)
    (matchingSet : Fin n → Finset F₀)
    (hmatchSub : ∀ j, matchingSet j ⊆ truncSet)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    {xw : ℕ}
    (hξw : weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
      (ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ))
    (hcard : ∀ j, BCIKS20.Claim510Supply.killBudget n D H.natDegree
        (Bivariate.natDegreeY R) xw * H.natDegree < (matchingSet j).card)
    (S₀ : Finset F₀)
    (hS₀sub : S₀ ⊆ truncSet)
    {Bw : ℕ} (hBw : ∀ t, ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).natDegree ≤ Bw)
    (hS₀ : max Bw 1 < S₀.card) :
    CellPackage domain k δ u R H :=
  CellPackage.ofSurfaceRoot x₀ hHyp hmonic hD hd2 hdHD hD_Rx0 hRgrade hrepG root
    hwdeg hwdvd hbaseT hsepT hdisc hcover hbig e he u₀ u₁ matchingSet
    -- hbaseA: derive from hbaseT by membership monotonicity
    (fun j z hz => hbaseT z (hmatchSub j hz))
    -- hsepA: derive from hsepT by membership monotonicity
    (fun j z hz => hsepT z (hmatchSub j hz))
    hfold hξw hcard S₀
    -- hbase₀: derive from hbaseT
    (fun z hz => hbaseT z (hS₀sub hz))
    -- hsep₀: derive from hsepT
    (fun z hz => hsepT z (hS₀sub hz))
    hBw hS₀

/-- **Disc-locus smart constructor.**  Canonically takes the truncation set to be the
non-vanishing locus of the discriminant, `Finset.univ.filter (fun z => disc.eval z ≠ 0)`.
The disc-cover leg `hcover` is then DISCHARGED (it is `Finset.mem_filter.mpr`), and the
matching/heavy-set inclusions become the purely-local statement "every matched/heavy place
is a disc-non-vanishing place" — exactly the BCIKS20 §6 discriminant geometry.

This discharges one of `ofSurfaceRoot`'s named hypotheses (`hcover`) entirely and removes
`truncSet` as a free parameter: it is now pinned to the disc geometry.  Combined with the
shared-certificate monotonicity, the residual surface of `CellPackageSupply` shrinks to:
ONE base reading + ONE separability certificate, each over the disc-non-vanishing locus,
plus the locus-membership of the matched/heavy places. -/
noncomputable def CellPackage.ofSurfaceRootDiscLocus [Fintype F₀] [DecidableEq F₀] {n : ℕ}
    [NeZero n] {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F₀) (hHyp : Hypotheses x₀ R H) (hmonic : H.Monic)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F₀[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly
      = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
    (root : (z : F₀) → rationalRoot (H_tilde' H) z)
    {w : F₀[X][Y]} (hwdeg : w.natDegree < n)
    (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    {disc : F₀[X]} (hdisc : disc ≠ 0)
    -- base/separability certificates over the disc-non-vanishing locus
    (hbaseT : ∀ z : F₀, disc.eval z ≠ 0 → (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepT : ∀ z : F₀, disc.eval z ≠ 0 →
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F₀)
    (e : Fin n → F₀) (he : Function.Injective e) (u₀ u₁ : Fin n → F₀)
    (matchingSet : Fin n → Finset F₀)
    -- matched/heavy places are disc-non-vanishing (the §6 discriminant geometry)
    (hmatchSub : ∀ j, ∀ z ∈ matchingSet j, disc.eval z ≠ 0)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    {xw : ℕ}
    (hξw : weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
      (ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ))
    (hcard : ∀ j, BCIKS20.Claim510Supply.killBudget n D H.natDegree
        (Bivariate.natDegreeY R) xw * H.natDegree < (matchingSet j).card)
    (S₀ : Finset F₀)
    (hS₀sub : ∀ z ∈ S₀, disc.eval z ≠ 0)
    {Bw : ℕ} (hBw : ∀ t, ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).natDegree ≤ Bw)
    (hS₀ : max Bw 1 < S₀.card) :
    CellPackage domain k δ u R H :=
  CellPackage.ofSurfaceRootShared (truncSet := Finset.univ.filter (fun z => disc.eval z ≠ 0))
    x₀ hHyp hmonic hD hd2 hdHD hD_Rx0 hRgrade hrepG root hwdeg hwdvd
    (fun z hz => hbaseT z (Finset.mem_filter.mp hz).2)
    (fun z hz => hsepT z (Finset.mem_filter.mp hz).2)
    hdisc
    -- hcover: DISCHARGED — every disc-non-vanishing z lands in the filter locus
    (fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩)
    hbig e he u₀ u₁ matchingSet
    (fun j z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ z, hmatchSub j z hz⟩)
    hfold hξw hcard S₀
    (fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ z, hS₀sub z hz⟩)
    hBw hS₀

/-- **The §6 discriminant-counting mass bound for the disc-locus constructor.**  The
truncation set chosen by `ofSurfaceRootDiscLocus` (the disc-non-vanishing locus) has
cardinality at least `|F₀| − deg(disc)`.  This is exactly the supply that makes the
matching/heavy-set cardinality legs (`hcard`, `hS₀`) achievable: the same `disc.natDegree`
that appears in the `hbig` budget `gradedCardBudget + disc.natDegree < |F₀|` bounds the
exceptional set, so a large locus remains.  (The disc-vanishing complement injects into the
roots of the nonzero `disc`, hence has `card ≤ disc.natDegree`.) -/
theorem discLocus_card_ge [Fintype F₀] [DecidableEq F₀]
    {disc : F₀[X]} (hdisc : disc ≠ 0) :
    Fintype.card F₀ - disc.natDegree
      ≤ (Finset.univ.filter (fun z : F₀ => disc.eval z ≠ 0)).card := by
  classical
  -- the complement (the disc-vanishing locus) is a set of roots of the nonzero `disc`
  have hcompl : (Finset.univ.filter (fun z : F₀ => ¬ disc.eval z ≠ 0)).card
      ≤ disc.natDegree := by
    refine le_trans (Polynomial.card_le_degree_of_subset_roots ?_) le_rfl
    intro a ha
    have hroot : disc.eval a = 0 := not_not.mp (Finset.mem_filter.mp ha).2
    exact (Polynomial.mem_roots hdisc).mpr (Polynomial.IsRoot.def.mpr hroot)
  -- the locus and its complement partition `univ`
  have hpart : (Finset.univ.filter (fun z : F₀ => disc.eval z ≠ 0)).card
      + (Finset.univ.filter (fun z : F₀ => ¬ disc.eval z ≠ 0)).card
      = Fintype.card F₀ := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  omega

end BCIKS20.CellPencilJohnson

