/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CellPackageSupplyShrink
import ArkLib.Data.CodingTheory.ProximityGap.ProductionRegimeBracket

/-!
# SYZ8: the disc-locus supply reduction of the Johnson-lane residual `CellPackageSupply`

The Johnson floor jump `(1−ρ)/3 → 1−√ρ` is gated on the single named residual
`CellPackageSupply` (`Hab25JohnsonPackageSupply.lean`) — the [BCIKS20] Claim 5.7 per-cell
§5 heavy-agreement package.  `CellPackageSupplyShrink.lean` shrank the *per-cell*
constructor surface three ways, culminating in `CellPackage.ofSurfaceRootDiscLocus`, which
pins the truncation set to the discriminant non-vanishing locus, discharges the cover leg,
and collapses the four redundant base/separability legs to a single certificate.

This file **lifts that reduction to the supply level.**  It introduces:

* `DiscLocusCellData` — a structure bundling exactly the inputs of
  `CellPackage.ofSurfaceRootDiscLocus`; a strictly *smaller* surface than `CellPackage`
  (no free `truncSet`; no `hcover`; base/separability given once over the disc locus, not
  four times over the matching/heavy loci).
* `CellPackage.ofDiscLocusData` — rebuilds the full `CellPackage` from that data.
* `CellPackageSupplyDiscLocus` — the disc-locus form of the supply Prop: every large cell
  carries `DiscLocusCellData` (rather than a full `CellPackage`).
* `cellPackageSupply_of_discLocus` — **the reduction**: disc-locus supply ⟹ `CellPackageSupply`.
* `johnsonDischargeStatement_of_discLocusSupply` — the Johnson discharge off the *smaller*
  residual.
* `production_good_johnson_of_discLocusSupply` — the production floor jump
  `δ ≤ δ*` in the Johnson range, now conditional on `CellPackageSupplyDiscLocus` instead of
  `CellPackageSupply`.

Net effect: the named residual on the Johnson floor lane can be replaced verbatim by its
strictly-smaller disc-locus form.  This does **not** discharge the residual — the [BCIKS20]
Claim 5.7 surface production (produce, over a large cell, the place curve `H`, the centre
`x₀`, the Y-root divisor `w`, and the disc-non-vanishing matching/heavy loci) remains the
genuine open mathematics.  It sharpens *what must be produced*.
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

/-- **The disc-locus per-cell data.**  Exactly the inputs consumed by
`CellPackage.ofSurfaceRootDiscLocus`: the GS surface facts, the Y-root divisor `w`, a
discriminant `disc` with a single base + separability certificate over its non-vanishing
locus, and the matching/heavy loci sitting inside that locus.  This is a strictly smaller
surface than `CellPackage` — the four redundant base/separability legs and the free
truncation set are gone. -/
structure DiscLocusCellData [Fintype F₀] [DecidableEq F₀] {n : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0) (u : WordStack F₀ (Fin 2) (Fin n))
    (R : (F₀[X])[X][Y])
    (H : F₀[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)] : Type where
  x₀ : F₀
  hHyp : Hypotheses x₀ R H
  hmonic : H.Monic
  D : ℕ
  hD : Bivariate.totalDegree H ≤ D
  hd2 : 2 ≤ Bivariate.natDegreeY R
  hdHD : H.natDegree ≤ D
  hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R)
  hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j
  Ppoly : F₀[X][Y]
  hrepG : polyToPowerSeries𝕃 H Ppoly
    = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp
  root : (z : F₀) → rationalRoot (H_tilde' H) z
  w : F₀[X][Y]
  hwdeg : w.natDegree < n
  hwdvd : (Polynomial.X - Polynomial.C w) ∣ R
  disc : F₀[X]
  hdisc : disc ≠ 0
  hbaseT : ∀ z : F₀, disc.eval z ≠ 0 → (w.eval (Polynomial.C x₀)).eval z = (root z).1
  hsepT : ∀ z : F₀, disc.eval z ≠ 0 →
    ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z (root z)
        (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
          hmonic.leadingCoeff z (root z))))).Separable
  hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
      + disc.natDegree < Fintype.card F₀
  e : Fin n → F₀
  he : Function.Injective e
  u₀ : Fin n → F₀
  u₁ : Fin n → F₀
  matchingSet : Fin n → Finset F₀
  hmatchSub : ∀ j, ∀ z ∈ matchingSet j, disc.eval z ≠ 0
  hfold : ∀ j, ∀ z ∈ matchingSet j,
    (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j
  xw : ℕ
  hξw : weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
    (ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ)
  hcard : ∀ j, BCIKS20.Claim510Supply.killBudget n D H.natDegree
      (Bivariate.natDegreeY R) xw * H.natDegree < (matchingSet j).card
  S₀ : Finset F₀
  hS₀sub : ∀ z ∈ S₀, disc.eval z ≠ 0
  Bw : ℕ
  hBw : ∀ t, ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).natDegree ≤ Bw
  hS₀ : max Bw 1 < S₀.card

/-- **Rebuild a full `CellPackage` from disc-locus data.**  Pure field-by-field feed into
`CellPackage.ofSurfaceRootDiscLocus`; witnesses that `DiscLocusCellData` is a faithful,
strictly-smaller presentation of the per-cell package. -/
noncomputable def CellPackage.ofDiscLocusData [Fintype F₀] [DecidableEq F₀] {n : ℕ}
    [NeZero n] {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (d : DiscLocusCellData domain k δ u R H) :
    CellPackage domain k δ u R H :=
  CellPackage.ofSurfaceRootDiscLocus d.x₀ d.hHyp d.hmonic d.hD d.hd2 d.hdHD d.hD_Rx0
    d.hRgrade d.hrepG d.root d.hwdeg d.hwdvd d.hdisc d.hbaseT d.hsepT d.hbig
    d.e d.he d.u₀ d.u₁ d.matchingSet d.hmatchSub d.hfold d.hξw d.hcard d.S₀ d.hS₀sub
    d.hBw d.hS₀

/-- **The disc-locus form of the supply residual.**  Every cell is small (`≤ T`) or carries
disc-locus data.  Strictly smaller than `CellPackageSupply`: the per-cell obligation is
`DiscLocusCellData` (single disc-locus certificate) rather than a full `CellPackage`. -/
def CellPackageSupplyDiscLocus [Fintype F₀] [DecidableEq F₀] {n : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0) (T : ℕ) : Prop :=
  ∀ (u : WordStack F₀ (Fin 2) (Fin n)) (R : (F₀[X])[X][Y]) (E : Finset F₀)
    (P : F₀ → F₀[X]),
    Irreducible R →
    (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
    (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
    E.card ≤ T ∨
    ∃ (H : F₀[X][Y]) (h1 : Fact (Irreducible H)) (h2 : Fact (0 < H.natDegree)),
      haveI := h1; haveI := h2
      Nonempty (DiscLocusCellData domain k δ u R H)

/-- **The reduction.**  Disc-locus supply ⟹ the named `CellPackageSupply` residual, by
rebuilding each cell's package with `CellPackage.ofDiscLocusData`.  This lets every consumer
of `CellPackageSupply` be re-based on the strictly-smaller disc-locus form. -/
theorem cellPackageSupply_of_discLocus [Fintype F₀] [DecidableEq F₀]
    {n k : ℕ} [NeZero n] {domain : Fin n ↪ F₀} {δ : ℝ≥0} {T : ℕ}
    (h : CellPackageSupplyDiscLocus domain k δ T) :
    CellPackageSupply domain k δ T := by
  intro u R E P hRirr hdec hdvdR
  rcases h u R E P hRirr hdec hdvdR with hsmall | ⟨H, h1, h2, hdata⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨H, h1, h2, hdata.map (fun d => CellPackage.ofDiscLocusData d)⟩

/-- **The Johnson discharge off the smaller residual.**  If disc-locus supply holds at every
instance in the discharge range, the full `JohnsonDischargeStatement` follows — the
`CellPackageSupply` in `johnsonDischargeStatement_of_packageSupply` is replaced verbatim by
its disc-locus form. -/
theorem johnsonDischargeStatement_of_discLocusSupply
    (hsupply : ∀ (n k m : ℕ) (_ : NeZero n) (F₀ : Type) (_ : Field F₀) (_ : Fintype F₀)
      (_ : DecidableEq F₀) (domain : Fin n ↪ F₀) (δ : ℝ≥0),
      2 ≤ k → k + 1 ≤ n → 12 ≤ m → δ ≤ 1 →
      CellPackageSupplyDiscLocus domain k δ
        (max (n * (GuruswamiSudan.constraintIndices m).card
          * (gs_degree_bound k n m / (k - 1))) n)) :
    JohnsonDischargeStatement :=
  johnsonDischargeStatement_of_packageSupply
    (fun n k m hNZ F₀ hF hFin hDec domain δ hk2 hkn hm12 hδ1 =>
      cellPackageSupply_of_discLocus
        (hsupply n k m hNZ F₀ hF hFin hDec domain δ hk2 hkn hm12 hδ1))

end BCIKS20.CellPencilJohnson

/-! ## The production floor jump off the disc-locus residual -/

namespace ProximityGap.ProductionRegime

open ProximityGap.SpikeFloor ProximityGap.MCAThresholdLedger
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open BCIKS20.CellPencilJohnson

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The conditional production Johnson floor, off the disc-locus residual.**  Identical to
`production_good_johnson_of_packageSupply` but conditioned on the strictly-smaller
`CellPackageSupplyDiscLocus`: every Johnson-range radius is good, i.e. `δ ≤ δ*` for every
`δ < 1 − √ρ₊ − η` in the discharge regime.  Landing this floor jump `(1−ρ)/3 → 1−√ρ` now
requires only the disc-locus [BCIKS20] Claim 5.7 production. -/
theorem production_good_johnson_of_discLocusSupply
    (hsupply : ∀ (n k m : ℕ) (_ : NeZero n) (F₀ : Type) (_ : Field F₀) (_ : Fintype F₀)
      (_ : DecidableEq F₀) (domain : Fin n ↪ F₀) (δ : ℝ≥0),
      2 ≤ k → k + 1 ≤ n → 12 ≤ m → δ ≤ 1 →
      CellPackageSupplyDiscLocus domain k δ
        (max (n * (GuruswamiSudan.constraintIndices m).card
          * (gs_degree_bound k n m / (k - 1))) n))
    {n k m : ℕ} [NeZero n] {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]
    (domain : Fin n ↪ F₀) (η δ : ℝ≥0)
    (hk2 : 2 ≤ k) (hkn : k + 1 ≤ n) (hm12 : 12 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < _root_.gs_johnson k n m)
    (hmle : (m : ℝ) ≤
      max (⌈((((k : ℝ) / n + 1 / n)) ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3)
    {εstar : ℝ≥0∞}
    (hbudget : ENNReal.ofReal (johnsonBoundReal domain k η δ) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F₀) (A := F₀)
        ((ReedSolomon.code domain k : Set (Fin n → F₀))) εstar :=
  production_good_johnson_of_packageSupply
    (fun n k m hNZ F₀ hF hFin hDec domain δ hk2 hkn hm12 hδ1 =>
      cellPackageSupply_of_discLocus
        (hsupply n k m hNZ F₀ hF hFin hDec domain δ hk2 hkn hm12 hδ1))
    domain η δ hk2 hkn hm12 hδ1 hδJ hmle hbudget

end ProximityGap.ProductionRegime

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms BCIKS20.CellPencilJohnson.CellPackage.ofDiscLocusData
#print axioms BCIKS20.CellPencilJohnson.cellPackageSupply_of_discLocus
#print axioms BCIKS20.CellPencilJohnson.johnsonDischargeStatement_of_discLocusSupply
#print axioms ProximityGap.ProductionRegime.production_good_johnson_of_discLocusSupply
