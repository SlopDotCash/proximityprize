/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ8CellPackageSupply

/-!
# SYZ11 — BCIKS20 Claim 5.7 program, Chunk 3 (grading + Y-root) + the composition assembly

This file continues the multi-chunk program (SYZ10) that discharges the strictly-smaller
Johnson-lane residual `CellPackageSupplyDiscLocus`
(`Frontier/_SYZ8CellPackageSupply.lean`), the per-cell disc-locus form of the [BCIKS20]
Claim 5.7 heavy-agreement package.  Each chunk is a self-contained axiom-clean interface
carving out a group of `DiscLocusCellData` fields; the chunks compose so the *entire*
per-cell assembly is machine-checked, with exactly the named open Props remaining.

## What this file delivers

1. **Interface structures** partitioning the `DiscLocusCellData` fields into the five chunk
   groups of the SYZ10 plan, each parameterized by the prior chunk's output so they compose:
   * `PlaceCurveSupply`   — C2 output: the place curve `H`, centre `x₀`, `Hypotheses`, and the
     open branch data (see the boundary-shift note below);
   * `GradedYRootSupply`  — C3 output: `PlaceCurveSupply` **plus** the §5 degree grading
     `D, hD, hdHD, hD_Rx0, hRgrade`;
   * `DiscBudgetSupply`   — C4 output: `disc, hdisc, hbaseT, hsepT, hbig`;
   * `MatchingFoldSupply` — C5 output: `e, …, matchingSet, hfold, xw, hξw, hcard`;
   * `HeavyPinSupply`     — C6 output: `S₀, Bw, hBw, hS₀`.

2. **`gradedYRootSupply_of_placeCurve`** — the C3 derivation: from `PlaceCurveSupply` produce
   `GradedYRootSupply` by proving the weighted-degree grading.  This is genuine (if elementary)
   §5 bookkeeping: a single grading bound `D` simultaneously dominating `totalDegree H`,
   `H.natDegree`, `totalDegree (R(x₀,·))`, and the per-`Y`-coefficient `X`-degree budget
   `degreeX(R.coeff j) + j`.

3. **`discLocusCellData_of_supplies`** — the C6 assembly half: field-by-field feed of the four
   downstream chunk outputs into `DiscLocusCellData`.  Together with (2) this makes the whole
   §5–§6 per-cell package a machine-checked composition of five named interfaces.

## Honest boundary shift (documented)

C3's genuine mathematical content is the **grading** only.  The other pieces the SYZ10 plan
tentatively assigned to C3 — the γ-series *polynomial* witness `Ppoly, hrepG`
(that `gammaGenuine` is genuine, i.e. finite), the per-`z` rational-root section `root`, and
the `Y`-root divisor `w, hwdeg, hwdvd` — are the actual Hensel-lift / branch-selection content
of BCIKS20 §5 (the `gammaGenuine` construction is `(𝕃 H)⟦X⟧`-valued; its genuineness and the
divisor `(X − C w) ∣ R` are not one-session gaps).  These are **shifted into `PlaceCurveSupply`**
(C2's obligations) as named fields, so that `gradedYRootSupply_of_placeCurve` genuinely proves
the grading and *passes the branch data through* rather than inventing it.  `hd2`
(`2 ≤ natDegreeY R`) is likewise a property of the cell's `R` and lives in `PlaceCurveSupply`.
No new mathematics is claimed for the branch data here; the grading proof is real and
axiom-clean.
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

namespace BCIKS20.CellPencilJohnson.SYZ11

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]
variable {n : ℕ} [NeZero n]

/-! ## C2 output — the place curve, plus the boundary-shifted branch data -/

/-- **Chunk-2 output interface (place curve supply).**  The [BCIKS20] §5–§6 place-curve step:
an irreducible positive-degree monic curve `H` (produced as the structure's index parameter,
existentially chosen upstream), its centre `x₀` with the Claim A.2 `Hypotheses`, and — shifted
in from C3 per the boundary note — the open Hensel-lift branch data: the γ-series polynomial
witness `Ppoly, hrepG`, the per-`z` rational-root section `root`, the `Y`-root divisor
`w, hwdeg, hwdvd`, and the `Y`-degree floor `hd2`.  These branch fields are the genuine open
BCIKS §5 mathematics; C3 (below) consumes them unchanged and adds only the grading. -/
structure PlaceCurveSupply (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin 2) (Fin n)) (R : (F₀[X])[X][Y])
    (H : F₀[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)] : Type where
  x₀ : F₀
  hHyp : Hypotheses x₀ R H
  hmonic : H.Monic
  hd2 : 2 ≤ Bivariate.natDegreeY R
  Ppoly : F₀[X][Y]
  hrepG : polyToPowerSeries𝕃 H Ppoly
    = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp
  root : (z : F₀) → rationalRoot (H_tilde' H) z
  w : F₀[X][Y]
  hwdeg : w.natDegree < n
  hwdvd : (Polynomial.X - Polynomial.C w) ∣ R

/-! ## C3 output — the degree grading on top of the place curve -/

/-- **Chunk-3 output interface (graded Y-root supply).**  Extends `PlaceCurveSupply` with the
[BCIKS20] §5 weighted-degree grading: a single bound `D` dominating the total degree of `H`,
its `Y`-degree, the total degree of the `x₀`-slice `R(x₀,·)`, and every per-`Y`-coefficient
`X`-degree budget `degreeX(R.coeff j) + j`.  This is the grading data consumed downstream by
the discriminant budget (C4) and the matching/heavy counts (C5/C6). -/
structure GradedYRootSupply (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin 2) (Fin n)) (R : (F₀[X])[X][Y])
    (H : F₀[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    extends PlaceCurveSupply domain k δ u R H where
  D : ℕ
  hD : Bivariate.totalDegree H ≤ D
  hdHD : H.natDegree ≤ D
  hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C toPlaceCurveSupply.x₀) R)
  hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j

/-- **Chunk 3 (the grading derivation).**  From a `PlaceCurveSupply` produce a
`GradedYRootSupply`: define the grading bound
`D = max (totalDegree H) (max H.natDegree (max (totalDegree R(x₀,·)) G))` where
`G = sup_{j ∈ supp R} (degreeX(R.coeff j) + j)`, and discharge the four grading inequalities.
The branch data passes through unchanged.  This is the genuine (elementary) §5 weighted-degree
bookkeeping — no branch mathematics is invented here. -/
noncomputable def gradedYRootSupply_of_placeCurve
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (p : PlaceCurveSupply domain k δ u R H) :
    GradedYRootSupply domain k δ u R H := by
  classical
  refine { toPlaceCurveSupply := p
           D := max (Bivariate.totalDegree H)
                 (max H.natDegree
                   (max (Bivariate.totalDegree (Bivariate.evalX (Polynomial.C p.x₀) R))
                     (R.support.sup (fun j => Bivariate.degreeX (R.coeff j) + j))))
           hD := le_max_left _ _
           hdHD := le_max_of_le_right (le_max_left _ _)
           hD_Rx0 := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
           hRgrade := ?_ }
  intro j
  by_cases hj : j ∈ R.support
  · have hle : Bivariate.degreeX (R.coeff j) + j
        ≤ R.support.sup (fun j => Bivariate.degreeX (R.coeff j) + j) :=
      Finset.le_sup (f := fun j => Bivariate.degreeX (R.coeff j) + j) hj
    have hD' : Bivariate.degreeX (R.coeff j) + j
        ≤ max (Bivariate.totalDegree H)
            (max H.natDegree
              (max (Bivariate.totalDegree (Bivariate.evalX (Polynomial.C p.x₀) R))
                (R.support.sup (fun j => Bivariate.degreeX (R.coeff j) + j)))) :=
      le_trans hle (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
    omega
  · have h0 : R.coeff j = 0 := by simpa [Polynomial.mem_support_iff] using hj
    have hdx : Bivariate.degreeX (R.coeff j) = 0 := by
      rw [h0]; simp [Bivariate.degreeX]
    omega

/-! ## C4/C5/C6 output interfaces -/

/-- **Chunk-4 output interface (discriminant budget supply).**  The §6 discriminant geometry
over the grading of C3: a nonzero discriminant `disc`, base-agreement `hbaseT` and separability
`hsepT` certificates over its non-vanishing locus, and the degree budget `hbig`
(`gradedCardBudget … + deg disc < |F₀|`).  Parameterized by the C3 output `g` (uses
`g.x₀, g.root, g.w, g.D, g.Ppoly`). -/
structure DiscBudgetSupply (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin 2) (Fin n)) (R : (F₀[X])[X][Y])
    (H : F₀[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (g : GradedYRootSupply domain k δ u R H) : Type where
  disc : F₀[X]
  hdisc : disc ≠ 0
  hbaseT : ∀ z : F₀, disc.eval z ≠ 0 →
    (g.w.eval (Polynomial.C g.x₀)).eval z = (g.root z).1
  hsepT : ∀ z : F₀, disc.eval z ≠ 0 →
    ((R.map (coeffHom_loc g.x₀ g.hHyp)).map
      (PowerSeries.map (π_hat_z g.hHyp z (g.root z)
        (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic g.hHyp
          g.hmonic.leadingCoeff z (g.root z))))).Separable
  hbig : gradedCardBudget (Bivariate.natDegreeY R) g.D H.natDegree g.Ppoly.natDegree
      + disc.natDegree < Fintype.card F₀

/-- **Chunk-5 output interface (matching-fold supply).**  The §6 heavy-agreement per-coordinate
matching sets sitting in the disc non-vanishing locus, folding through the `Y`-root divisor
`g.w`, together with the weight ceiling `xw` and the `killBudget` count `hcard`.  Parameterized
by C3 output `g` and C4 output `db` (uses `db.disc`). -/
structure MatchingFoldSupply (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin 2) (Fin n)) (R : (F₀[X])[X][Y])
    (H : F₀[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (g : GradedYRootSupply domain k δ u R H)
    (db : DiscBudgetSupply domain k δ u R H g) : Type where
  e : Fin n → F₀
  he : Function.Injective e
  u₀ : Fin n → F₀
  u₁ : Fin n → F₀
  matchingSet : Fin n → Finset F₀
  hmatchSub : ∀ j, ∀ z ∈ matchingSet j, db.disc.eval z ≠ 0
  hfold : ∀ j, ∀ z ∈ matchingSet j,
    (g.w.eval (Polynomial.C (e j) + Polynomial.C g.x₀)).eval z = u₀ j + z * u₁ j
  xw : ℕ
  hξw : weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
    (ξ g.x₀ R H g.hHyp) g.D ≤ (WithBot.some xw : WithBot ℕ)
  hcard : ∀ j, BCIKS20.Claim510Supply.killBudget n g.D H.natDegree
      (Bivariate.natDegreeY R) xw * H.natDegree < (matchingSet j).card

/-- **Chunk-6 output interface (heavy-pin supply).**  The §6 heavy set `S₀` in the disc
non-vanishing locus with `max Bw 1 < |S₀|`, where `Bw` bounds the `X`-degrees of the Taylor
coefficients of `g.w` at `g.x₀`.  Parameterized by C3 output `g` and C4 output `db`. -/
structure HeavyPinSupply (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin 2) (Fin n)) (R : (F₀[X])[X][Y])
    (H : F₀[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (g : GradedYRootSupply domain k δ u R H)
    (db : DiscBudgetSupply domain k δ u R H g) : Type where
  S₀ : Finset F₀
  hS₀sub : ∀ z ∈ S₀, db.disc.eval z ≠ 0
  Bw : ℕ
  hBw : ∀ t, ((Polynomial.taylor (Polynomial.C g.x₀) g.w).coeff t).natDegree ≤ Bw
  hS₀ : max Bw 1 < S₀.card

/-! ## The composition assembly (C6 assembly half) -/

/-- **The per-cell assembly.**  Field-by-field feed of the four downstream chunk outputs
(`GradedYRootSupply` (C3, itself containing the C2 place-curve data), `DiscBudgetSupply` (C4),
`MatchingFoldSupply` (C5), `HeavyPinSupply` (C6)) into `DiscLocusCellData`.  Every field of the
target structure is sourced from exactly one chunk output; the whole [BCIKS20] Claim 5.7
per-cell disc-locus package is thereby a machine-checked composition of the named interfaces. -/
noncomputable def discLocusCellData_of_supplies
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (g : GradedYRootSupply domain k δ u R H)
    (db : DiscBudgetSupply domain k δ u R H g)
    (mf : MatchingFoldSupply domain k δ u R H g db)
    (hp : HeavyPinSupply domain k δ u R H g db) :
    DiscLocusCellData domain k δ u R H where
  x₀ := g.x₀
  hHyp := g.hHyp
  hmonic := g.hmonic
  D := g.D
  hD := g.hD
  hd2 := g.hd2
  hdHD := g.hdHD
  hD_Rx0 := g.hD_Rx0
  hRgrade := g.hRgrade
  Ppoly := g.Ppoly
  hrepG := g.hrepG
  root := g.root
  w := g.w
  hwdeg := g.hwdeg
  hwdvd := g.hwdvd
  disc := db.disc
  hdisc := db.hdisc
  hbaseT := db.hbaseT
  hsepT := db.hsepT
  hbig := db.hbig
  e := mf.e
  he := mf.he
  u₀ := mf.u₀
  u₁ := mf.u₁
  matchingSet := mf.matchingSet
  hmatchSub := mf.hmatchSub
  hfold := mf.hfold
  xw := mf.xw
  hξw := mf.hξw
  hcard := mf.hcard
  S₀ := hp.S₀
  hS₀sub := hp.hS₀sub
  Bw := hp.Bw
  hBw := hp.hBw
  hS₀ := hp.hS₀

/-- **The full five-stage composition.**  Starting from the C2 place-curve supply, run the C3
grading derivation and then assemble with the C4/C5/C6 outputs.  This realizes the SYZ10 chunk
plan's `PlaceCurveSupply → … → HeavyPinSupply → DiscLocusCellData` pipeline as a single
machine-checked term.  Every remaining open obligation is a named field of one of the input
structures. -/
noncomputable def discLocusCellData_of_placeCurve
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (p : PlaceCurveSupply domain k δ u R H)
    (db : DiscBudgetSupply domain k δ u R H (gradedYRootSupply_of_placeCurve p))
    (mf : MatchingFoldSupply domain k δ u R H (gradedYRootSupply_of_placeCurve p) db)
    (hp : HeavyPinSupply domain k δ u R H (gradedYRootSupply_of_placeCurve p) db) :
    DiscLocusCellData domain k δ u R H :=
  discLocusCellData_of_supplies (gradedYRootSupply_of_placeCurve p) db mf hp

end BCIKS20.CellPencilJohnson.SYZ11

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms BCIKS20.CellPencilJohnson.SYZ11.gradedYRootSupply_of_placeCurve
#print axioms BCIKS20.CellPencilJohnson.SYZ11.discLocusCellData_of_supplies
#print axioms BCIKS20.CellPencilJohnson.SYZ11.discLocusCellData_of_placeCurve
