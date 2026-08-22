/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ11BCIKS57Chunk3
import ArkLib.ToMathlib.DecodedRootSupply

/-!
# SYZ14 — BCIKS20 Claim 5.7 program, Chunk 2 (`PlaceCurveSupply`): the Hensel-branch handoff

This file discharges the **structural** half of chunk C2 of the SYZ10 chunk plan (see
`Frontier/_SYZ11BCIKS57Chunk3.lean` for the interface partition and the downstream
C3→C4→C5→C6 composition into `DiscLocusCellData`).

`PlaceCurveSupply` (C2's output) carries two kinds of field:

* the **place-curve base facts** — the centre `x₀`, the Claim-A.2 `Hypotheses`, monicity
  `hmonic`, and the `Y`-degree floor `hd2`.  For `H` selected as an irreducible factor of the
  `x₀`-slice of `R`, these are exactly the fields of `GSFactorData.Bundle x₀`
  (`ArkLib/ToMathlib/GSFactorData.lean`: `R, H, hIrr, hPos, hHyp`) plus the two elementary
  facts `H.Monic` and `2 ≤ natDegreeY R`.  They are **not** the branch mathematics.

* the **Hensel-branch data** (boundary-shifted into C2 per the SYZ11 note) — the γ-series
  polynomial representative `Ppoly, hrepG`, the per-`z` rational-root section `root`, and the
  `Y`-root divisor `w, hwdeg, hwdvd`.  These are the genuine open [BCIKS20] §5 branch-selection
  content.

## What this file delivers

1. **`HenselBranchSupply`** — the single named interface bundling the genuinely-open §5 branch
   inputs: the GS split `evalX (C x₀) R = H · G`, the `Y`-root divisor `w, hwdeg, hwdvd`, the
   global branch-simplicity certificate `hbranch`, and the γ-representative `Ppoly, hrepG`.
   This is ONE Prop-carrying structure per genuinely-missing piece of §5 mathematics.

2. **`placeCurveSupply_of_henselBranch`** — from the four base facts (`x₀, hHyp, hmonic, hd2`)
   and a `HenselBranchSupply`, produce `PlaceCurveSupply`.  The `root` section is **derived**,
   not carried: at every `z` the branch root is `DecodedRootSupply.rootDecoded` applied to the
   split, the divisor, and the branch-simplicity certificate.  So C2's six branch fields collapse
   to the divisor + split + one global nonvanishing + the γ-representative.

3. **`discLocusCellData_of_henselBranch`** — the full C2→C6 composition: `HenselBranchSupply`
   (+ base facts) run through `gradedYRootSupply_of_placeCurve` (C3) and assembled with the
   C4/C5/C6 supplies into `DiscLocusCellData`.  Every remaining open obligation is a named field
   of `HenselBranchSupply` or of one of the C4/C5/C6 interfaces.

## Honest status of `hrepG` (documented, load-bearing)

The `hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp` field is carried, not
produced.  This is deliberate: `ArkLib/ToMathlib/GenuinePpolyConverter.lean`
(`not_hrepG_of_two_le_natDegree`) proves this equation is **unsatisfiable whenever
`2 ≤ H.natDegree`** — the single-polynomial `polyToPowerSeries𝕃` representative lives on the
ground `F[Z]`-line, while `coeff 0 (gammaGenuine) = α₀ = T/W` is off it.  So the *literal*
`PlaceCurveSupply` (and hence the whole disc-locus package) is genuinely blocked at every curve
of interest on the issue-#304 single-vs-`T`-loaded representative gap; the corrected `T`-loaded
representative (`polyToPowerSeries𝕃T`, two polynomials) is the real §5 object.  This file does
NOT paper over that: `hrepG` is a named input of `HenselBranchSupply`, flagged here as the
genuinely-open §5 mathematics that the rest of C2 reduces to.
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

namespace BCIKS20.CellPencilJohnson.SYZ14

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]
variable {n : ℕ} [NeZero n]

/-! ## The named §5 branch residual -/

/-- **The Hensel-branch supply (the single named C2 residual).**  The genuinely-open [BCIKS20]
§5 branch-selection data over one cell, bundled as one interface:

* `G, hsplit` — the GS split of the `x₀`-slice `evalX (C x₀) R = H · G` (the irreducible place
  curve `H` peeled off, `G` the residual cofactor);
* `w, hwdeg, hwdvd` — the `Y`-root divisor `(X − C w) ∣ R` with `w.natDegree < n` (the branch
  whose centre value roots `H`);
* `hbranch` — global branch-simplicity: at every `z`, `G(z, w(x₀, z)) ≠ 0`, so the decoded
  branch is a *simple* root of the `x₀`-slice (this is exactly what makes `w(x₀,·)` a genuine
  root section of `H`, off the residual cofactor);
* `Ppoly, hrepG` — the γ-series polynomial representative.  **NOTE:** `hrepG` is unsatisfiable
  for `2 ≤ H.natDegree` in this single-polynomial `polyToPowerSeries𝕃` form
  (`GenuinePpolyConverter.not_hrepG_of_two_le_natDegree`); it is the true open §5 object (the
  corrected `T`-loaded representative), carried here as the genuinely-missing mathematics. -/
structure HenselBranchSupply (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin 2) (Fin n)) (R : (F₀[X])[X][Y])
    (H : F₀[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F₀) (hHyp : Hypotheses x₀ R H) : Type where
  G : F₀[X][Y]
  hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G
  w : F₀[X][Y]
  hwdeg : w.natDegree < n
  hwdvd : (Polynomial.X - Polynomial.C w) ∣ R
  hbranch : ∀ z : F₀,
    Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0
  Ppoly : F₀[X][Y]
  hrepG : polyToPowerSeries𝕃 H Ppoly
    = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp

/-! ## C2 output from the branch residual (root DERIVED) -/

/-- **Chunk 2 (the place-curve supply from the branch residual).**  From the four base facts
(`x₀, hHyp, hmonic, hd2`) and a `HenselBranchSupply`, produce `PlaceCurveSupply`.  The per-`z`
rational-root section `root` is **derived** — `DecodedRootSupply.rootDecoded` turns the split,
the divisor, and the branch-simplicity certificate into a `rationalRoot (H_tilde' H) z` at every
`z`, with value the centre fold `w(x₀, z)` (monic case).  So of C2's six branch fields, only the
divisor `w, hwdvd`, the split `G, hsplit`, the global nonvanishing `hbranch`, and the
γ-representative `Ppoly, hrepG` remain as inputs; `root` is no longer an independent obligation. -/
noncomputable def placeCurveSupply_of_henselBranch
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F₀) (hHyp : Hypotheses x₀ R H) (hmonic : H.Monic)
    (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hb : HenselBranchSupply domain k δ u R H x₀ hHyp) :
    SYZ11.PlaceCurveSupply domain k δ u R H where
  x₀ := x₀
  hHyp := hHyp
  hmonic := hmonic
  hd2 := hd2
  Ppoly := hb.Ppoly
  hrepG := hb.hrepG
  root := fun z =>
    ArkLib.DecodedRootSupply.rootDecoded (Fact.out) hb.hsplit hb.hwdvd z (hb.hbranch z)
  w := hb.w
  hwdeg := hb.hwdeg
  hwdvd := hb.hwdvd

/-! ## The full C2→C6 composition -/

/-- **The full per-cell package from the branch residual.**  Run C2 (this file) into C3
(`gradedYRootSupply_of_placeCurve`), then assemble with the C4/C5/C6 supplies
(`DiscBudgetSupply`, `MatchingFoldSupply`, `HeavyPinSupply`) into `DiscLocusCellData`.  Every
remaining open obligation is a named field of `HenselBranchSupply` or of one of the three
downstream interfaces — the entire [BCIKS20] Claim 5.7 disc-locus package is thereby a
machine-checked composition anchored at the single §5 branch residual. -/
noncomputable def discLocusCellData_of_henselBranch
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F₀) (hHyp : Hypotheses x₀ R H) (hmonic : H.Monic)
    (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hb : HenselBranchSupply domain k δ u R H x₀ hHyp)
    (db : SYZ11.DiscBudgetSupply domain k δ u R H
      (SYZ11.gradedYRootSupply_of_placeCurve
        (placeCurveSupply_of_henselBranch x₀ hHyp hmonic hd2 hb)))
    (mf : SYZ11.MatchingFoldSupply domain k δ u R H
      (SYZ11.gradedYRootSupply_of_placeCurve
        (placeCurveSupply_of_henselBranch x₀ hHyp hmonic hd2 hb)) db)
    (hp : SYZ11.HeavyPinSupply domain k δ u R H
      (SYZ11.gradedYRootSupply_of_placeCurve
        (placeCurveSupply_of_henselBranch x₀ hHyp hmonic hd2 hb)) db) :
    DiscLocusCellData domain k δ u R H :=
  SYZ11.discLocusCellData_of_placeCurve
    (placeCurveSupply_of_henselBranch x₀ hHyp hmonic hd2 hb) db mf hp

end BCIKS20.CellPencilJohnson.SYZ14

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms BCIKS20.CellPencilJohnson.SYZ14.placeCurveSupply_of_henselBranch
#print axioms BCIKS20.CellPencilJohnson.SYZ14.discLocusCellData_of_henselBranch
