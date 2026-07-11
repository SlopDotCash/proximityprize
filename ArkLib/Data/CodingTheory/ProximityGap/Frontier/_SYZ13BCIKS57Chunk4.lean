/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ11BCIKS57Chunk3
import ArkLib.ToMathlib.ConditionDiscProduct
import ArkLib.ToMathlib.GSSurfaceMappedSeparability

/-!
# SYZ13 — BCIKS20 Claim 5.7 program, Chunk 4 (`DiscBudgetSupply`)

This file discharges the **C4** chunk of the SYZ10 multi-chunk program: the §6 discriminant
budget interface `DiscBudgetSupply` (`Frontier/_SYZ11BCIKS57Chunk3.lean`), built on top of a
`GradedYRootSupply` (C3 output).  `DiscBudgetSupply` bundles five fields:

* `disc : F₀[X]`, `hdisc : disc ≠ 0` — the discriminant candidate and its nonvanishing;
* `hbaseT` — the base-agreement certificate (the `Y`-root divisor `w` at `x₀` reads off the
  rational root over the disc non-vanishing locus);
* `hsepT` — the per-place separability certificate (the doubly-mapped local `R` is separable
  over `F⟦X⟧` at each place of the locus);
* `hbig` — the field-size degree budget.

## What this file delivers (honest verdict)

**The STRUCTURAL half of C4 is discharged with zero extra input.**  The discriminant candidate
is the genuine [BCIKS20] Lemma-A.1 elimination polynomial — the product of the two `Y`-resultant
"reading" discriminants

  `disc := elimPoly hH ξ * elimPoly hH W𝒪`

(each `elimPoly hH β = resultant (H̃′ H) (canonicalRep β)`, an honest univariate resultant built
from Mathlib's `Polynomial.resultant`; note Mathlib has **no** univariate `Polynomial.discriminant`,
so the resultant elimination polynomial *is* the in-tree discriminant object).  Its nonvanishing
`hdisc` is proved **unconditionally** — no genericity, no numeric side condition — from the two
proven global unit facts `ξ ≠ 0` (monic ⇒ unit) and `W𝒪 ≠ 0`, via `elimPoly_ne_zero_of_ne_zero`
(ultimately: `resultant ≠ 0` because neither factor vanishes).  This is exactly the C4 note's
part (a), proved NOW.

Moreover the disc's non-vanishing locus is **semantically live**: on it the `ξ`- and `W`-readings
are nonzero at every rational root (`π_z_ne_zero_of_elimPoly_eval_ne_zero`), which is the `hx`
input the downstream separability consumes — so `disc` is not a bookkeeping placeholder but the
actual §6 reading discriminant used by C5's matching set.

**The genuinely-open half is shrunk to two named minimal certificates + one numeric hypothesis:**

* `hsep : MappedSliceSeparability g.hHyp` — the per-place separability certificate.  This is the
  *consolidated* separability hypothesis of `MappedSeparability` (issue #301/#302/#304): strictly
  **below** the trivariate Node-B separability `R.Separable`, and producible from per-place
  finite-**field** residue-discriminant data (`MappedSliceSeparability.of_residue`).  `hsepT` is
  *exactly* one instance of it at `(z, g.root z)` with the monic `ξ`-unit witness, so it discharges
  definitionally (proof-irrelevance on the `hx` argument of `π_hat_z`).
* `hbase` — the base-agreement of the `Y`-root divisor `w` with the rational-root section.  Per
  the SYZ11 boundary note this is genuine BCIKS §5 branch/decoding content (the `CurveFamilyHensel`
  handoff, *not* a discriminant condition — cf. `RootSupplyOn`), so it is honestly a named input
  rather than something the disc geometry can supply.
* `h_numeric` — the field-size budget `gradedCardBudget … + disc.natDegree < |F₀|`.  At production
  `|F₀| ≈ 2¹⁵⁸` this is roomy but the abstract Prop is stated over an arbitrary `F₀`, so it stays a
  cell-side numeric hypothesis (the C4 note's part (d)).

No new mathematics is claimed for `hbase`/`hsep`; both are the pre-existing named residuals of the
§5/§6 lanes, now wired through the chunk interface.  Everything here is axiom-clean.

## References
* [BCIKS20] Claim 5.7, §5–§6, Appendix A.1/A.4.
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

namespace BCIKS20.CellPencilJohnson.SYZ13

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]
variable {n : ℕ} [NeZero n]

open BCIKS20.CellPencilJohnson.SYZ11

/-- **The C4 discriminant candidate.**  The product of the two [BCIKS20] Lemma-A.1 elimination
polynomials (`Y`-resultants) for the `ξ`- and `W`-readings.  This is the genuine §6 reading
discriminant: on its non-vanishing locus both readings are nonzero at every rational root. -/
noncomputable def c4Disc
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (g : GradedYRootSupply domain k δ u R H) : F₀[X] :=
  elimPoly (Fact.out (p := 0 < H.natDegree)) (ξ g.x₀ R H g.hHyp)
    * elimPoly (Fact.out (p := 0 < H.natDegree)) (BCIKS20.HenselNumerator.W𝒪 H)

/-- `c4Disc ≠ 0`, proved **unconditionally** from the two proven global unit nonvanishings. -/
theorem c4Disc_ne_zero
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (g : GradedYRootSupply domain k δ u R H) : c4Disc g ≠ 0 :=
  mul_ne_zero
    (ArkLib.Match304.elimPoly_ne_zero_of_ne_zero _
      (ArkLib.Match304.ξ_ne_zero H g.x₀ R g.hHyp))
    (ArkLib.Match304.elimPoly_ne_zero_of_ne_zero _
      (ArkLib.Match304.W𝒪_ne_zero H))

/-- **Chunk 4 (the discriminant budget derivation).**  From a `GradedYRootSupply` and the two
named minimal certificates (`hsep`, the per-place separability strictly below Node B; `hbase`, the
§5 base-agreement handoff) plus the field-size numeric budget `h_numeric`, produce the C4 interface
`DiscBudgetSupply`.  The discriminant `disc := c4Disc g` and its nonvanishing `hdisc` are genuine
(no extra hypotheses); the two certificate fields and the budget field are the named residuals. -/
noncomputable def discBudgetSupply_of_gradedYRoot
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (g : GradedYRootSupply domain k δ u R H)
    (hsep : ArkLib.MappedSeparability.MappedSliceSeparability g.hHyp)
    (hbase : ∀ z : F₀, (c4Disc g).eval z ≠ 0 →
      (g.w.eval (Polynomial.C g.x₀)).eval z = (g.root z).1)
    (h_numeric : gradedCardBudget (Bivariate.natDegreeY R) g.D H.natDegree g.Ppoly.natDegree
        + (c4Disc g).natDegree < Fintype.card F₀) :
    DiscBudgetSupply domain k δ u R H g where
  disc := c4Disc g
  hdisc := c4Disc_ne_zero g
  hbaseT := hbase
  hsepT := fun z _ =>
    hsep z (g.root z)
      (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic g.hHyp
        g.hmonic.leadingCoeff z (g.root z))
  hbig := h_numeric

end BCIKS20.CellPencilJohnson.SYZ13

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms BCIKS20.CellPencilJohnson.SYZ13.c4Disc_ne_zero
#print axioms BCIKS20.CellPencilJohnson.SYZ13.discBudgetSupply_of_gradedYRoot
