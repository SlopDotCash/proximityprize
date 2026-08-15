# SYZ13 — BCIKS 5.7 program, Chunk C4 (`DiscBudgetSupply`) — 2026-07-11

**Issue #466 · lane: BCIKS20 Claim 5.7 per-cell disc-locus package (SYZ10 chunk plan) · file:**
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ13BCIKS57Chunk4.lean`

## Verdict

**STRUCTURAL half of C4 discharged, axiom-clean, with zero extra input; open half shrunk to 2
named certificates + 1 numeric hypothesis.** `discBudgetSupply_of_gradedYRoot` produces the C4
interface `DiscBudgetSupply` from a `GradedYRootSupply` (C3 output). The discriminant candidate
and its nonvanishing are genuine and unconditional; the three residual fields are named minimal
inputs already living in the §5/§6 lanes.

## What is genuinely proved (no hypotheses)

- **`c4Disc g := elimPoly hH (ξ …) * elimPoly hH (W𝒪 H)`** — the product of the two [BCIKS20]
  Lemma-A.1 elimination polynomials (`elimPoly hH β = Polynomial.resultant (H̃′ H) (canonicalRep β)`).
  This is the genuine resultant-based discriminant object: **Mathlib has `Polynomial.resultant` but
  NO univariate `Polynomial.discriminant`**, so the Y-resultant elimination polynomial *is* the
  in-tree discriminant. (Confirms the SYZ10 C4 note: "build from resultant".)
- **`c4Disc_ne_zero`** — `c4Disc g ≠ 0` proved **unconditionally** from the two proven global unit
  nonvanishings `ξ ≠ 0` (monic ⇒ `ξ` a unit of `𝒪 H`) and `W𝒪 ≠ 0`, via
  `ArkLib.Match304.elimPoly_ne_zero_of_ne_zero`. This is the C4 note's part (a), proved NOW.
  The key that makes (a) provable now: `ClaimA2.Hypotheses` gives `H ∣ R(x₀,·)` with `R(x₀,·)`
  separable, and monicity gives `ξ` a unit — no perfect-field/inseparability worry needed for the
  resultant nonvanishing, because the elimination polynomial is nonzero iff neither factor is zero.
- **Semantic liveness of the locus** (documented, via in-tree
  `π_z_ne_zero_of_elimPoly_eval_ne_zero`): on `c4Disc.eval z ≠ 0` both the ξ- and W-readings are
  nonzero at every rational root — exactly the `hx` the downstream C5 separability consumes. So the
  disc is the real §6 reading discriminant, not a placeholder.

## The open half (named minimal residuals — inputs to the theorem)

1. **`hsep : ArkLib.MappedSeparability.MappedSliceSeparability g.hHyp`** — per-place separability of
   the doubly-mapped local `R` over `F⟦X⟧`. This is the *consolidated* hypothesis of issue
   #301/#302/#304: strictly **below** trivariate Node-B `R.Separable`, and producible from per-place
   finite-**field** residue-discriminant data (`MappedSliceSeparability.of_residue` +
   `separable_of_powerSeries_residue`). **`hsepT` discharges to exactly one instance of it** at
   `(z, g.root z)` with the monic ξ-unit witness `pi_z_xi_ne_zero_of_monic` — definitionally, by
   proof-irrelevance on the `hx : π_z … ξ ≠ 0` argument of `π_hat_z`. (C4 note part (b), reduced to a
   pre-existing named lane residual.)
2. **`hbase`** — base agreement of the Y-root divisor `w` at `x₀` with the rational-root section
   `g.root`, over the disc non-vanishing locus. Per the SYZ11 boundary note this is genuine BCIKS §5
   branch/decoding content (the `CurveFamilyHensel` handoff; cf. `RootSupplyOn`, which is provably
   NOT a discriminant condition), so it is honestly a named input, not disc-derivable. (C4 note
   part (c): belongs to the C5 core / boundary shift.)
3. **`h_numeric`** — `gradedCardBudget dY g.D H.natDegree g.Ppoly.natDegree + (c4Disc g).natDegree <
   |F₀|`. Roomy at production `|F₀| ≈ 2¹⁵⁸`, but abstract over arbitrary `F₀`, so a cell-side numeric
   hypothesis. (C4 note part (d).)

## Theorem statements (verbatim, elided binders)

```
noncomputable def c4Disc (g : GradedYRootSupply domain k δ u R H) : F₀[X] :=
  elimPoly (Fact.out (p := 0 < H.natDegree)) (ξ g.x₀ R H g.hHyp)
    * elimPoly (Fact.out (p := 0 < H.natDegree)) (BCIKS20.HenselNumerator.W𝒪 H)

theorem c4Disc_ne_zero (g : GradedYRootSupply domain k δ u R H) : c4Disc g ≠ 0

noncomputable def discBudgetSupply_of_gradedYRoot
    (g : GradedYRootSupply domain k δ u R H)
    (hsep : ArkLib.MappedSeparability.MappedSliceSeparability g.hHyp)
    (hbase : ∀ z : F₀, (c4Disc g).eval z ≠ 0 →
      (g.w.eval (Polynomial.C g.x₀)).eval z = (g.root z).1)
    (h_numeric : gradedCardBudget (Bivariate.natDegreeY R) g.D H.natDegree g.Ppoly.natDegree
        + (c4Disc g).natDegree < Fintype.card F₀) :
    DiscBudgetSupply domain k δ u R H g
```

## Axiom audit

Both `c4Disc_ne_zero` and `discBudgetSupply_of_gradedYRoot` rest only on
`[propext, Classical.choice, Quot.sound]`.

## Remaining-open list for the BCIKS 5.7 per-cell package after SYZ13

- **C4** — STRUCTURAL DONE (disc + hdisc unconditional). Open inputs: `MappedSliceSeparability`
  (below Node B, field-residue-producible), `hbase` (§5 branch handoff), `h_numeric`.
- **C5** (`MatchingFoldSupply`) — fold-matching genuine core still isolated (SYZ12); ξ-weight
  discharged.
- **C6** (`HeavyPinSupply`) — heavy-pin discharged to one counting inequality (SYZ12).
- **C2** (`PlaceCurveSupply`) — the Hensel-lift branch data (`Ppoly/hrepG`, `root`, `w/hwdvd`)
  remain the genuine open §5 mathematics (boundary-shifted per SYZ11).

## Build

`lake env lean` on the file (deps `_SYZ11BCIKS57Chunk3`, `ConditionDiscProduct`,
`GSSurfaceMappedSeparability` oleans warm). Lockless, ~18s.
