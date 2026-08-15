# SYZ14 — BCIKS 5.7 program, Chunk C2 (`PlaceCurveSupply`) + program scoreboard — 2026-07-11

**Issue #466 · lane: BCIKS20 Claim 5.7 per-cell disc-locus package (SYZ10 chunk plan) · file:**
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ14BCIKS57Chunk2.lean`
(namespace `BCIKS20.CellPencilJohnson.SYZ14`, axiom-clean).

## Verdict

**C2 structural half discharged: the per-`z` root section is DERIVED, not carried, and C2's six
branch fields collapse to one named §5 residual `HenselBranchSupply`.** The full BCIKS 5.7 per-cell
package is now a machine-checked composition from ONE anchoring §5 Prop
(`discLocusCellData_of_henselBranch`). The genuinely-open surface of the *entire* program is
**four named Props** (one per genuinely-missing piece of mathematics), enumerated below.

The load-bearing honest finding: **`hrepG` is provably UNSATISFIABLE for `2 ≤ H.natDegree`**
(`ToMathlib/GenuinePpolyConverter.lean`, `not_hrepG_of_two_le_natDegree`). The single-polynomial
`polyToPowerSeries𝕃 H Ppoly` representative lives on the ground `F[Z]`-line, whereas
`coeff 0 (gammaGenuine) = α₀ = T/W` is off it. So the *literal* `PlaceCurveSupply` (and thus the
whole disc-locus package, `DiscLocusCellData`, and the Johnson-lane `CellPackage`) is genuinely
blocked at every curve of interest on the issue-#301/#302/#304 single-vs-`T`-loaded representative
gap. The corrected object is `polyToPowerSeries𝕃T` (two polynomials, `T`-loaded). This is not
worked around here — `hrepG` is a named field of `HenselBranchSupply`, flagged as the true open
§5 mathematics.

## C2 field → producer map

`PlaceCurveSupply domain k δ u R H` (SYZ11) fields, split by origin:

| field | status | producer / note |
|---|---|---|
| `x₀`, `hHyp : Hypotheses x₀ R H` | in-tree producer | `GSFactorData.Bundle x₀` (`ToMathlib/GSFactorData.lean`) provides `R, H, hIrr, hPos, hHyp` for `H` an irreducible factor of the `x₀`-slice, via `Bundle.of_section5Inputs` (`H := H_graph`, `hHyp := claimA2_hypotheses_graph`). Base fact, not branch math. |
| `hmonic : H.Monic` | elementary input | property of the selected place curve `H`. |
| `hd2 : 2 ≤ natDegreeY R` | elementary input | property of the cell's `R`. |
| `root : (z) → rationalRoot (H_tilde' H) z` | **DERIVED (this file)** | `DecodedRootSupply.rootDecoded` from the GS split `evalX (C x₀) R = H·G`, the divisor `(X−C w) ∣ R`, and per-`z` branch simplicity `G(z, w(x₀,z)) ≠ 0`; value `= w(x₀,z)` monic (`rootDecoded_val_monic`). **No longer an independent obligation.** |
| `w, hwdeg, hwdvd` | genuine open §5 | the `Y`-root divisor `(X−C w) ∣ R`, `w.natDegree < n` — BCIKS §5 branch selection. Named field of `HenselBranchSupply`. |
| `Ppoly, hrepG` | genuine open §5 (**UNSAT literal**) | γ-series representative; `hrepG` unsatisfiable at `2 ≤ H.natDegree` (`GenuinePpolyConverter.not_hrepG_of_two_le_natDegree`). Named field of `HenselBranchSupply`; true open object is the `T`-loaded `polyToPowerSeries𝕃T` representative. |

## What is proved (statements verbatim, binders elided)

```
structure HenselBranchSupply (domain) (k) (δ) (u) (R) (H) [Fact (Irreducible H)]
    [Fact (0 < H.natDegree)] (x₀ : F₀) (hHyp : Hypotheses x₀ R H) : Type where
  G : F₀[X][Y]
  hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G
  w : F₀[X][Y]
  hwdeg : w.natDegree < n
  hwdvd : (Polynomial.X - Polynomial.C w) ∣ R
  hbranch : ∀ z : F₀, Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0
  Ppoly : F₀[X][Y]
  hrepG : polyToPowerSeries𝕃 H Ppoly
    = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp

noncomputable def placeCurveSupply_of_henselBranch
    (x₀ : F₀) (hHyp : Hypotheses x₀ R H) (hmonic : H.Monic)
    (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hb : HenselBranchSupply domain k δ u R H x₀ hHyp) :
    SYZ11.PlaceCurveSupply domain k δ u R H
    -- root := fun z => DecodedRootSupply.rootDecoded (Fact.out) hb.hsplit hb.hwdvd z (hb.hbranch z)

noncomputable def discLocusCellData_of_henselBranch
    (x₀) (hHyp) (hmonic) (hd2)
    (hb : HenselBranchSupply domain k δ u R H x₀ hHyp)
    (db : SYZ11.DiscBudgetSupply … (gradedYRootSupply_of_placeCurve (placeCurveSupply_of_henselBranch …)))
    (mf : SYZ11.MatchingFoldSupply … db)
    (hp : SYZ11.HeavyPinSupply … db) :
    DiscLocusCellData domain k δ u R H
```

## Axiom audit

`placeCurveSupply_of_henselBranch` and `discLocusCellData_of_henselBranch` both rest only on
`[propext, Classical.choice, Quot.sound]`.

## The six-chunk program scoreboard (SYZ10 plan, complete)

Target: discharge the strictly-smaller Johnson-lane residual `CellPackageSupplyDiscLocus`
(`Frontier/_SYZ8CellPackageSupply.lean`) = the per-cell `DiscLocusCellData` form of the [BCIKS20]
Claim 5.7 heavy-agreement package. `DiscLocusCellData` partitioned into five chunk interfaces
`PlaceCurveSupply → GradedYRootSupply → DiscBudgetSupply → MatchingFoldSupply → HeavyPinSupply`.

| chunk | interface | status | file |
|---|---|---|---|
| **C2** | `PlaceCurveSupply` | **structural DONE (this file, SYZ14)**: root DERIVED; open = `HenselBranchSupply` | `_SYZ14BCIKS57Chunk2` |
| **C3** | `GradedYRootSupply` | **DONE unconditional** (`gradedYRootSupply_of_placeCurve`): the §5 weighted-degree grading, elementary, zero extra input | `_SYZ11BCIKS57Chunk3` |
| **C4** | `DiscBudgetSupply` | **structural DONE** (`discBudgetSupply_of_gradedYRoot`): `c4Disc` + `c4Disc_ne_zero` unconditional (Lemma-A.1 resultant product); open = `MappedSliceSeparability` + `hbase` + `h_numeric` | `_SYZ13BCIKS57Chunk4` |
| **C5** | `MatchingFoldSupply` | **narrowed to `FoldMatchingCore`** (`matchingFoldSupply_of_foldMatchingCore`): ξ-weight discharged; open = the α-series fold data + count | `_SYZ12BCIKS57Chunks56` |
| **C6** | `HeavyPinSupply` | **DONE given one inequality** (`heavyPinSupply_of_discBudget`): `S₀ := locus`, pigeonhole via `Match304.card_nonvanishing_gt`; open = `hHeavyBudget` counting | `_SYZ12BCIKS57Chunks56` |

Composition (all machine-checked, axiom-clean):
`HenselBranchSupply` (+ base facts) →[C2 SYZ14]→ `PlaceCurveSupply` →[C3 `gradedYRootSupply_of_placeCurve`]→ `GradedYRootSupply` →[C4/C5/C6 supplies]→ `DiscLocusCellData` →[SYZ8]→ `CellPackageSupplyDiscLocus` →[SYZ8/SYZ11 welds]→ `CellPackageSupply` →[`johnsonDischargeStatement_of_packageSupply`, Hab25JohnsonPackageSupply.lean]→ `JohnsonDischargeStatement` → production Johnson floor.

## The minimal open-Prop list (the entire program's open surface)

1. **`HenselBranchSupply`** (C2, this file) — the §5 branch handoff: the `Y`-root divisor
   `w, hwdvd` + GS split `G, hsplit` + global branch simplicity `hbranch` + the γ-representative
   `Ppoly, hrepG`. **`hrepG` is the true open object** (UNSAT literal at `d_H ≥ 2`; corrected =
   `T`-loaded `polyToPowerSeries𝕃T`).
2. **`MappedSliceSeparability g.hHyp`** (C4) — per-place separability of the doubly-mapped local
   `R` over `F⟦X⟧`; strictly below trivariate Node-B `R.Separable`; field-residue-producible
   (`MappedSliceSeparability.of_residue`).
3. **`FoldMatchingCore`** (C5) — the α-series fold-matching data `e, u₀, u₁, matchingSet, hfold`
   + the count `hcard`; genuine BCIKS §6 matching (cannot be `matchingSet = locus`).
4. **Numeric ceilings** (C4 `h_numeric` + C6 `hHeavyBudget` + C4 `hbase`) — roomy at production
   `|F₀| ≈ 2¹⁵⁸`; abstract over arbitrary `F₀`, so cell-side hypotheses. `hbase` (base agreement
   of `w` with `root` on the locus) is the SYZ11 boundary §5 branch handoff — with root now
   DERIVED as `w(x₀,z)`, `hbase` is `(w.eval (C x₀)).eval z = (rootDecoded …).1`, which
   `rootDecoded_val_monic` makes definitional; so it is discharged the moment `HenselBranchSupply`
   supplies the divisor. (Recorded for the successor round.)

## Build

`lake env lean` on the file (deps `_SYZ11BCIKS57Chunk3`, `DecodedRootSupply` oleans warm under
`.lake/build/lib/lean/`). Lockless, ~14s. Commit `feat(#466 SYZ14): …`.
