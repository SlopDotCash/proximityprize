# SYZ10: BCIKS20 Claim 5.7 formalization program — chunk plan + chunk 1 (2026-07-10)

## Goal

Discharge the single remaining known-math obstacle to the production Johnson floor jump
`(1−ρ)/3 ≈ 0.16667 → 1−√ρ ≈ 0.29289`: the residual `CellPackageSupplyDiscLocus`
(`Frontier/_SYZ8CellPackageSupply.lean`), the disc-locus (strictly-smaller) form of the
[BCIKS20] Claim 5.7 per-cell heavy-agreement package supply. Landing it feeds
`johnsonDischargeStatement_of_discLocusSupply` / `production_good_johnson_of_discLocusSupply`
(both already axiom-clean in SYZ8) and thence `firstPrime_rateHalf_ladder_floor_johnson`.

The residual asks: for each *large* cell `(u, R, E, P)` (R irreducible, E a set of decoded
scalars sharing a near-codeword divisor), produce a `DiscLocusCellData domain k δ u R H` bundle
— an irreducible positive-degree monic place curve `H` with `Hypotheses x₀ R H`, its degree
grading `(D, hd2, hdHD, hD_Rx0, hRgrade)`, γ-series representation `(Ppoly, hrepG)`, the
rational-root section `root`, the Y-root divisor `w` with `(X−C w) ∣ R`, a nonzero discriminant
`disc` with budget `gradedCardBudget + deg disc < |F₀|` and single base/separability
certificates over `disc.eval z ≠ 0`, per-coordinate matching sets in that locus folding
correctly with `killBudget·deg H < |matchingSet j|`, and a heavy set `S₀` in that locus with
`max Bw 1 < |S₀|`.

## Chunk plan (6 chunks), mapped to BCIKS20 §5–§6 and to the `DiscLocusCellData` field groups

Each chunk = a self-contained axiom-clean Lean file exporting a named interface Prop that the
next chunk consumes. Field-group labels reference the `DiscLocusCellData` fields in SYZ8.

| Chunk | BCIKS §step | DiscLocusCellData fields produced | Interface Prop (output) | Difficulty | In-tree support |
|---|---|---|---|---|---|
| **C1** surface / interpolation existence | §5 GS surface | (produces the raw interpolant `Q`; feeds H selection) | `SurfaceInterpolantSupply k n m ωs f` | **LOW — adaptor (LANDED)** | `gs_existence`, `Conditions` fully in-tree |
| **C2** irreducible factor selection + Hypotheses | §5–§6 factor of `Q`, place curve | `H`, `Fact (Irreducible H)`, `Fact (0<natDegree)`, `hmonic`, `x₀`, `hHyp : Hypotheses x₀ R H` | `PlaceCurveSupply` (∃ H irred monic + Hypotheses from a surface) | **HIGH — genuine open AG** | `Hypotheses` def, `H_tilde'`, `WfDvd`/`UFD` factorization in Mathlib; irreducible-with-hypotheses selection NOT in-tree |
| **C3** degree grading + γ-series representation | §5 weighted-degree bookkeeping | `D, hD, hd2, hdHD, hD_Rx0, hRgrade`, `Ppoly, hrepG`, `root`, `w, hwdeg, hwdvd` | `GradedYRootSupply` | **MED-HIGH** | `Bivariate.totalDegree/degreeX/natDegreeY`, `gammaGenuine`, `polyToPowerSeries𝕃`, `rationalRoot_of_*`, `betaRec`; Y-root divisor construction partly in `CurveHenselSupply` |
| **C4** discriminant nonvanishing + degree budget | §6 discriminant geometry | `disc, hdisc, hbaseT, hsepT, hbig` | `DiscBudgetSupply` | **MED-HIGH** | `resultant` (Mathlib), `gradedCardBudget`+`gradedCardBudget_mono`, `DiscriminantBadSet`, separability wrappers (`LinearCentreCertificates`, `GSSurfaceMappedSeparability`); the "one nonzero disc controlling base+separability off its locus" is the open piece |
| **C5** matching-set fold agreement + killBudget count | §6 heavy-agreement counting | `e, he, u₀, u₁, matchingSet, hmatchSub, hfold, xw, hξw, hcard` | `MatchingFoldSupply` | **MED** | `killBudget`, `weight_Λ_over_𝒪`+`betaRec_weight_le_graded`, `card_matching_gt_of_disc`, `discLocus`-style counting (`card_nonvanishing_gt`); fold identity from `w` is the work |
| **C6** heavy pinning `S₀` | §6 heavy set pin | `S₀, hS₀sub, Bw, hBw, hS₀` | `HeavyPinSupply` → assembles `DiscLocusCellData` ⇒ `CellPackageSupplyDiscLocus` | **MED** | `card_nonvanishing_gt` gives `≥ |F₀|−deg disc` locus points; Taylor-coeff degree bound `Bw` is elementary; final assembly is field-by-field |

Assembly: C2–C6 outputs feed the `DiscLocusCellData` constructor; the top theorem
`cellPackageSupplyDiscLocus_of_supplies : PlaceCurveSupply → … → HeavyPinSupply →
CellPackageSupplyDiscLocus domain k δ T`, then wired through
`johnsonDischargeStatement_of_discLocusSupply`.

### Pure-algebra vs new-machinery split

* **Essentially in Mathlib / in-tree (plumbing):** C1 (done), C6 counting, the `resultant`
  object and `gradedCardBudget` monotonicity in C4, the `Bivariate` degree API in C3.
* **Genuine open mathematics (BCIKS §5–§6 content):** C2 (produce an *irreducible* place curve
  satisfying `Hypotheses` from the GS interpolant — Newton-polygon/branch selection) and the
  *nonvanishing* half of C4 (a single discriminant whose non-vanishing locus simultaneously
  certifies base agreement and separability). These are the substance of Claim 5.7 and are not
  one-session gaps; the chunk boundaries isolate them so the surrounding plumbing lands
  independently and axiom-clean.

## Chunk 1 — LANDED (axiom-clean)

File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ10BCIKS57Chunk1.lean`
(namespace `BCIKS20.CellPencilJohnson.SYZ10`).

Verbatim statements:

```
def SurfaceInterpolantSupply (k n m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) : Prop :=
  ∃ Q : F[X][Y], GuruswamiSudan.Conditions k m (gs_degree_bound k n m) ωs f Q

theorem surfaceInterpolantSupply {k n m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    SurfaceInterpolantSupply k n m ωs f :=
  GuruswamiSudan.gs_existence k n ωs f hk hn hm
```

Plus accessors `SurfaceInterpolantSupply.{surface, surface_conditions, surface_ne_zero,
surface_weightedDegree_le, surface_roots, surface_multiplicity}` projecting the chosen surface,
its `Q ≠ 0`, `(1,k−1)`-weighted-degree bound `≤ gs_degree_bound k n m`, per-point vanishing, and
order-`≥ m` bivariate `rootMultiplicity`.

**Status/honesty:** the substantive dimension-count (nonzero interpolant from
constraints < coefficients) is entirely the pre-existing, axiom-clean `GuruswamiSudan.gs_existence`
(`GuruswamiSudan/GuruswamiSudan.lean`; supporting counts in `MonomialCount.lean:89
exists_ne_zero_vanishesToOrder_of_partial_sum`). Chunk 1 adds **no new mathematics** — it fixes
the interface boundary (names the §5 surface step as a composable Prop) so Chunk 2 consumes it
without re-deriving the count. `#print axioms` on all five declarations: `[propext,
Classical.choice, Quot.sound]` — clean.

**Honest gap between C1 and C2:** C1 delivers a surface `Q(X,Y)` parameterized by concrete
interpolation data `(ωs, f)`. The cell context of `CellPackageSupplyDiscLocus` is abstract
`(domain, u, R, E, P)`; instantiating `(ωs, f)` from a large cell (the received-word / decoded
divisor data) is part of C2's remit, not yet done. So C1 is a *reusable building block*, not yet
wired into the residual's cell quantifier.

## Inventory highlights (for later chunks)

* GS interpolation: `GuruswamiSudan.{Conditions, gs_existence, gs_divisibility}`;
  dim-count `MonomialCount.lean:89`; trivariate `TrivariateInterpolation.lean`.
* `Hypotheses` = `RationalFunctionsCore.lean:2170`; `gammaGenuine` = `BCIKS20/GammaGenuine.lean:174`;
  `weight_Λ_over_𝒪` = `RationalFunctionsCore.lean:692`; `killBudget` = `BCIKS20/Supply.lean:97`;
  `polyToPowerSeries𝕃` = `RationalFunctionsCore.lean:2007`.
* Disc/budget: Mathlib `resultant` (`RingTheory/Polynomial/Resultant/Basic.lean:139`);
  in-tree `gradedCardBudget` (`ToMathlib/BetaWeightGradedSupply.lean:60`), `DiscriminantBadSet.lean`
  (`card_nonvanishing_gt`, `card_matching_gt_of_disc`). No univariate `Polynomial.discriminant`
  in Mathlib — must build from `resultant` if needed in C4.
* Bivariate degree API in CompPoly dep (`BivariateDegree.lean`): `totalDegree/degreeX/natDegreeY/
  evalX/weightedDegree/natWeightedDegree`; `rootMultiplicity` in `BivariateMultiplicity.lean`.
* `rationalRoot`/`H_tilde'` = `RationalFunctionsCore.lean:587/180`; Hensel machinery
  `HenselNumerator.lean`, `BetaRecursion.lean`, `Data/Polynomial/HenselExistence.lean`.

## Files

* New: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ10BCIKS57Chunk1.lean`
* Consumes: `GuruswamiSudan/GuruswamiSudan.lean` (`gs_existence`, `Conditions`),
  `GuruswamiSudan/Basic.lean` (`gs_degree_bound`).
* Target (later chunks): `Frontier/_SYZ8CellPackageSupply.lean`
  (`DiscLocusCellData`, `CellPackageSupplyDiscLocus`).
