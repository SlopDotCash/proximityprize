# ArkLib proof-gap index (2026-06-06)

This index closes the umbrella audit role for ArkLib proof gaps. It records how to reproduce the
census and where each named residual family is tracked. Focused issues own the remaining proof work;
this document prevents the same residual surfaces from being rediscovered as anonymous holes.

## Audit commands

Raw proof holes and project-level assumptions:

```sh
rg -n --glob '*.lean' '^\s*(sorry|admit)\b|:=\s*(by\s+)?(sorry|admit)\b|by\s+(sorry|admit)\b|\baxiom\s+[A-Za-z_]|opaque\s+[A-Za-z_]' ArkLib
```

Current clean-tree census (2026-06-06, `python3 scripts/sorry_census.py`):

```json
{
  "total_tokens": 310,
  "holes": 0,
  "doc_mentions": 310,
  "files_with_holes": 0,
  "decls_with_holes": 0
}
```

Named residual APIs:

```sh
rg -n --glob '*.lean' '^(noncomputable\s+)?(def|structure|class|theorem|lemma)\s+\w*Residual\w*|\b\w*Residual\w*\s*:' ArkLib
```

Placeholders, explicit hypotheses, and roadmap markers:

```sh
rg -n --glob '*.lean' 'opaque\s+\w+|placeholder|stub|TODO|FIXME|named residual|explicit hypothesis|remaining unproven|only remaining|sole residual|single remaining' ArkLib
```

## Focused issue map

| Residual surface | Tracking issue |
|---|---|
| BCIKS20 correlated agreement: `StrictCoeffPolysResidual`, `BoundaryCardResidual` | #7 |
| BCIKS20 Claim 5.7 graph/count/factorization residuals | #8 |
| BCIKS20 Appendix-A Hensel term weights and Faà-di-Bruno vanishing | #9 |
| BCIKS20 Appendix-A P1 `DivWeightLe` / structured βHensel weight invariant | #89 |
| BCIKS20 Appendix-A P2 `RestrictedFaaDiBrunoMatch` / `B_coeff` prefactor re-keying | #90 |
| Hab25 Johnson MCA residuals | #10 |
| ABF26 Lemma 4.6 hard direction | #11 |
| GG25 line-decodability multi-gamma coverage | #12 |
| LogUp Protocol 2 completeness and soundness residuals | #13 |
| Batched FRI query-round soundness residuals | #14 |
| Duplex-sponge Fiat-Shamir statistical-distance placeholder | #15 |
| Zero-knowledge and HVZK definitions / FS transfer surface | #112 |
| ToyProblem KoalaBear concrete carrier replacement | #16 (closed; see #18/#30 for remaining anchors) |
| SendWitness knowledge-soundness placeholder reductions | #17 |
| ToyProblem protocol and leaderboard residual anchors | #18 |
| RingSwitching and Binius completeness plumbing | #19 |
| WHIR MCA conjecture placeholders and envelope bounds | #20 |
| WHIR Vector IOPP construction, perfect completeness, and RBR soundness assembly | #113 |
| External list-decoding, Johnson, interleaving, and subspace-design APIs | #21 |
| CS25/BCHKS/BGKS bridges and deep-hole probability inputs | #22 |
| BCHKS25 field-sized close-RS list `BadLineWitness` construction | #103 |
| BGKS20 char-2 `NearCertainBadLine` separation witness | #104 |
| Historical proximity-prize docs and inventories | #23 |
| FRI/STIR soundness accounting and proximity-gap residuals | #24 |
| Composed FRI folding reduction perfect completeness | #117 |
| OracleReduction sequential composition and Fiat-Shamir run equality | #25 |
| Commitment/folding placeholder modules | #26 |
| Merkle probabilistic RO-collision binding and simulation-based salted hiding | #119 |
| L13 beta existence with `betaRec` witness | #27 |
| ToyProblem rewinding-extractor framework | #28 |
| RingSwitching KState weakening | #29 |
| KoalaBear numeric anchors | #30 |
| L6.12 ToyStep4/SoundnessBounds integration | #31 |
| Leaderboard Fenzi-Sanso KoalaBear winning-set cardinality residual | #106 |
| Binius new-API Prelude and Basic call sites | #32 |
| Binius step residuals after Prelude port | #33 |
| Toolchain and Mathlib rebuild stabilization | #34 |
| Axiom audits pending toolchain rebuild | #35 |
| Final global verification report refresh | #36 |
| BKR06 final arithmetic side conditions | #38 |
| Grand MCA radius-one middle-band extremal count | #39 |
| Upstream PRs to Verified-zkEVM/ArkLib | #44 |
| ABF26 errata to Proximity Prize judges | #45 |
| ABF26 §4 CapacityBounds external CA/MCA theorem family | #48 |
| Johnson-family bounds: Joh62 Jqℓ + MDS Johnson corollary | #49 |
| GGR11 interleaved list-size recursion + erase-decode tree | #50 |
| Multiplicative rigidity: product-coset + in-band cluster bounds | #51 |
| MCAGS beyond-UDR GS-list mass bound | #52 |
| ABF26 §3 list-decoding theorem family | #54 |
| ABF26 T2.18 UM subspace-design half | #92 |
| CZ25 guarded dimension-count residual `CZ25SpanBound'` | #93 |
| CZ25 folded-RS capacity from T3.4/T2.18 inputs | #94 |
| AGL24 random Reed-Solomon near-capacity list decoding | #95 |
| AGL23/BDG24 counting-extraction barrier residual | #96 |
| Grand challenges MCA-attainment counterpart / stale reference | #55 |
| Grand LD four-rate numeric Johnson/Elias certificates | #56 |
| Grand LD OrdinaryRSCapacityAtPrizeRates Lambda-Elias frontier | #101 |
| Grand LD four-rate Elias-volume adjacent certificates | #102 |
| Grand MCA faithful lattice-threshold brackets at four rates | #57 |
| Grand challenges singular/plural lattice encoding bridges | #58 |
| Proximity Prize apex four-rate `mcaPrize` / `listDecodingPrize` deliverable | #120 |
| Proximity-prize audit doc refresh (this index family) | #59 |
| Root build / validation regressions after #36 | #60 |
| Proximity Prize betaRec-to-hcoeffPoly keystone assembly | #61 |
| BCIKS20 Section 5 `hPz` supplier from per-z Hensel/matching data | #91 |
| BCS compiler beyond statement-level scaffolding | #62 |
| ArkLib SNARK/proof-system completion obligations | #63 |
| Spartan second-sumcheck / final CheckClaim / composed PIOP security | #114 |
| Plonk gate/permutation soundness and full PIOP composition | #115 |
| Algebraic Group Model foundational lemmas and AGM-to-GGM transfer | #118 |
| BCIKS20 exact lattice boundary residual for the closed Johnson branch | #64 |
| Grand MCA J1 radius-1/n finite-algebra bad-scalar cap | #65 |
| Grand MCA beyond-UDR GS-row mass bound and faithfulness bridge | #66 |
| ABF26 T5.1 GKL24/GCXK25 first-moment bad-gamma residual | #67 |
| Hab25 Johnson-range MCA GS-over-F(Z) algebraic residual bundle | #68 |
| Grand LD faithful list-lattice threshold after the RIM refutation | #69 |
| Grand MCA four-rate faithful lattice-threshold numeric gap | #70 |
| ABF26 random RS uniform size-n subset probability primitive | #71 |
| ABF26/proximity-prize stale audit-doc refresh | #72 |
| GGR11 Erase-Decode tree structure for interleaved list-size bounds | #73 |
| ABF26 §3 external list-decoding theorem families | #74 |
| ABF26 §4 CapacityBounds CA/MCA theorem families | #75 |
| DG25 L4.19 covering-radius sampling lower bound for `epsCA` | #77 |
| GLMRSW22 T3.11 random-linear first-moment probability residual | #79 |
| BCHKS25+KK25 T4.16 near-capacity `epsCA` lower bound | #81 |
| CS25 T4.17 qEntropy RS-ball-count lower witness | #82 |
| BCHKS25 T4.18 `epsCA` Johnson-jump witness family | #83 |
| GKL24/BGKS20 T4.11 1.5-Johnson CA/MCA theorem pair | #84 |
| BCHKS25 T4.12 Johnson-range RS `epsMCA` bound | #85 |
| GG25 T4.13/T4.14 subspace-design and folded-RS MCA up to capacity | #86 |
| BCHKS25 T4.9.2/R4.10 RS `epsCA` item-2 and small-loss corollary | #87 |
| AHIV17/AHIV22 T4.8 row-span to affine-line specialization | #88 |
| GG25 random-RS MCA over `SizeSubset` domains | #99 |
| BCGM25/BSGM25 polynomial-generator MCA preservation in the native API | #100 |

Closed second-pass issues (#37, #40-#43, #46-#47, #53) are recorded in the refreshed
proximity-prize index; see "Related indexes" below.

## Interpretation

The current tree should be read as residualized, not silently complete. A focused issue is the
source of ownership for each residual family. If a proof route is mathematically false or external
to ArkLib's current formal scope, it should be documented as such rather than hidden behind `True`,
`opaque`, or a broad placeholder.

## Related indexes

* `docs/kb/audits/proximity-prize/CURRENT-RESIDUALIZED-TREE-2026-06-06.md`
* `Research/ProximityPrize/PermanentlyBlocked.lean`
* `Research/ProximityPrize/ExternalDebt.lean`
