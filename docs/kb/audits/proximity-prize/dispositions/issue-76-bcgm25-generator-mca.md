# Issue #76 - BCGM25 Polynomial-Generator MCA API Split

Status: resolved on 2026-06-06.

Decision:

- Keep the canonical CapacityBounds front door in the generator-native framework:
  `CodingTheory.polynomialGenerator_isMCAGenerator_bcgm25`.
- State that front door in terms of `CoreDefinitions.IsPolynomialGenerator` and
  `CoreDefinitions.IsMCAGenerator`.
- Retain `CodingTheory.subspaceDesign_epsCA_curves_polynomial_generators_bcgm25` only as the
  historical ABF26 survey-ledger compatibility shadow.
- Do not prove the old `epsCA_curves` shadow from the generator-native statement in this pass:
  current `IsMCAGenerator` is a scalar-code API, while the old shadow is a vector-alphabet
  `epsCA_curves` statement. A checked bridge would need a separate curve-MCA/curve-CA adapter.

Regression search:

```sh
rg -n 'BCGM25|BSGM25|polynomial-generator|IsMCAGenerator|IsPolynomialGenerator|subspaceDesign_epsCA_curves_polynomial_generators_bcgm25|epsCA_curves' \
  Research/ProximityPrize/CapacityBounds.lean \
  ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean \
  ArkLib/Data/CodingTheory/ProximityGap/MCAGenerator.lean \
  docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md \
  docs/kb/audits/proximity-prize/dispositions/issue-76-bcgm25-generator-mca.md
```

Expected result:

- `polynomialGenerator_isMCAGenerator_bcgm25` is the canonical external theorem surface.
- `subspaceDesign_epsCA_curves_polynomial_generators_bcgm25` remains documented as a
  compatibility shadow, not the API to extend.
- No audit text still says the generator framework is pending in an external PR.
