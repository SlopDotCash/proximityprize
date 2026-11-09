---
kind: paper
bibkey: AFK22
title: "Fiat-Shamir Transformation of Multi-Round Interactive Proofs"
year: "2022"
bib_source: website/blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2021/1377
source_metadata: ../sources/AFK22/metadata.yml
status: seeded
related_modules:
  - ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean
---

# AFK22

## At A Glance

`AFK22` analyzes the Fiat–Shamir transformation of multi-round public-coin interactive proofs,
showing that for `(k₁, …, kμ)`-special-sound protocols the soundness/knowledge loss is much smaller
than the generic `Qᵘ` bound. For ArkLib it is the reference for the **rewinding / forking** analysis
that turns (coordinate-wise) special soundness into knowledge soundness.

## What ArkLib Uses From This Paper

- The tree-of-transcripts extraction strategy and forking analysis for multi-round special-sound
  protocols, which underlies ArkLib's intended proof of
  `coordinateWiseSpecialSound_implies_knowledgeSoundness`.

## Main ArkLib Touchpoints

- [`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean`](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean)
  formerly cited `AFK22` for the Fiat–Shamir / forking analysis backing the rewinding knowledge
  extractor. The current umbrella re-exports the `Basic`/`Composition` development and no longer
  carries that citation (see the gap entry below).
- [`ArkLib/ToMathlib/RewindingExtractor.lean`](../../../ArkLib/ToMathlib/RewindingExtractor.lean)
  — the abstract rewinding-extractor framework, which records the knowledge-soundness implication
  as a blocked residual.

## Version Notes

- TCC 2022 (Springer LNCS); extended version in Journal of Cryptology, 2023. ePrint 2021/1377.

## Known Divergences From ArkLib

- ArkLib's tree of transcripts (`ChallengeTree`) branches only at challenge rounds and is
  arity-indexed (`ArkLib/OracleReduction/Security/TranscriptTree/Basic.lean`). The intended forking
  primitive is `VCVio.CryptoFoundations.forkReplay` rather than the paper's abstract rewinding
  argument; it is named only in the documentation of `ArkLib/ToMathlib/RewindingExtractor.lean` as
  the operational counterpart, and no current ArkLib proof uses it.

## Open Formalization Gaps

- The forking-based construction of an accepting, structured tree from a single prover — the core of
  the knowledge-soundness implication — is not yet formalized. *(Updated 2026-10-28, audit T48: the
  earlier entry located this as a `sorry` in a named implication theorem under the old umbrella
  path. That location is stale. `CoordinateWiseSpecialSoundness.lean` now only re-exports the
  `Basic`/`Composition` development, and no `coordinateWiseSpecialSound_implies_knowledgeSoundness`
  theorem, `forkReplay` use or `AFK22` citation remains in the current CWSS / `TranscriptTree`
  tree. The implication is recorded as a blocked residual in
  `ArkLib/ToMathlib/RewindingExtractor.lean`. This is a documentation correction, not evidence of a
  live `sorry` or a new proof of the paper's extractor.)*

## Source Access

- Source metadata: [`../sources/AFK22/metadata.yml`](../sources/AFK22/metadata.yml)
- Public reference: [`website/blueprint/src/references.bib`](../../../website/blueprint/src/references.bib)
