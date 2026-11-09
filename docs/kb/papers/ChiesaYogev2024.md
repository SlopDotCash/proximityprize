---
kind: paper
bibkey: ChiesaYogev2024
title: "Building Cryptographic Proofs from Hash Functions"
year: 2024
bib_source: website/blueprint/src/references.bib
canonical_url: https://github.com/hash-based-snargs-book
source_metadata: ../sources/ChiesaYogev2024/metadata.yml
status: seeded
related_concepts:
  - oracle-reductions
related_modules:
  - ArkLib/OracleReduction/BCS/Basic.lean
  - ArkLib/OracleReduction/FiatShamir/Basic.lean
---

# ChiesaYogev2024

## At A Glance

`ChiesaYogev2024` is the textbook reference for building cryptographic proofs from hash
functions. ArkLib cites it in the oracle-reduction layer, especially around the BCS transform and
Fiat-Shamir treatment.

## What ArkLib Uses From This Paper

- Background for the BCS transformation from oracle reductions to ordinary reductions.
- Conceptual guidance for the hash-function and Fiat-Shamir layers used by ArkLib's oracle
  reduction framework.

## Main ArkLib Touchpoints

- [`ArkLib/OracleReduction/BCS/Basic.lean`](../../../ArkLib/OracleReduction/BCS/Basic.lean)
  cites this textbook alongside the original BCS16 IOP reference.
- [`ArkLib/OracleReduction/FiatShamir/Basic.lean`](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean)
  states that the formalization mostly follows this treatment.
- [`docs/kb/concepts/oracle-reductions.md`](../concepts/oracle-reductions.md) records this book as
  background for ArkLib's oracle-reduction architecture.

## Source Access

- Source metadata: [`../sources/ChiesaYogev2024/metadata.yml`](../sources/ChiesaYogev2024/metadata.yml)
- Public reference: [`website/blueprint/src/references.bib`](../../../website/blueprint/src/references.bib)
