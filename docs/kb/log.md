# Knowledge Base Log

This file is append-only.
Each entry records a notable KB event: initialization, ingest, audit creation, or major update.

## [2026-04-15] initialize | docs/kb

Created the initial knowledge-base subtree:

- `docs/kb/README.md`
- `docs/kb/index.md`
- `docs/kb/log.md`
- `docs/kb/papers/`
- `docs/kb/concepts/`
- `docs/kb/audits/`
- `docs/kb/queries/`
- `docs/kb/sources/`
- `docs/kb/_generated/`

## [2026-04-15] seed | initial paper pages

Seeded the first repository-local paper pages for currently active or already cited references:

- `ACFY24`
- `ACFY24stir`
- `BCIKS20`
- `BCS16`
- `BBS24`
- `DP24`

## [2026-04-15] seed | citation coverage stubs

Scaffolded paper pages and source metadata for the remaining citation keys currently used in
`ArkLib/**/*.lean`:

- `AHIV22`
- `BSS08`
- `FRI1216`
- `GWZC19`
- `JM24`
- `LFKN92`
- `LPS24`
- `PS94`
- `Poseidon2`
- `STIR2005`
- `Spi95`
- `codingtheory`
- `listdecoding`

## [2026-04-15] generate | bibliography and citation registries

Added initial generated outputs:

- `docs/kb/_generated/references.json`
- `docs/kb/_generated/lean-citations.json`

using the new scripts under `scripts/kb/`.

## [2026-04-15] migrate | list-decoding audit

Promoted the existing paper audit into:

- `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`

and updated tracked wiki navigation to point to the KB copy rather than to a branch-local
untracked file.

## [2026-04-15] refine | high-value paper pages

Replaced initial stubs with ArkLib-specific summaries for:

- `AHIV22`
- `LFKN92`
- `GWZC19`
- `FRI1216`

These are now better landing pages for active review and protocol work in the `InterleavedCode`,
`Sumcheck`, `Plonk`, and `Fri` subtrees.

## [2026-04-15] automate | review context helper

Added:

- `scripts/kb/review_context.py`

to resolve citation keys, KB paper pages, source metadata, and public URLs from explicit keys or
changed Lean files, with output shaped for `.github/workflows/review.yml`.

## [2026-04-15] refine | second paper-page batch

Replaced initial stubs with ArkLib-specific summaries for:

- `JM24`
- `LPS24`
- `Poseidon2`
- `BSS08`
- `STIR2005`
- `listdecoding`
- `codingtheory`

This improves the KB coverage for the `AGM`, `Data/Hash`, `ProofSystem/Stir`, and
`JohnsonBound` areas.

## [2026-04-15] refine | final cited-paper stubs

Replaced the remaining cited-paper stubs with ArkLib-specific summaries for:

- `PS94`
- `Spi95`

and added a concept hub:

- `docs/kb/concepts/polishchuk-spielman-lineage.md`

for the corrected-vs-original Polishchuk-Spielman source lineage.

## [2026-05-03] audit | BCIKS20 Appendix A rational functions

Added:

- `docs/kb/audits/bciks20-appendix-a-rational-functions.md`

to track the rational-function and Hensel-lifting declarations supporting the BCIKS20
list-decoding branch.

## [2026-06-04] concept | oracle-reductions architecture page

Added the concept page requested in issue #480:

- `docs/kb/concepts/oracle-reductions.md`

It documents the IOR layer conceptually (prover/verifier interaction model, oracle verifiers and the
`embed` mechanism, the Basic/Execution/Security separation of concerns, reduction-style security, and
sequential composition + BCS transform), grounded in the real `ArkLib/OracleReduction/**` modules. It
cross-links with `concepts/interactive-oracle-proofs.md` and is registered in `index.md` and
`concepts/README.md`. Per the maintainer, no docstrings were added to `Basic.lean` (rewrite in #433).

## [2026-05-03] prove | BCIKS20 function-field regularity API

Updated `ArkLib/Data/Polynomial/RationalFunctions.lean` with an explicit function-field `T`
variable, regular-element closure lemmas, and a concrete low-degree `ξ` regularity helper.
The Appendix A rational-functions audit now records this as the next denominator-clearing layer
toward `ClaimA2.ξ_regular`.

## [2026-06-13] synthesize | power-word zero-sum list law for delta*

Added:

- `docs/kb/deltastar-powerword-zero-sum-law-2026-06-13.md`

to record the exact all-`k` power-word sub-Johnson list identity from
`PowerWordListBound.lean`, its ten connections to the #389/#371 supply programme, and the
next symmetric-function fiber targets.

## [2026-06-26] refine | delta-star slack-profile cap equivalence

Updated:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberSlackDominance.lean`
- `docs/kb/deltastar-464-profile-slack-dominance-2026-06-26.md`
- `docs/kb/deltastar-464-profile-slack-cap-collapse-2026-06-26.md`

to record that a slack-profile representative scheme is exactly the existing profile-cap interface
with the induced cap `bad(rep p) + slack p`.  The update adds axiom-clean equivalence lemmas and
preserves the critical conclusion: only a genuine compressed-profile stability theorem would make
the route mathematically stronger than direct profile caps.

## [2026-06-26] prove | profile-fiber oscillation certificate

Extended:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberSlackDominance.lean`
- `docs/kb/deltastar-464-profile-slack-dominance-2026-06-26.md`

with `ProfileRepresentativeInFiber`, `ProfileFiberOscillationBounded`, and
`ProfileFiberOscillationCertificate`.  The new certificate proves the existing slack certificate,
feeds the same open-core and delta-star consumers, and has an exact three-way failure surface:
representative misses its used fiber, same-profile oscillation exceeds slack, or the
representative-plus-slack budget is above `B`.  Endpoint lemmas make explicit that the coarsest
profile collapses oscillation back to a global pairwise bad-count diameter bound, while the identity
profile, and more generally any injective profile with zero slack and in-fiber representatives, are
exactly the original all-stack incidence theorem.

## [2026-06-26] refine | profile granularity endpoints

Added:

- `docs/kb/deltastar-464-profile-granularity-endpoints-2026-06-26.md`

to tie the stack-profile cardinality tradeoff to the slack-profile proof obligations.  The note
records the two dead endpoints: constant profiles require global pairwise oscillation control, while
injective profiles are just relabelings of the all-stack theorem.  The remaining live target is a
genuinely non-injective profile with a real same-fiber oscillation theorem.
