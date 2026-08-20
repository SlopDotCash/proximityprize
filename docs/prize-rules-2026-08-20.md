# Proximity Prize rules — dated capture of the official page

**Capture date:** 2026-08-20
**Source:** https://proximityprize.org/ (fetched 2026-08-20)
**Status:** candidate for maintainer ratification — not yet ratified

## Purpose

Issue #49 asks the repository maintainers to make the applicable prize rules
explicit and immutable so Slop can bind contribution receipts to a specific
versioned terms artifact. The official prize page currently labels its
conditions "Preliminary version" and reserves the judges' right to change them.
This file is a dated, immutable capture of the official page at a single point
in time, offered as the versioned rules artifact for the "ratified dated
capture" option in issue #49.

This document does **not** claim prize eligibility, ownership, or payment
authority for this repository. The prize is an external opportunity controlled
by the Ethereum Foundation and the prize judges.

## Captured conditions (verbatim summary of proximityprize.org, 2026-08-20)

The page is headed "Preliminary version" and states details may still change,
inviting feedback before the conditions are finalised.

### The challenges

Two grand challenges, formalised in *Open Problems in List Decoding and
Correlated Agreement* (Arnon, Boneh, Fenzi, 2026) (eprint 2026/680), for
Reed–Solomon codes `C := RS[F, L, k]` over a smooth evaluation domain
`L ⊆ F`, rate `ρ(C) := k/|L| ∈ {1/2, 1/4, 1/8, 1/16}`, target error
`ε* = 2^−128`, `|F|` sufficiently large:

1. **Grand MCA.** Determine the largest `δ*_C ∈ [0,1]` such that
   `ε_mca(C, δ*_C) ≤ ε*`.
2. **Grand list decoding.** For a constant `m`, determine the largest
   `δ*_C ∈ [0,1]` such that `|Λ(C^{≡m}, δ*_C)| ≤ ε*·|F|`.

The prize offers **$1,000,000** in awards.

### Submission guidelines (as captured)

1. Submissions by email to proximityprize@ethereum.org.
2. Considered only if passed scientific peer-review (reputable field-appropriate
   conference or journal).
3. Publicly available on an open repository (e.g. IACR ePrint or arXiv); the
   first public version is the formal timestamp; a major revision re-timestamps
   to the relevant revision.
4. Formal verification (e.g. Lean) encouraged but not required.
5. Conflicts of interest disclosed during submission.
6. Anyone eligible except the prize judges; unless otherwise specified, any
   award is shared equally among named authors.

The prize judges reserve the right to deviate from these guidelines in
exceptional cases, or to change the guidelines in the future.

### FAQ points most relevant to this repository (as captured)

- Partial results: encouraged, significant contribution even if partial.
- AI policy: AI-aided submissions allowed, but must be human-verified and
  edited, using standard language/notation; human authors are solely
  responsible for correctness.
- Splitting: judges/EF may split awards among multiple submissions, including
  partial, complementary, or independently obtained results.
- Grants: no grant system currently available.

### Prize judges (as captured)

- Dan Boneh (Stanford University)
- Giacomo Fenzi (EPFL)
- Gal Arnon (Bocconi University)

## Ratification request

Maintainers, please either:

- approve this dated capture as the applicable preliminary version for Slop
  receipt binding, or
- replace it with a different versioned, immutable rules artifact.

Until one of those decisions is merged, Slop will keep receipts in
`pending-authority-activation` and will continue to describe Delta Star as an
external opportunity controlled by the Ethereum Foundation and prize judges.
