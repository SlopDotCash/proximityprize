# Proximity Prize rules — versioned maintainer transcription

**Transcription date:** 2026-08-20
**Source:** https://proximityprize.org/
**Source response:** 13,891 bytes, SHA-256
`82618a3f0e407bef82e7e591cc316c89713c7fa2f48cdbc35bc2e6f589b7e5de`,
ETag `a9802432b0136fd3ab47795646a72e8f-ssl`
**Independent recheck:** 2026-08-22T17:43:34Z returned the same byte count,
SHA-256, and ETag
**Status:** this exact file is ratified only by its merge into `main` under
policy revision `2026-08-23.1`; a pull-request or fork copy is not authoritative

## Purpose

Issue #49 asks the repository maintainers to make the applicable prize rules
explicit and immutable so Slop can bind contribution receipts to a specific
versioned terms artifact. The official prize page currently labels its
conditions "Preliminary version" and reserves the judges' right to change them.
This file is a maintainer-authored, normalized transcription of the substantive
rules on the official page, offered as the versioned rules artifact for issue
#49. It is not the raw HTML response. The source-response metadata above lets a
reviewer distinguish this transcription from the fetched bytes and reproduce
the source boundary independently.

The official page remains controlling for any condition omitted or transcribed
incorrectly here. A future source change does not rewrite this file: maintainers
must review a successor artifact and explicitly update downstream bindings.

This document does **not** claim prize eligibility, ownership, or payment
authority for this repository. The prize is an external opportunity controlled
by the Ethereum Foundation and the prize judges.

## Repository allocation terms

Historical work keeps its Apache-2.0 grants and notices. Contributors accepting
policy revision `2026-08-23.1` retain copyright in their original contributions
and license them under both MIT and Apache-2.0. Accepted Proximity Prize work
is contributor-owned in aggregate; acceptance assigns no copyright and does
not infer joint ownership of another person's contribution.

If the external organizer awards prize money for a result whose included
contributors accepted that policy, 10% of the amount actually received is
allocated to Slop Cash and the remaining 90% is shared among the contributors
to that awarded result. The contributor split is based on the project's public,
evidence-backed contribution-share record and requires final approval from the
named authors, subject to the organizer's controlling rules. Historical
contributors are not bound retroactively and must affirm the policy before
their work or share is included. This is an allocation of an award if received,
not a representation that any award is guaranteed. Slop does not hold keys,
take custody, sign, or broadcast a prize payment.

## Transcribed conditions from proximityprize.org (2026-08-20)

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

- Submission contents: each submission must include a PDF that clearly states
  the claimed results, explains how they relate to the prize challenge, and
  situates them with respect to prior work. Additional material must be clearly
  labeled and may be included or hosted online and linked from the main PDF.
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

- approve this versioned transcription as the applicable preliminary rules
  artifact for Slop
  receipt binding, or
- replace it with a different versioned, immutable rules artifact.

Until one of those decisions is merged, Slop will keep receipts in
`pending-authority-activation` and will continue to describe Delta Star as an
external opportunity controlled by the Ethereum Foundation and prize judges.
