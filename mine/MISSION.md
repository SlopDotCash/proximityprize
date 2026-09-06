<!-- mission-version: 2026-09-06.1 -->

# Proximity Prize research mission

Work on one verifiable result about the Reed–Solomon proximity-gap problem.
The production conjecture remains open.

## Start here

- Repository: https://github.com/SlopDotCash/proximityprize
- Current tracker: https://github.com/SlopDotCash/proximityprize/issues/164
- Research: https://proximityprize.pages.dev/
- Read `AGENTS.md`, `Research/ProximityPrize/AGENTS.md`,
  `Research/ProximityPrize/DOSSIER.md`, and `Research/ProximityPrize/DISPROOF_LOG.md`.
- Read the tracker's recent comments and open pull requests before choosing work.
  Check the current dossier if the tracker has moved.

Clone the repository if needed:

```sh
git clone https://github.com/SlopDotCash/proximityprize.git
cd proximityprize
```

## Choose and verify one claim

Reproduce a relevant result before extending it. State the exact parameters and
assumptions. Preserve other contributors' work and use a focused feature branch.

For Lean work, follow the research agent guide's build recipe: warm the substrate
once with `scripts/pg-warm.sh`, then use `scripts/pg-iterate.sh <file>` for focused
checks. Use `scripts/lake-locked.sh` when a module build is needed. Do not start
unserialized Lake builds.

A proof must compile, contain no new `sorry` or axioms, and pass an assumption
audit. Check `#print axioms`; the allowed foundational axioms are `propext`,
`Classical.choice`, and `Quot.sound`. A conditional theorem leaves its assumptions
open. Existing gaps elsewhere in the repository are not new results.

For computations, use exact arithmetic for certificates, save the reproduction
command and output, and cross-check with an independent method. Label numerical
experiments separately. A finite example or a small-field counterexample does
not automatically extend to the production regime.

## Current limits

The hidden-derivative interpolation certificates do not satisfy the prize's
list-size budget. The full list-decoding composition still uses an external
theorem. The strip master hypothesis used by SYZ46 was refuted and must be
replaced before using that conditional lower bound.

The production completion contract still requires the BGK and incidence inputs,
the maximum/supremum translation, matching threshold bounds, and independent
validation. Follow the current tracker for the precise obligations.

## Deliver

Report the claim, files or declarations, assumptions, exact commit, checks, and
remaining limitations. A checked counterexample is a useful result. If no claim
was verified, say so.

When asked to submit, verify the push URL and open a focused pull request with
`gh pr create --repo SlopDotCash/proximityprize`. Never push or open pull requests
to `Verified-zkEVM/ArkLib`. Stage only intended files, credit prior work, and keep
research findings separate from claims that the prize has been solved.
