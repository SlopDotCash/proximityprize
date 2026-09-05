# Standalone cleanup reassessment — 2026-09-05

Base: `a6475f7c0` (`origin/main` at the start of this review).
This follows issue #2's post-migration comments; the historical fork-wide
campaign eviction plan does not describe this standalone repository.

## Current disposition

- The large `declarations.json` and `dedup-report.md` catalogs are already
  untracked and ignored. The checker materializes them from current Lean sources
  on a fresh checkout. No further untracking operation is needed.
- `scripts/probes/` has 413 tracked files. Together with `_nubs_research/`,
  `_research_357/`, `_research_ll/`, and `scratchpad/`, the retained research
  inventory contains 421 files / 2,950,303 bytes. The historical count of 409
  probes is obsolete.
- Direct filename references exist for 329 of those 421 artifacts. The other
  92 remain retained: lack of a filename reference is not evidence that the
  mathematical claim or counterexample is redundant. Filename matches are
  navigation aids, not verified claim mappings or proof checks.
- `_nubs_research/` contains a finite-field witness and its exact Python check;
  `_research_357/` contains a Stepanov extraction; `_research_ll/` contains a
  historical source extraction; `scratchpad/` contains four orbit-arc probes.
  This change deletes none of them. Their names alone do not establish obsolescence.
- `mine/` and `home_page/` remain product/site surfaces, outside this evidence
  cleanup. Remote branch pruning and dependency-closed upstream contributions
  require separate branch/dependency evidence and are not claimed here.

## Reproducible review

Run `python3 scripts/kb/audit_probe_retention.py --output /tmp/probe-retention.json`.
The JSON records every tracked artifact's path, byte size, SHA-256, direct source
references, and explicit retention disposition. The inventory excludes untracked
experiments and generated KB catalogs, and does not execute research programs.
Regenerate it for the exact tree under review instead of committing another large
catalog. Any future deletion needs a claim-level replacement and provenance review.

The KB workflow now detects newly scaffolded untracked paper/source pages as well
as tracked changes. Its former `git diff` check could miss the new files. Ignored
local catalogs continue to be excluded from the commitment requirement.

## Validation

- Fresh-checkout KB generated-state check and strict cited-page lint.
- Documentation integrity check.
- Temporary-repository regression checks: inventory hashes and exact filename
  references, exclusion of untracked research, retention of unreferenced evidence,
  detection of a new KB paper stub, and exclusion of an ignored local catalog.

No Lean proof sources or imports change; no mathematical closure is asserted.
