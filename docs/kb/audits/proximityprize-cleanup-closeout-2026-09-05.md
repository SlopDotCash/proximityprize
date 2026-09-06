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
  cleanup. Dependency-closed upstream contributions remain a separate review; branch
  disposition is recorded below.

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

## Historical branch disposition

The following remote refs were deleted using exact-tip leases after checking live
PR state and local worktrees. None was checked out locally:

| Branch | Deleted tip | Evidence |
| --- | --- | --- |
| `codex/migrate-to-slopdotcash-org` | `bbf7f8cd80187e566efc719ba4c63d73a58694ee` | Ancestor of main; PR #50 merged |
| `slop-project-authority` | `fd1323dd5c4bd293c1d3fb2f4343025e01c8dc51` | Ancestor of main; PR #28 merged |
| `codex/slop-policy-2026-08-18-1` | `b32d08b557d244ef1c73a832285d5fd463a4f563` | PR #48 merged this exact head; patch-equivalent commit on main |
| `fix/codex-refresh-kb-after-pr31` | `8c188b97a03b3db6d868c6e1dad348d3b09fefb7` | PR #45 merged this exact head; patch-equivalent commit on main |

`codex/port-arklib-pr-513` remains: seven unique commits and closed, unmerged PR #9
explicitly preserving the design for possible revival. `codex/port-arklib-pr-537`
remains: three unique commits and superseded but unmerged PR #8. Closure of a PR
alone is not merge evidence. The historical `automation/kb-generated-*`,
`codex/r382-half-radius-mds-line`, and `integrate/goal-2026-07-09` refs were already
absent. Current work branches were not pruning candidates.
