# Generated and Derived Files

Edit the source of truth, not the output.

| Path | What it is | Edit directly? | Source of truth / refresh path |
| --- | --- | --- | --- |
| `CLAUDE.md` | compatibility symlink | No | Edit `AGENTS.md` |
| `ArkLib.lean` | generated Proximity Prize umbrella imports | No | `./scripts/update-lib.sh` or `./scripts/check-imports.sh` |
| `.lake/` | build artifacts and cache | No | `lake build`, `lake exe cache get` |
| `blueprint/web/`, `blueprint/print/` | generated blueprint output | No | `leanblueprint web`, `leanblueprint pdf`, or `./scripts/build-web.sh` |
| `blueprint/src/print.pdf` | generated blueprint PDF inside source tree | No | `leanblueprint pdf` |
| `home_page/docs/` | copied API docs for the site | No | `./scripts/build-web.sh` |
| `dependency_graphs/` | generated dependency visualizations | No | rerun scripts under `scripts/dependency_analysis/` |
| `docs/kb/_generated/references.json` | normalized bibliography export | No | `python3 ./scripts/kb/sync_from_bib.py` |
| `docs/kb/_generated/lean-citations.json` | generated map from Lean files to cited keys | No | `python3 ./scripts/kb/extract_lean_citations.py` |
| `docs/kb/_generated/declarations.json` | declaration catalog across `ArkLib/` (file, line, kind, namespace, name, brief signature, docstring head) | No | `python3 ./scripts/kb/extract_declarations.py` |
| `docs/kb/_generated/dedup-report.md` | duplicate-candidate review aid (same-short-name groups + cross-file near-duplicate docstrings) derived from the catalog | No | `python3 ./scripts/kb/find_dedup_candidates.py` |

## Important Notes

- `./scripts/update-lib.sh` imports the tracked modules under
  `ArkLib/Data/CodingTheory/ProximityGap/` plus its root module. Their transitive imports retain
  the required ArkLib substrate without making unrelated proof-system experiments default build
  targets. Four explicitly documented performance-blocked frontier experiments (`_FSMA...`,
  `_FSMC...`, `_P1RateQuarterSharedFreshTripleRefuted`, and
  `_P1RateQuarterCommonFactorConcreteLocatorAttempt`) remain direct-check lanes rather than CI
  umbrella imports. The script still fails fast if untracked Lean files would be skipped.
- Generated site and blueprint output are for review and deployment, not authoring.
- If a path looks derived, confirm its source of truth before editing it.

## Local knowledge-base catalogs

`declarations.json` and `dedup-report.md` are ignored local outputs. On a fresh
checkout, `python3 scripts/kb/check_generated.py` materializes both from the current
Lean sources before checking and linting the knowledge base. Tracked bibliography
and citation exports still require committed updates. If either catalog is tracked
(on an older branch), the checker continues to reject stale contents.

The KB workflow checks both tracked changes and newly scaffolded paper/source
files with `git status --porcelain --untracked-files=all`. A plain `git diff` misses
new paper stubs and can incorrectly pass after regeneration. Ignored local catalogs
are intentionally excluded from this commitment check.

## Research evidence retention

The standalone campaign retains `scripts/probes/`, `_nubs_research/`,
`_research_357/`, `_research_ll/`, and `scratchpad/` as research evidence.
The pre-migration cleanup proposal in issue #2 is not authorization to treat
unreferenced probes as disposable. Neither absence from CI nor a missing filename
mention establishes that an experiment's conclusions were distilled elsewhere.

Run `python3 scripts/kb/audit_probe_retention.py --output /tmp/probe-retention.json`
from a clean snapshot with every tracked file present (use a fresh worktree if
local deletions are pending). The command reads working-tree contents and fails
if a tracked file is missing; it does not reconstruct deleted files from Git.
It produces a tracked-file inventory with byte counts, SHA-256 fingerprints, and direct
filename-reference pointers from the current tree. It does not run the probes or
certify their mathematical claims. All entries have an explicit retain disposition;
manual claim-level review is required before any future deletion. Keep this large
inventory local and regenerate it when reviewing a proposed removal.
