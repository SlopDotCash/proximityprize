# Generated and Derived Files

## Integrated library surfaces

[`scripts/arklib-upstream.json`](../../scripts/arklib-upstream.json) records the
reviewed canonical upstream revision and file inventory. `scripts/update-lib.sh`
uses that inventory to regenerate the `module` / `public import` root
`ArkLib.lean`, the classic `ProximityPrize.lean` and `ProximityPrize/Extensions.lean` umbrellas, and the
marked downstream-library ownership block in `lakefile.toml`. Stage added or
removed source files before regeneration. `scripts/check-imports.sh` checks these
surfaces together with `Research/ProximityPrize/All.lean` and the library/research
boundary. It also runs `scripts/integration/check_consolidation.py` once to
verify canonical Git provenance and the full import graph. New canonical modules must be added to the reviewed upstream inventory;
classic downstream modules retain their separate Lake library ownership.

Confirmed duplicate DSFS modules retain their former short import paths as shims;
the single implementation owners and exact pre-consolidation hashes are recorded in
`scripts/integration/duplex-clone-consolidation.json`. Port the implementation owner,
then verify the compatibility imports through the package build.

`CLAUDE.md` remains a compatibility symlink to the canonical `AGENTS.md`.
`docs/kb/_generated/declarations.json` and `dedup-report.md` are ignored local
catalogs; `scripts/kb/check_generated.py` materializes them when absent. Tracked
bibliography and citation exports still require regeneration and commitment in
this downstream repository. The source trees for these catalogs are `ArkLib/`,
`Research/`, and `ProximityPrize/`.

Edit the source of truth, not the output.

| Path | What it is | Edit directly? | Source of truth / refresh path |
| --- | --- | --- | --- |
| `ArkLib.lean`, `ProximityPrize.lean`, `ProximityPrize/Extensions.lean`, generated Lake ownership block | canonical and classic production module surfaces | No | `./scripts/update-lib.sh`; verify with `./scripts/check-imports.sh` |
| `Research/ProximityPrize/All.lean` | research import surface | No | `python3 scripts/update-research-lib.py` |
| `scripts/residual_census.json`, `docs/wiki/residual-census.md` | syntactic strict production residual inventory of `ArkLib/` and `ProximityPrize/` with source locations (heuristic labels, not a verified completion ledger) | Only the `> **Campaign addendum` blocks of the wiki page, which regeneration carries forward | `python3 scripts/residual_census.py --wiki-out docs/wiki/residual-census.md` |
| `.lake/` | build artifacts and cache | No | `./scripts/lake-locked.sh build`, `./scripts/lake-locked.sh exe cache get` |
| `blueprint/lean_decls` | referenced Lean declarations | No | official Lean blueprint post-parse callback over `blueprint/src/`; `leanblueprint web` refreshes it in CI |
| `blueprint/web/`, `blueprint/print/` | generated blueprint output | No | `leanblueprint web`, `leanblueprint pdf`, or `./scripts/build-web.sh` |
| `blueprint/src/print.pdf` | generated blueprint PDF inside source tree | No | `leanblueprint pdf` |
| `home_page/docs/` | copied API docs for the site | No | `./scripts/build-web.sh` |
| `dependency_graphs/` | generated dependency visualizations | No | rerun scripts under `scripts/dependency_analysis/` |
| `scripts/axiom_baseline.json` | kernel-level accounting of existing `sorryAx` debt | No | `./scripts/lake-locked.sh exe axiomsweep --update-baseline` after a complete locked build, only for verified closures or renames of existing debt. Baseline edits cannot authorize new debt. Native-trust taint prevents the update |
| `docs/kb/_generated/references.json` | normalized bibliography export | No | `python3 ./scripts/kb/sync_from_bib.py` |
| `docs/kb/_generated/lean-citations.json` | generated map from Lean files to cited keys | No | `python3 ./scripts/kb/extract_lean_citations.py` |
| `docs/kb/_generated/declarations.json` | local declaration catalog across `ArkLib/`, `Research/`, and `ProximityPrize/` (file, line, kind, namespace, name, brief signature, docstring head) | No | `python3 ./scripts/kb/extract_declarations.py` |
| `docs/kb/_generated/dedup-report.md` | duplicate-candidate review aid (same-short-name groups + cross-file near-duplicate docstrings) derived from the catalog | No | `python3 ./scripts/kb/find_dedup_candidates.py` |

## Important Notes

- The generators use tracked source paths in their respective `ArkLib/`, `ProximityPrize/`,
  and `Research/` trees and fail if untracked Lean files would be skipped.
  `git add` new paths before regenerating or running validation.
- The generator wraps any `public import` that would exceed 100 characters, placing its module
  name on an indented continuation line.
- After merging `main` into a branch that adds Lean files, rerun `./scripts/update-lib.sh` and
  stage every changed production surface and generated Lake ownership block; regenerate the
  research surface too when its inputs change. Resolving an umbrella conflict with only one
  side can omit modules. The canonical upstream inventory uses the
  [current file headers](module-system.md#the-canonical-file-shape); retained classic extensions
  keep their separate Lake target and source format.
  Keep compile-time canaries in the mirrored `ArkLibTest/` path, where `lake test` checks them
  without exporting test helpers through the production umbrella.
- Run `uv run --no-project --python 3.12 python ./scripts/kb/regenerate.py` when bibliography or
  Lean citations change. Commit the tracked indexes and any new cited-paper pages or source
  metadata it scaffolds. Declaration and dedup catalogs remain ignored local outputs.
- The read-only KB workflow checks regeneration on relevant pull requests and pushes to `main`
  and supports manual dispatch. When an index or scaffold is stale, regenerate it in the branch
  that changes its inputs.
- Generated site and blueprint output are for review and deployment, not authoring.
- If a path looks derived, confirm its source of truth before editing it.

## Reusing local documentation caches

The pinned local doc-gen4 backend stores collected module data in
`.lake/build/api-docs.db`; its `.lake/build/doc-data/` files include completion markers and
build traces. A bibliography change can invalidate dependency `docInfo` facets as well as
ArkLib's own docs, so a warm Lean build can still need substantial documentation regeneration.
When reusing a completed documentation cache between matching dependency/bibliography snapshots,
wait for all documentation writers in both the source and destination to finish. Take a
consistent SQLite backup, including committed WAL pages, together with its matching module/core
`doc-data/` artifacts and bibliography data.
HTML generation has separate `*.docs_built` and
`*.docsHeader_built` completion files, with matching `.hash` and `.trace` files. For an identical
source snapshot, copy their HTML, static assets and `doc-manifest.json` too, or omit/quarantine
those exact HTML-marker families so doc-gen4 regenerates local outputs. Invalidate those HTML
markers when source content or the root-module set changes, even if old HTML exists, to ensure
a fresh rendering and index from the updated database. Preserve the module/core `*.doc` markers
and bibliography data; broad `*.doc*` invalidation discards the reusable module-data cache.
Completion markers alone supply neither database rows nor HTML/static files.

Use isolated writable caches for concurrent builds. Copied Lean traces can retain absolute source
paths from the former worktree. When changing source after relocation, check that affected module
traces refer to the current source path; stale foreign inputs can leave an incompatible compiled
module in use. With all writers stopped, quarantine those affected module traces and rebuild them
from the current source. Do not rewrite generated trace metadata. For a stack of related slices,
retaining one worktree path allows later validation runs to reuse completed artifacts without
concurrent writers.

A copied documentation database can also retain retired module rows. Its global name lookup can
then mix obsolete and current declaration documentation even when the generated module manifest
matches the current imports. Check affected declaration pages against their source, including
structure fields. Use a matching clean snapshot or regenerate the database with the pinned backend.
If using its module-deletion API to prune an isolated, backed-up copy, first prove each module is
absent from both source and registered files and that no retained module imports it. Verify database
integrity, foreign keys and unchanged retained rows before installing the consistent snapshot.
Before rerendering, quarantine each retired module's `declaration-data-{module}.bmp`,
`backrefs-{module}.json` and stale pages, along with the exact HTML completion markers. The backend
merges those per-module index and backreference files independently of its current import/database
closure. Preserve current module/core data. Overlay site assembly can retain removed pages, so
check its copy too. Do not patch rendered HTML or trace data.

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

### Retained archives with superseded wording

Retained `_out_*.txt` archives are kept byte-for-byte, because their SHA-256
fingerprints are pinned by the retention receipts in `docs/kb/audits/`. Some archive
prose has since been corrected in the producer and the receipt. Cite the receipt,
not the archive's own summary lines, for these (2026-10-28 audit, T48/T45):

- `scripts/probes/_out_g94_jacobi_cocycle_metric.txt`: the introduction calls
  `gamma2_norm` "the smallest chaining gauge value". It is the cost of the chosen
  greedy nets at the least legal rescaling, an upper bound on the infimum over
  admissible nets (`docs/kb/audits/g94-greedy-cost-correction-2026-09-06.md`).
- `scripts/probes/_out_326_overdet_incidence_max_stronger_decoupling.txt`: the final
  summary says the tight-chain margins grow "quadratically"; they grow cubically
  (`docs/kb/audits/probe-retention-incidence-archives-2026-09-06.md`).
- `scripts/probes/_out_324_dyadic_wall_floor_depth4.txt`: the header claims a
  "UNIVERSAL" floor and strict improvement over depth three at every `m ≥ 2`. The
  replay covers the finite range `m = 2..199`, and at `m = 2` both maxima equal `9`,
  so strict improvement starts at `m = 3`
  (`docs/kb/audits/probe-retention-dyadic-floors-2026-09-06.md`).
- `scripts/probes/_out_466r10_transfer_skeptic.txt`: section (B) treats the
  primitive-generator shift as the dyadic tower step and reads one mixed-moment
  equality as an independence test. Both readings are superseded
  (`docs/kb/audits/probe-retention-transfer-2026-09-06.md`).
- `scripts/probes/_out_w11_c3_kill_n16.txt`: the two stage verdicts and the summary
  header ("C=3 KILLED", "C=3 KILL SUMMARY") divide a certified spread lower bound by
  a searched monomial lower bound. That ratio is only a comparison with the searched
  baseline; no monomial upper bound is proved, so C=3 is unresolved at these cells.
  The producer now prints "spread exceeds 3x searched baseline; C=3 unresolved"
  (`docs/kb/audits/w11-search-verdict-correction-2026-09-06.md`; 2026-10-28 audit,
  T127).
- `scripts/probes/_out_g92_n32.txt` and `scripts/probes/_out_g92_n16.txt`: the
  "C=3 VIOLATED (in evidence)", "C=2 violated" and "[C=3 VERDICT]" lines are the same
  ratio of two search lower bounds. The n=32 C=3 claim is retracted in-tree:
  `Research/ProximityPrize/Frontier/_G101FMonomialBaselineGrowth.lean` certifies a
  monomial baseline of at least 8 at n=32, a=11, so the best ratio known there is
  23/8. In the n=16, k=2, q=65617, a=5 row the winning "spread" `x^0+1*x^4` is the
  `x^4` monomial class modulo the code (worstBad is invariant under codeword
  translation and scaling), so its count 48 shows the searched monomial baseline 37
  is incomplete. The producer `probe_g92_spread_excess_c3.py` now drops such
  translates from the spread class and reports search separations as "C unresolved"
  (2026-10-28 audit, T127).

Exit codes recorded in dated receipts describe those historical runs, not fresh
audit replays. A receipt whose recorded source hash differs from the current file
certifies only that historical source.
