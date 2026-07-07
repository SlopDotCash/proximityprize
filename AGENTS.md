# ArkLib Agent Guide

Lean 4 formalization of SNARK-related theory, interactive oracle reductions, and proof systems.
Start with [`README.md`](README.md) for project overview.

`AGENTS.md` is the canonical root guide. `CLAUDE.md` is a symlink to this file.

## Fast Start

1. For a convenient routine check, start with `./scripts/validate.sh`.
2. On a cold clone, run `./scripts/lake-locked.sh exe cache get` first.
3. If you add, rename, or delete files under `ArkLib/`, `git add` new paths before validation.
4. If you also want Lean style linting, run `./scripts/validate.sh --lint`.
5. For docstring or docs work, `./scripts/validate.sh --docs` is a convenient add-on check.
6. Only build site or blueprint output when touching `blueprint/` or `home_page/`:
   `./scripts/validate.sh --site`.

## Where To Work

- `ArkLib/Data/` - reusable math, coding theory, polynomials, and supporting definitions.
- `ArkLib/OracleReduction/` - core IOR abstractions and security theory.
- `ArkLib/ProofSystem/` - protocol formalizations built on the core.
- `ArkLib/Commitments/` - commitments and opening arguments.
- `ArkLib/ToMathlib/` - local extensions intended for upstreaming.
- `blueprint/src/` - deep design docs and bibliography.
- `scripts/` - repo utilities.

## Guardrails

- Never run bare `lake build` / `lake exe cache get` when other agents may be building on the
  same machine: use `./scripts/lake-locked.sh build <targets>` (and
  `./scripts/lake-locked.sh exe cache get`). It serializes builds per checkout, caps
  machine-wide build concurrency, and auto-repairs a missing mathlib olean cache before
  building. Unserialized concurrent builds corrupt `.lake` artifacts and silently fall back to
  compiling Mathlib from source. See
  [`docs/wiki/quickstart.md`](docs/wiki/quickstart.md).
- Lean defaults: `autoImplicit = false`; the long-file linter cap is `1500` unless a file opts
  out locally.
- `ArkLib.lean` is generated; do not hand-edit it.
- Edit source, not derived output such as `.lake/`, `blueprint/web/`, `blueprint/print/`,
  `dependency_graphs/`, or `home_page/docs/`.
- Pre-existing `sorry` blocks exist in active formalizations; distinguish existing gaps from new
  regressions.
- If a PR changes commands, repo structure, generated outputs, or the blueprint/citation
  workflow, update the matching page in [`docs/wiki/`](docs/wiki/README.md) in the same PR.
- Promote recurring agent learnings into [`docs/wiki/`](docs/wiki/README.md); do not let stable
  guidance live only in ephemeral notes.

## Active Challenge: Proximity Gap Grand Challenge (#334)

If you are working on the Proximity Prize / proximity-gap formalization (issue #334, successor
to #232), read the dedicated agent guide **before** touching that cone — it has the build recipe
you need to avoid clogging the machine:

- [`ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md`](ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md)
  (auto-loaded in that directory; `AGENTS.md` there is a copy): build/concurrency/honesty rules,
  the #334 ledger, substrate API map, references, and pitfall catalogue.
- **Fast iteration (mandatory):** that cone is ~3,500 files (3,483 `.lean` as of 2026-07-01);
  `lake build` traces a 3000+-job graph
  (~2-3 min even no-op) and takes the build lock (serializes all agents). Instead run
  `scripts/pg-warm.sh` ONCE (pre-builds the substrate oleans), then iterate per-attempt with
  `scripts/pg-iterate.sh <file>` (= `lake env lean`, ~30-75s, **no lock → fully parallel**).
- **Start here:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/README.md` for lane-file
  status (as of 2026-07-01: `A5` equivariance pin LANDED; `B3` Thorner-Zaman concrete ladder
  LANDED through n=32768 with the asymptotic form still a named hypothesis; `B2`
  curve-decodability OPEN), then the ranked live frontier in
  `docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` §6 and `PROXIMITY_PRIZE_WORKBENCH.lean` §5.
- **Open-residual map (whole project):**
  [`docs/wiki/residual-census.md`](docs/wiki/residual-census.md) — 100 strict residuals:
  55 open / 44 discharged / 1 refuted (regenerated 2026-07-01); the "named residual"
  convention is modularity, not incompleteness.

## Deeper Docs

- [`docs/wiki/README.md`](docs/wiki/README.md) - hub and maintenance rules.
- [`docs/skills/README.md`](docs/skills/README.md) - reusable cross-cutting workflows.
- [`docs/wiki/quickstart.md`](docs/wiki/quickstart.md) - commands and validation.
- [`docs/wiki/repo-map.md`](docs/wiki/repo-map.md) - structure and module routing.
- [`docs/wiki/generated-files.md`](docs/wiki/generated-files.md) - source-of-truth rules for
  derived outputs.
- [`docs/wiki/blueprint-and-citations.md`](docs/wiki/blueprint-and-citations.md) - blueprint,
  references, and citations.

## Canonical Project Docs

- [`README.md`](README.md) - project overview.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) - style, naming, docstrings, citations, and large
  contributions.
- [`ROADMAP.md`](ROADMAP.md) - planned directions.
- [`BACKGROUND.md`](BACKGROUND.md) - background references.
