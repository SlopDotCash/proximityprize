# ArkLib Scripts 

This directory contains various utility scripts for the ArkLib project.

## Available Scripts

### Build and Validation
- **`validate.sh`** - Recommended convenience wrapper for routine local validation
- **`lake-locked.sh`** - Serialized `lake` wrapper for multi-agent checkouts: per-checkout
  exclusive lock + machine-wide build slots + mathlib olean-cache auto-repair. Use it instead of
  bare `lake build` whenever other agents may be building on the same machine
  (`./scripts/lake-locked.sh build <targets>`)
- **`build-project.sh`** - Compile-only helper (`lake build` via `lake-locked.sh`)
- **`build_timing_report.sh`** - CI timing/report helper for clean builds, warm rebuilds, and the validation wrapper
- **`update-lib.sh`** - Update ArkLib.lean with the standalone Proximity Prize import surface
- **`check-imports.sh`** - Check if ArkLib.lean matches that import surface
- **`check-warning-log.py`** - Fail on scoped warning classes found in a captured build log
- **`check-docs-integrity.py`** - Check docs links and the `CLAUDE.md` symlink
- **`proximity_prize_cleanroom_audit.py`** - Optional post-build clean-room audit for
  proximity-prize final declarations: checks blessed axioms and rejects residual or
  goal-equivalent `Prop` assumptions in active manifest targets
- **`lint-style.py`** - Python-based style linting with a maintained per-file exception baseline
- **`update-style-exceptions.sh`** - Regenerate the Proximity Prize style exception baseline
- **`lint-style.lean`** - Lean-based style linting

### Dependency Analysis
- **`dependency_analysis/`** - Complete dependency analysis toolkit
  - Generate dependency graphs for all ArkLib modules
  - Interactive exploration of dependencies
  - Visual representations (PNG, SVG)
  - See `dependency_analysis/README.md` for detailed usage

### Knowledge Base
- **`kb/`** - Scripts for syncing and inspecting the repository knowledge base
  - Export bibliography metadata
  - Extract citation usage from `ArkLib/**/*.lean`
  - Scaffold paper pages and lint KB structure
  - Resolve review context from cited keys or changed Lean files
  - See `kb/README.md` for usage

## Quick Start

### Recommended Routine Validation
```bash
./scripts/validate.sh
```

### Validation With Optional Checks
```bash
# Add Lean style linting
./scripts/validate.sh --lint

# Build API docs too
./scripts/validate.sh --docs

# Build site / blueprint output too
./scripts/validate.sh --site
```

### Generate Dependency Graphs
```bash
cd scripts/dependency_analysis
python generate_dependency_graph.py --root ../../ --output-dir ../../dependency_graphs
```

### Compile Only
```bash
./scripts/build-project.sh
```

### Build Timing Helper
```bash
bash scripts/build_timing_report.sh --help
```

### Proximity Prize Clean-Room Audit
```bash
# Requires the relevant modules to be built, like scripts/axiom_audit.py.
python3 scripts/proximity_prize_cleanroom_audit.py

# Manifest-only smoke check.
python3 scripts/proximity_prize_cleanroom_audit.py --dry-run
```

### Update Library Imports
```bash
# Update ArkLib.lean with the standalone Proximity Prize imports
./scripts/update-lib.sh

# Check if imports are up to date
./scripts/check-imports.sh

# Refresh the scoped style baseline after intentionally accepting legacy findings
./scripts/update-style-exceptions.sh
```

### Check Docs Integrity
```bash
python3 ./scripts/check-docs-integrity.py
```

### Knowledge Base Indexes
```bash
python3 ./scripts/kb/sync_from_bib.py
python3 ./scripts/kb/extract_lean_citations.py
python3 ./scripts/kb/check_generated.py
python3 ./scripts/kb/lint.py
python3 ./scripts/kb/review_context.py --files ArkLib/ProofSystem/Fri/Spec/SingleRound.lean
```

### `build_timing_report.sh`

Helper used by CI to measure and render build timings for clean builds, warm
rebuilds, and the `./scripts/validate.sh` path. The CI workflow uploads
timing-data artifacts so PR runs can compare against a previously recorded
baseline without rerunning that baseline in the same job. This supports
[`../.github/workflows/ci.yml`](../.github/workflows/ci.yml).

## Requirements

- Python 3.6+ (for Python scripts)
- Lean 4 (for Lean scripts)
- Graphviz (for dependency visualization)
- Virtual environment (`.venv`) for Python dependencies

## Notes

- Most scripts should be run from the ArkLib root directory
- Python scripts require the virtual environment to be activated
- Some scripts may require specific Lean toolchain versions
- `validate.sh` is the recommended local wrapper; use the lower-level scripts directly when you
  want to run or debug one piece in isolation
- `validate.sh` mirrors the CI policy gates: forbidden-token precheck, full build, zero live proof
  holes, flagship axiom audit, umbrella imports, docs integrity, and generated-KB checks. The
  research corpus has a large legacy compiler-warning backlog; use `--lint` for the maintained
  style baseline and `check-warning-log.py` for targeted warning-cleanup work.
- In this standalone repository, `lint-style.sh` targets the Proximity Prize cone; unrelated
  ArkLib sources are retained as substrate/history but are outside the maintained default target.
- New `ArkLib/**/*.lean` files must be staged before `update-lib.sh` or `check-imports.sh`
