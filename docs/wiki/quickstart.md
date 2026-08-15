# Quickstart

This page is the recommended agent playbook for commands and validation.
Use it as the main guide for routine local checks.

## Recommended Validation

For a convenient routine check, run:

```bash
./scripts/validate.sh
```

On a cold clone, fetch precompiled dependencies first:

```bash
./scripts/lake-locked.sh exe cache get
./scripts/validate.sh
```

## Concurrent Agent Builds (`lake-locked.sh`)

When several agents share a machine (even in different checkouts/worktrees), never run bare
`lake build` or `lake exe cache get`. Use the serialized wrapper, a drop-in replacement for
`lake`:

```bash
./scripts/lake-locked.sh build ArkLib.Some.Target
./scripts/lake-locked.sh exe cache get
```

This applies to helper scripts too: `scripts/pg-warm.sh` originally called bare `lake build`
and bypassed the lock (observed 2026-07-10: two warm builds plus a locked build ran three
simultaneous lake drivers compiling the same files); it now routes through `lake-locked.sh`.
If you write a script that builds, call the wrapper, never bare `lake`.

What it does (observed failure mode 2026-06-11: 7 concurrent lake builds plus a racing
`cache get` in shared checkouts produced 60+ lean workers on 12 cores, corrupted oleans, and
four builds silently recompiling all of Mathlib from source):

- **Per-checkout exclusive lock** (`.lake/agent-build.lock`): at most one lake invocation per
  checkout. A second invocation waits and then gets a warm incremental build instead of a
  corrupting race. Lake has no built-in lock and no `--jobs` cap in the pinned version.
- **Machine-wide build slots** (`~/.cache/lake-build-slots`, default 2, override with
  `LAKE_LOCKED_SLOTS`): caps total concurrent builds across all checkouts so each gets real
  cores instead of thrashing.
- **Mathlib cache guard**: if `.lake/packages/mathlib` is present but its root olean is
  missing, it runs `lake exe cache get` first (inside the lock). A build must never fall back
  to compiling Mathlib from source — that is hours of CPU and the main melt-down mode.
- **Stale-lock stealing**: locks carry a heartbeat refreshed every 30s; a lock whose heartbeat
  is older than `LAKE_LOCKED_STALE_SECS` (default 300) is presumed killed and stolen, so a
  `taskkill`ed build never wedges the queue.

`./scripts/validate.sh` and `./scripts/build-project.sh` already route their builds through the
wrapper. `LAKE_LOCKED_DISABLE=1` bypasses it (single-tenant machines, CI debugging).

Build hygiene on shared machines:

- One `lake exe cache get` to **completion** before the first build in a fresh checkout; never
  run it concurrently with builds in the same checkout (the wrapper enforces this).
- A build process tree (lake + lean workers) that has been running for far longer than the
  target warrants — for example a small-target build past 20–30 minutes that is grinding
  through `Mathlib/` files — usually indicates a clobbered cache, not a slow build. Kill the
  build tree (never agent processes), restore the cache, retry through the wrapper.

Do not use bare `lake update` as a routine cache-repair command. It re-resolves
`lake-manifest.json` and may delete/re-clone package directories while other checks are running.
Use `lake exe cache get` after syncing instead. Run `lake update` only when intentionally changing
dependency pins, and commit the resulting manifest together with the matching `lean-toolchain`.

### Recovering a corrupted or re-cloning `mathlib` package

Symptoms (tree-wide build failures, OOM, or stalls that are not your change):

- `.lake/packages/mathlib` is large on disk but has no checked-out source
  (e.g. `Mathlib/Algebra/Field/Basic.lean` is missing) or `git -C .lake/packages/mathlib rev-parse HEAD` fails.
- Many concurrent `git-remote-https ... mathlib4` clone processes are racing into that one
  directory, so it never converges and every session's build fails on missing `mathlib` oleans.

Root cause: a per-session package fetch checked out mathlib's default branch instead of the
manifest-pinned revision, and parallel sessions racing the same directory prevent convergence.

Non-destructive recovery (one actor at a time; do **not** `rm -rf` the shared package — the pinned
revision is usually already fetched inside it):

```bash
# 1. Pause (do not kill) the racing clones so the directory stops being overwritten.
pkill -STOP -f 'git-remote-https.*mathlib4'

# 2. Check out the revision pinned in lake-manifest.json (NOT the default branch).
#    Find the pin with: python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])"
git -C .lake/packages/mathlib checkout -f <manifest-pinned-rev>

# 3. Decompress the matching precompiled oleans for that revision.
lake exe cache get

# 4. Verify a real build completes.
lake build ArkLib.Data.CodingTheory.ProximityGap.Collapse
```

Prevention: never run `lake update` for cache repair (see above); let a single coordinator do
package recovery; the only source of truth for the mathlib revision is the `mathlib` entry in
`lake-manifest.json`.

## Validation By Change Type

### Existing Lean files only

```bash
./scripts/validate.sh
```

### Added, renamed, or deleted files under `ArkLib/`

```bash
git add path/to/newfile.lean
./scripts/validate.sh
```

`./scripts/update-lib.sh` only considers tracked files, and now fails fast if untracked
`ArkLib/**/*.lean` files are present.

### Lean-heavy refactors or cleanup

```bash
./scripts/validate.sh --lint
```

This adds `./scripts/lint-style.sh` to the convenience wrapper. The main CI build currently runs
with lint disabled, so treat this as opt-in for now.
If the task is specifically Lean warning cleanup, follow
[`../skills/fix-lean-warnings.md`](../skills/fix-lean-warnings.md).

### Docstrings, blueprint, or website changes

```bash
./scripts/validate.sh --docs
```

For website or blueprint output, run:

```bash
./scripts/validate.sh --site
```

`./scripts/build-web.sh` is still what assembles the site, and it skips blueprint generation if
`leanblueprint` is not installed. If blueprint output matters, install it first:

```bash
python3 -m pip install leanblueprint
```

## Stale-Olean Kernel Errors (`unknown constant Semiring.toMonoid` etc.)

Symptom: `lake env lean <file>` (or `pg-iterate.sh`) fails with a KERNEL error
`(kernel) unknown constant 'Semiring.toMonoid'` (or another long-renamed instance path),
usually pointing at a line that merely *applies* an imported theorem. Cause: a `.olean` in the
import cone was compiled against a different toolchain/Mathlib revision (toolchain drift in the
shared checkout); the elaborator inlines a constant name that no longer exists.

Fix (verified 2026-07-09, three occurrences in one session):

```bash
./scripts/lake-locked.sh build <TheStaleModule>   # rebuild JUST the suspect module
```

Isolation recipe: binary-search the import cone with tiny `/tmp` test files that `#check` and
then *apply* the suspect theorems — `#check` alone does not force the failure; an application
in a real `theorem` does. Suspect first any module whose `.olean` mtime predates the last
toolchain bump (`ls -la .lake/build/lib/lean/.../*.olean`). Both ArkLib and Mathlib modules
can be affected (`Mathlib.LinearAlgebra.Matrix.AbsoluteValue` was one instance).

## Important Notes

- `./scripts/validate.sh` is the recommended convenience wrapper for routine local validation.
- By default it runs the forbidden-token precheck, `lake build`, the zero-hole sorry census, the
  flagship axiom audit, umbrella-import checks, docs integrity checks, and knowledge-base checks,
  so a clean local `validate.sh` matches the CI gate set (issue #111 parity). Compiler warnings in
  the inherited research corpus remain visible but are not a zero-budget gate; `--lint` enforces
  the maintained style-exception baseline, and `check-warning-log.py` supports targeted cleanup.
- The lower-level scripts remain valid when you only want one specific check.
- `scripts/build-project.sh` is now just a compile-only helper, not the convenience wrapper.
- `scripts/README.md` is still useful as an inventory of helper scripts.
- Only run docs and site builds when those surfaces are relevant; they are slower and more
  tool-dependent than normal Lean builds.

## Optional Direct Commands

You can still run the underlying pieces directly when debugging a specific issue:

```bash
lake build
python3 ./scripts/forbidden_tokens.py
python3 ./scripts/sorry_census.py --fail-on-holes
python3 ./scripts/axiom_audit.py
./scripts/check-imports.sh
python3 ./scripts/check-docs-integrity.py
python3 ./scripts/kb/check_generated.py
python3 ./scripts/kb/lint.py --strict-cited-pages
```

If you specifically need to regenerate `ArkLib.lean`, use:

```bash
./scripts/update-lib.sh
```

If blueprint output matters and `leanblueprint` is missing:

```bash
python3 -m pip install leanblueprint
```

## CI Mapping

- [`../../.github/workflows/ci.yml`](../../.github/workflows/ci.yml)
  compiles every module imported by generated `ArkLib.lean` in sixteen cumulative topological stages.
  Each stage restores the preceding stage's ArkLib oleans, compiles the next contiguous portion of
  the import DAG, and uploads the cumulative result. This preserves full-project coverage without
  relying on one hosted runner surviving a multi-hour cold build. The final artifact is also the
  input to the Pages documentation workflow.
  A parallel policy job enforces the issue #47 verification gates: a fast precheck rejecting
  `native_decide`/`bv_decide`/custom `axiom` declarations in live source
  (`scripts/forbidden_tokens.py`), a comment-stripped sorry census requiring
  zero live holes (`scripts/sorry_census.py --fail-on-holes`), and a
  `#print axioms` sweep over the pinned flagship list
  (`scripts/axiom_audit.py` reading `scripts/flagship_axioms.txt`) that must
  stay within `propext`, `Classical.choice`, `Quot.sound`. Renaming or
  deleting a pinned flagship theorem without updating the list is a hard CI
  failure. As of issue #111 these same three gates also run from
  `./scripts/validate.sh`, so local validation matches CI.
- The forbidden-token precheck rejects every custom `axiom` *except* the
  documented, tracked residuals listed in
  [`../../scripts/residual_axioms.txt`](../../scripts/residual_axioms.txt) (route (a)
  of #111). Each allowlist entry names one residual axiom and the issue that owns its
  eventual discharge; an undocumented or newly added `axiom` still fails the gate, and a
  stale allowlist entry (matching no live axiom) prints a warning to prompt cleanup.
  `scripts/forbidden_tokens.py` also accepts explicit Lean files or directories for
  focused checks; stale allowlist warnings are only meaningful on the default full-tree scan.
- [`../../.github/workflows/check-imports.yml`](../../.github/workflows/check-imports.yml)
  checks that `ArkLib.lean` matches the tracked source tree.
- [`../../.github/workflows/docs-integrity.yml`](../../.github/workflows/docs-integrity.yml)
  checks local markdown links and the `CLAUDE.md` symlink.

## Manual Timing Helper

If you need to reproduce the timing workflow locally, the same helper script can
capture a measurement and render a report:

```bash
bash scripts/build_timing_report.sh run clean_build /tmp/build-timing.jsonl -- \
  bash -eo pipefail -c 'rm -rf .lake/build && lake build'
bash scripts/build_timing_report.sh render /tmp/build-timing.jsonl
```

## Swarm Verification Discipline

Hard-won rules for multi-agent sessions where several agents land commits on
`main` concurrently (distilled from the 2026-06-10 #232 frontier sessions):

- **An announced brick is not a brick.** Commit messages and `DISPROOF_LOG.md`
  entries can name theorems that never landed (found once: a theorem announced
  in a commit message existed nowhere in history). Before citing or building on
  a named lemma, `grep` the tree — not the log — and prefer
  `git log -S <name>` to confirm a Lean occurrence.
- **`#print axioms` lines are expected output.** Several modules end with
  `#print axioms <thm>` audit lines by convention. A zero-output compile gate
  must treat those lines as a pass signal (each should read exactly
  `[propext, Classical.choice, Quot.sound]`); anything else in the output —
  warnings, errors, `sorry` notices — is a failure.
- **Main-branch CI runs supersede in queue.** With
  `cancel-in-progress: ${{ github.ref != 'refs/heads/main' }}`, queued main
  runs are replaced by newer pushes; individual-push runs showing `cancelled`
  is normal. The head run validates the whole tree, so "CI green on every
  push" means: the most recent *completed* main run is green and contains your
  commits (`git merge-base --is-ancestor <sha> <ci-sha>`).
- **Joint-import check before declaring a batch done.** Single-file
  `lake env lean` passes do not rule out cross-module name clashes. After
  landing several new modules, build exactly those targets
  (`lake build <Module1> <Module2> …`) and compile a scratch file importing
  all of them together.
- **Rebase before every push; new files only.** Concurrent agents editing
  shared files (especially `ArkLib.lean`, `DISPROOF_LOG.md`) is the main
  collision source. One designated writer appends to shared logs; everyone
  else ships new modules and lets `./scripts/update-lib.sh` regenerate the
  import index at commit time.
- **After landing, confirm your commit survived: `git branch -r --contains
  <sha>`.** Concurrent lanes rewrite history; locally-green commits get
  dropped while the file content survives untracked on disk. Recovery is
  cheap — `git add` + re-commit the surviving file (byte-identical to the
  orphan blob), then push via a detached worktree if the main tree has other
  lanes' unstaged edits: `git worktree add /tmp/wt FETCH_HEAD && cd /tmp/wt &&
  git cherry-pick <sha> && git push fork HEAD:main`.
- **Agent deaths leave complete orphan files — check before re-proving.** A
  prover that hits its session limit after writing but before verifying
  leaves a finished (often fully correct) file at its target path. Before
  relaunching the brick, `git status --short` the target directory, compile
  the orphan, and fix at most the 1–2 mechanical tactic errors (recurring
  shapes: `Set.injOn_id` unification → introduce the `InjOn` proof as a
  `have`; `WithBot` casts → `WithBot.coe_le_coe.mpr`; `smul_eq_mul`
  commutation → `simp [smul_eq_mul]` then `ring`, since `simp [mul_comm]`
  loops).
- **A surprise `sorryAx` in `#print axioms` for a sorry-free file means stale
  imports, not a tainted proof.** Rebuild the import closure
  (`lake build <each imported module>`) and re-check before debugging the
  proof. Confirmed twice on 2026-06-10/11.
