# ProximityGap / δ* campaign — agent guide

This checkout is on the long-lived `research/proximity-prize` branch. It contains both the library
formalization of the proximity-gap literature and the machine-checked δ* research campaign. The
branch was split from `main` on 2026-07-09 (issue #499); never merge it into `main`. Sync library
changes from `main` only with the corpus-preserving procedure in `RESEARCH_BRANCH.md`.

On `main`, this directory must remain upstream-shaped: paper-keyed developments plus the
protocol-facing API. Campaign work such as `Frontier/`, `DISPROOF_LOG.md`, the workbench, dossier,
and KB notes belongs only on `research/proximity-prize`.

## Mandatory fast iteration

The cone contains more than 800 files and a full build traces over 3,000 jobs. Do not use bare
`lake build`, and do not take the shared build lock for ordinary proof iteration.

1. Run `scripts/pg-warm.sh` once per cold session.
2. Iterate with `scripts/pg-iterate.sh <path/to/file.lean>`.
3. Use `./scripts/lake-locked.sh build <module>` only when an olean/module build is required.
4. Run `./scripts/validate.sh` for the repository gate; add `--lint` or `--docs` when relevant.

When several agents share the checkout, develop in a detached `/tmp` worktree whose `.lake` points
to this checkout. Never run concurrent unserialized Lake builds: they can corrupt `.lake` artifacts.

## Honesty contract

- A mathematical advance is an axiom-clean Lean theorem or a reproducible probe.
- Target theorem axioms are limited to `propext`, `Classical.choice`, and `Quot.sound` unless a
  declaration explicitly formalizes a cited external theorem as an assumption.
- No new `sorry`, `sorryAx`, `axiom` laundering, asserted named residual, or conditional theorem may
  be reported as closure.
- Put refuted approaches and their reusable obstruction lemmas in `DISPROOF_LOG.md`.
- Distinguish an exact production pin from toy-instance pins, brackets, reductions, and no-go maps.

## Current verified frontier (2026-07-10)

The production δ* conjecture is **open**. Exact finite-instance and deep-rung pins, the threshold
ledger, many equivalent reductions, and a large axiom-clean no-go map are in-tree. They do not prove
the production statement.

The binding analytic target is square-root-scale cancellation for the adversarial smooth
multiplicative subgroup, equivalently the deep DC-subtracted energy / Paley-BGK face. G70 rules out
flat-Dudley chaining as an improvement; G73 proves the Shkredov–Vyugin multi-shift bound remains
strictly above exponent `1/2` for every finite number of shifts. After G73, the signed cross-cell
`relationAnomaly`/transversality route is the sole recorded off-BGK route not yet closed. Otherwise
the core remains ON-BGK.

Start from:

- `docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` for the consolidated theorem and no-go map;
- `DISPROOF_LOG.md` (tail first) for results after the dossier snapshot;
- `Frontier/_R366CenteredRelationAnomaly.lean` and
  `Frontier/_R367SignedShadowPairDiscrepancy.lean` for the live signed route;
- `Frontier/_DeltaStarDefinitive.lean` for the final threshold-facing reduction;
- `docs/wiki/deltastar-programme.md` and `docs/wiki/residual-census.md` for programme state.

GitHub control plane (fork `lalalune/ArkLib`): canonical tracker #466; live signed route #505;
state/census maintenance #506; completion audit #507; branch refactor #499; discussion #508;
project `https://github.com/users/lalalune/projects/1`.
