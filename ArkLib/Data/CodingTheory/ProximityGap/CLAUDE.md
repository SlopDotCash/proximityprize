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
flat-Dudley chaining; G73 proves the Shkredov–Vyugin multi-shift bound remains strictly above
exponent `1/2` for every finite number of shifts. The 2026-07-10 evening arc localized further:
G77 closes the signed `relationAnomaly` route as a Fourier gauge and G78 proves the weighted
embedding qualifier has zero slack (commits `e78e41383`, `1c7b20205`); G81 seals the deep rungs
unconditionally — `DCEnergyBound` holds once `(2r-1)!! >= |G|^r` (commit `2ee6e69f7`) — so the
open rung window is finite in depth, but it still contains the prize depth `r ~ log p`. On the
line-list surface, S2 discharges the within-Johnson side of `PuncturedListBudget` (commit
`981b38e62`); the open band is exactly beyond-Johnson. The G82 audit (commit `203395261`) records
the one-hypothesis-deep CONDITIONAL production gate `mcaDeltaStar = 31/64` in
`Frontier/_PrizeShapeRateHalfBracket.lean` — a conditional reduction, not a closure.

The corrected maximal-cancellation decoder is now formal, and the production depth-three collision
sector is discharged; depth four is the first open decoder-side sector. Adaptive all-depth Wick
budgets are available, but G95 proves raw sector cardinalities cannot satisfy them: the live masses
must be normalized, signed/relation-weighted quantities. On the analytic side G89 proves the
first-incidence cross-orbit functional equals the wall with constant exactly one, while G90
refutes the unsigned sup-arc certificate shape at the required strength. G80V proves the averaged
dilation-coincidence identity, but its pointwise maximum remains the wall. The surviving CORE input
must therefore control a signed/correlated cross-arc or equivalent weighted single-embedding
functional; no such square-root-scale estimate is currently proved.

Issue #505 is CLOSED (2026-07-10 evening): G88's orbit-class Parseval makes the DC-centered
numerator an exact PSD sum over distinct orbit classes with zero cross terms, and with G89 the
first-incidence formulation is pinned to the wall in two independent coordinate systems. The
successor CORE issue is #509: bound the orbit-class mass profile `(S₀, (S_γ)_γ)`. Equivalent
current forms of the missing certificate: signed control of `K+1` prefix deviations of `b·μ_n`
(G97 reduction into the G80Z consumer) = near-uniform small-difference pair statistics of every
dilate (codex G80Q terminal form). Chaining is closed metric-universally (G94), the GM/HM Gram
bootstrap is count-fenced (G98), the Esseen ladder is non-contracting (G99 — which also lands
the first unconditional non-Fourier containment certificate: no dilate of `μ_n` fits in an
interval shorter than `√(p/2)`), the cyclic-code few-weight dictionary provably cannot apply at
prize shape (G95F), and the bounded spread-excess law is refuted in evidence at every constant
near the Johnson boundary (G92). Workbench §5 item (10) is the doctrine-v3 statement.

Start from:

- `docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` for the consolidated theorem and no-go map
  (its §6 addendum dated 2026-07-10 is the latest frontier snapshot);
- `DISPROOF_LOG.md` (tail first) for results after the dossier snapshot;
- `docs/kb/deltastar-466-tool-shape-doctrine-v2-2026-07-10.md` for the positive specification
  of any CORE closure (the single missing non-Fourier certificate);
- `Frontier/_G81DeepRungDCRecovery.lean`, `Frontier/_S2PuncturedJohnsonDischarge.lean`, and
  `Frontier/_PrizeShapeRateHalfBracket.lean` for the sharpest current pins;
- `Frontier/_DeltaStarDefinitive.lean` for the final threshold-facing reduction;
- `docs/wiki/deltastar-programme.md` and `docs/wiki/residual-census.md` for programme state.

GitHub control plane (fork `lalalune/ArkLib`): canonical tracker #466; live CORE issue #509
(orbit-class mass profile; #505 closed 2026-07-10); state/census maintenance #506; completion
audit #507; branch refactor #499; discussion #508;
project `https://github.com/users/lalalune/projects/1`.

Naming note (#506): both swarms minted G-numbers concurrently on 2026-07-10 — G89/G90/G91/G94/G95
each denote two unrelated results. FILE NAMES are the primary key; cite files, not bare G-numbers.
