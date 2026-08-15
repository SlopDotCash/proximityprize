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

## The rate-1/2 strip route (SYZ arc) — assembly, fixed point, and small-field discipline

Parallel to the CORE Paley/BGK line above, the SYZ18–SYZ53 arc pursues δ*=1/3 through the rate-1/2
proximity strip. As of SYZ54 (2026-07-11) it is **assembled** but **not closed**; production δ*
remains OPEN / ON-BGK. What a next agent must know:

- **The assembly.** `Frontier/_SYZ40FinalAssembly.lean` expresses the whole strip theorem as one
  theorem on `StripMasterHypothesis`; `Frontier/_SYZ46CensusBridge.lean` wires the count bound to the
  δ*-floor and states the **conditional bracket** `deltaStar_bracket_of_strip_master_hypothesis`
  (`357913941/2³⁰ ≤ δ* ≤ 358612991/2³⁰`, ceiling unconditional, floor conditional). The merged branch
  (`m ≤ 3`) is unconditional; the spread branch (`m ≥ 4`) consumes the hypotheses.
- **The two-field fixed point (SYZ42/43).** The strip conclusion reduces to exactly two open fields:
  `uniformSylvester` (SYZ38/39 generalized-Sylvester injectivity = BGK-type resultant non-vanishing at
  `n=2³⁰`; the sole substantive input) and `realizabilityCore` (SYZ42, auto-instantiated by any
  over-budget `mcaEvent` stack via the G87 syndrome bridge, leaving only the union-rank bound
  `hrank`). The census bracket's full honest wire list is (i)–(iv) in the SYZ46 note. Do NOT report the
  bracket or `31/64`-neighbourhood as a pin — no equality is claimed.
- **The BGK unification (SYZ49).** The balanced-interior obstruction = max level set of
  `R = W_BC/W_AC` on `μ_n` = the BGK additive-log-phase coincidence bound. The strip's non-BGK
  residual and the CORE character-sum wall are the **same object**; the strip cannot be closed
  BGK-free. SYZ44 + the swarm SYZ53 half-gap identity `ι = ⌊(δ₂−δ₁)/2⌋` reduce the non-BGK obligation
  to the crisp Hilbert–Burch gap `δ₂−δ₁ ≤ 1` on the balanced interior — the object to target.
- **Small-field discipline (G84 / SYZ53 — MANDATORY).** SYZ52 measured an over-budget `mca`-bad count
  (`19 > n−1`) on band-realizable `ι=2` interior witnesses over `𝔽₂₉` that read as a δ*=1/3
  refutation candidate; SYZ53's exact per-prime `p`-sweep showed it **collapses** to the generic
  floor by `p* ∈ (197,1009)` and stays flat through `2³¹` — a small-characteristic artifact, δ*=1/3
  survives. **NEVER trust a small-p verdict, in either direction** (over-budget or in-budget): always
  run the p-sweep to `p ≫ p*` (`probe_syz53_p_scaling.py` exact-count tool). A small-field count is a
  saturation-regime analogue artifact, not evidence about production.

Start from:

- `docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` for the consolidated theorem and no-go map
  (its §6 addendum dated 2026-07-11 (SYZ54) is the latest frontier snapshot; the 2026-07-10 addendum
  precedes it);
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
