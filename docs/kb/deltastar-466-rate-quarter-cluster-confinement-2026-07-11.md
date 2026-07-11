# δ* #466 — Cluster confinement: compounded rank-drop floors (X₄, X₅), dyadic blocking at every confined size, the five-pencil master budget, and the FINAL residual form `StallResidual ⟸ SwarmResidual` (2026-07-11)

**Lane:** P1 rate-quarter — eighth round of the 2026-07-11 arc, following the
pair-cloud second moment (clusters confined to sizes 3–5).
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterClusterConfinement.lean`
(pg-iterate OK 10s; 11 theorems; full axiom lists read manually via `lake env lean`:
9 exactly `[propext, Classical.choice, Quot.sound]`, 2 `[propext]`; no sorryAx, no
warnings).  Constants Python-verified exactly before formalization.

## (1) Compounded rank-drop floors (kernel)

An `m`-cluster of near-full pencils has an `(m−1)`-dimensional telescoping
difference lattice: per-row parameter budget `(m−1)k` vs overlap demand
`Σ|ov| ≥ m(T−5) − N`.  Generic deficits (`cluster_rank_drop_floors`):

| m | X_m = m(T−5) − N − (m−1)k |
|---|---|
| 3 | 167 772 147 |
| 4 | 492 131 652 |
| 5 | 816 491 157 |

growth `(T−5) − k = 324359505` per pencil — the escape rank-drop requirement
COMPOUNDS (round 5's single-identity drop was `1.67·10⁸`; a 5-cluster must defeat
`8.16·10⁸` independent evaluation constraints).  Structural support:
`bonferroni_double` (general m-set Bonferroni, proved by Finset induction) +
`cluster_overlap_mass` (the coincidence mass any cluster must realize).

## (2) Dyadic blocking at every confined size (kernel)

The binomial-constructor window at cluster size `m` is
`[⌈(m(T−5) − N)/C(m,2)⌉, k−1]`: `[234881020, …]`, `[216239670, …]`,
`[189023299, 268435455]` for `m = 3, 4, 5` — ALL inside the dyadic gap
`(2²⁷, 2²⁸)`, which contains no power of two (`dyadic_gap`,
`cluster_windows_dyadic_free`).  On `μ_{2^30}` every known constructor class is
blocked at every confined cluster size — more pairs give more slack (the window
LEFT edge falls as `1/C(m,2)`) but never enough to reach `2²⁷`.

## (3) The five-pencil master budget and the final residual form (kernel)

* `six_sets_impossible_param` — the second-moment six-set impossibility,
  PARAMETRIC in the size threshold θ (generalizing round 7); instantiated at
  `θ = T − 12`: `sixPencil_margin13_forced` — among any six pairwise-distinct
  pencils, one has margin ≥ 13.
* `margined_riders_le_of_thirteen` — margin-13 harvest `≤ 36995913`.
* `stall_budget_of_five_pencil_cover` — two arbitrary + three margin-13 pencils:
  `#bad ≤ 2·480946859 + 3·36995913 = 1072881457 ≤ N` (slack `860367`;
  `master_ledger`).
* **`stallResidual_of_swarmResidual`** — THE FINAL FORM:
  `SwarmResidual dom → StallResidual dom`, where `SwarmResidual` (named Prop) is
  the budget restricted to families admitting NO margined five-pencil cover
  (`FiveCoverForm`).  Every five-pencil-coverable family is discharged
  unconditionally.

## Residual map — the P1 counting branch after eight rounds

`StallResidual(μ_{2^30}) ⟸ SwarmResidual(μ_{2^30})`, whose open content is:

1. **3-to-5 near-full clusters** that cannot be complemented into a
   `FiveCoverForm` — these require Bezout rank drops `≥ X_m` (compounding), with
   every known constructor dyadically blocked.
2. **The sub-Johnson swarm** — families whose pairs spread over ≥ 6 pencils none
   of which can serve as the two capacity slots — counting-immune per round 7's
   no-go rungs; needs beyond-Johnson list input (the campaign's global wall).

Everything else — 1/2-pencil scalar covers, ≤ 4-pencil pair covers, 3–5-pencil
scalar covers with margins, five-pencil margined covers — is now
kernel-discharged.

## Honesty

`StallResidual(μ_{2^30})` remains OPEN — this round reduces it exactly to
`SwarmResidual` and pins the cluster escape floors; the swarm itself is
untouched (and provably untouchable by the counting jaws).  No δ* movement;
bracket `3/8 ≤ δ* ≤ 43/96 + 1/(3·2^30)` untouched.

## Arc status (eight rounds, 2026-07-11)

census → harvest cap → dimension deficit → Stepanov weld (adversarial-domain
REFUTATION) → dyadic restoration → pencil-cover theorem → pair-cloud second
moment → **cluster confinement (final residual form)**.  Eight new files,
**68 kernel theorems, all axiom-clean**, six exact probes, one refutation, two
no-go theorems, and the P1 counting branch reduced to a single named Prop
(`SwarmResidual`) whose content is the campaign's known global wall.
