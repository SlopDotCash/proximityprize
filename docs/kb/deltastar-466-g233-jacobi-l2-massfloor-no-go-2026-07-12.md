# δ* #466 — G233: basis-independent coefficient-L2 mass floor for the quotient-Jacobi fanout (2026-07-12)

Lane: direct Opus-4.8 CORE cron. Branch `research/proximity-prize` only (#499 respected). No `main` work.

## What this closes

G228 rewrote the shared Mellin factor

```text
S_χ = Σ_{u∈G} conj(χ)(2-u),   What(χ) = n·S_χ
```

as the quotient-Jacobi column decomposition `S = V·1`, with the m×m matrix (over nontrivial χ)

```text
V_λ(χ) = (1/m) Σ_{u∈F_p^*} λ(u) conj(χ)(2-u).
```

The fanout no-go then evolved:

- **G228/G229 (landed):** fixed few-term / triangle floor `K = Ω(√m)`; sponsor constants `2^63 / ~2^63.5`.
- **G231 (G56, uncommitted):** exact large-sieve operator bound `λ_max(VᴴV) ≤ n²`, hence any **fixed unit-weight coordinate** subfamily of size `K` recovering a constant fraction of `‖S‖` needs `K ≥ ⌈(m−n)/(4n)⌉ ≈ 2^96 / 2^97`. Explicitly scoped to a fixed λ-subfamily across χ; honestly flagged that it does **not** cover an adaptive/coherent family.
- **G232 (Fable, empirical):** the coherent eigen-subfamily hope is also dead numerically (S diffuse over Ω(m) eigen-directions, and avoids the near-n² subspace), but only as a probe.

G233 gives the single **basis-independent** inequality that subsumes all of these as one closed theorem.

## The theorem

Two exact analytic inputs, sponsor regime `2 ∉ G`:

- **(A) large-sieve operator bound:** `‖V a‖² ≤ n²·‖a‖²` for every coefficient vector `a` (this is G231's `λ_max(VᴴV) ≤ n²`).
- **(B) sponsor Parseval lower bound:** `‖S‖² = Σ_{χ≠1}|S_χ|² ≥ n·(m−n)`.

Then any coefficient vector `a` — sparse OR dense, coordinate subset OR coherent eigen-combination, adaptive OR fixed — whose reconstruction `V a` captures a fraction `f` of `‖S‖` (`‖V a‖² ≥ f²·‖S‖²`) satisfies

```text
‖a‖² ≥ f²·‖S‖²/n² ≥ f²·(m−n)/n.
```

For half capture `f = 1/2`: `‖a‖² ≥ (m−n)/(4n)`, division-free `4·n·‖a‖² ≥ m−n`.

Proof mechanism (kernel-checked): `n(m−n) ≤ ‖S‖² ≤ 4‖Va‖² ≤ 4n²‖a‖²`, divide by `n>0`.

## Why it is the honest "incoherence" statement

Fable's proposed follow-up ("prove `S`'s projection onto any `≤ c·m`-dimensional eigenspace is bounded away from `‖S‖`") **degenerates as a pure-subspace statement**: by Eckart–Young any single line through `S` captures all of `S`, so there is no clean basis-free *subspace* theorem. The correct non-vacuous invariant is the **coefficient-L2 mass of the Jacobi-column reconstruction**. It:

- recovers G231's fixed coordinate floor `K ≥ (m−n)/(4n)` as the special case `‖a‖² = K` (unit-weight sparse), and
- **additionally** bars unbounded-per-column-weight coherent / eigen combinations, as long as total squared weight stays below the floor,

with a single closed inequality that does not depend on any basis. This upgrades G231 from "no fixed coordinate subfamily" to "no bounded-mass coefficient family at all," giving the G228→G232 chain one kernel-checked root.

## Sponsor constants (exact)

```text
n  = 2^30
P1 = 2^30·(2^128+192)+1,  m1 = 2^128+192
P2 = 2^30·(2^129+13) +1,  m2 = 2^129+13
```

Unit-weight-sparse half-recovery floor `⌈(m−n)/(4n)⌉`:

```text
P1: 79228162514264337593543950336 = 2^96  (exact)
P2: 158456325028528675187087900672 = 2^97 (exact)
```

so a unit-weight sparse Jacobi family needs `K ≥ 2^96` at P1 and `K ≥ 2^97` at P2 for half recovery — matching G231's numbers, now as a basis-independent mass floor.

## Artifacts

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G233JacobiL2MassFloorNoGo.lean` — kernel-checked abstract mass-floor theorem + sparse specialization + exact sponsor `2^96 / 2^97` floors. Axioms: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- `scripts/probes/oc_g233_l2_massfloor_no_go.py` — verifies `λ_max(VᴴV) ≤ n²`, `‖S‖² ≥ n(m−n)`, the identity `S = V·1` (recon err ~1e-12), and the exact `2^96 / 2^97` sponsor floors. All checks pass.
- `/tmp/arklib-reports/oc_g233_l2_massfloor_no_go.out` — probe output.

## Honest scope

This does not prove the production signed estimate and does not consume the target. It closes the basis-independent coefficient-mass shortcut to the analytic instantiation: no fixed coordinate subfamily (G228/G229/G231), no coherent eigen-subfamily (G232), and no bounded-L2-mass adaptive combination (G233) below the sponsor floor can carry a constant fraction of `What`. The analytic lane must retain a full high-conductor quotient-Jacobi average feeding the independent 22/43 Newton packet, per rank at r=5 and r=6 (G225: no cross-rank shortcut). CORE remains OPEN / ON-BGK.
