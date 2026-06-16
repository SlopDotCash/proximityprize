# delta* sweep A36 — Geometric-moment-growth conditional rescue (Bessel escape): REFUTED

Date: 2026-06-14. Type: numerical-probe. Status: **REFUTED** (the geometric escape; the
389-T15 retraction is confirmed and the mechanism is now pinned, at the genuinely-live band,
n up to 64). Artifact: `scripts/probes/sweep_A36_geometric_growth.py`.

## The question (merged 389-T15)

The moment method gives the prize floor `B(μ_n) = max_{b≠0}|S_b| ≤ (q·E_r)^{1/2r}`, where
`S_b = Σ_{x∈μ_n} e_p(bx)` and `E_r^(p)(μ_n) = (1/q)Σ_b |S_b|^{2r}` (Parseval). To reach
`B ≤ C'·√(n·log q)` one needs `E_r^(p)` to stay near its char-0 Bessel value
`E_r^∞ = (2r)![x^r] I₀(2√x)^{n/2}` out to the saddle depth `r ~ log q`.

"Exact cleanness" (`E_r^(p) = E_r^∞` to depth `log q`) is **provably false** in the prize
regime: by Fourier positivity the anomaly `A_r := E_r^(p) − E_r^∞ ≥ 0` is forced `> 0` once
`q·E_r^∞ < n^{2r}` (crossover `r* ~ β+1`, far below `log q`). A36 asks the strictly **weaker,
reopenable** conditional: the route survives if the excess grows at most **geometrically**,
`A_{r+1}/A_r ≤ C` for an n-independent constant `C`, because then `E_r^(p) ≤ E_r^∞ + C^r·const`
and the saddle bound inflates by only `√C`:  `B ≤ √C·√(n·log q)` — still a `√(n log)` law.

389-T15 retracted this ("off-diagonal grows like `n^r` past `log_n p`") but the retraction was
**computation-limited** (n=32, `r=4→5` excess ×5.7 was still *below* the crossover, i.e. inside
the clean regime / mirage). A36 measures the step-ratio squarely in the live band
`r ∈ [r_max, log₂ p]` at the largest FFT-feasible n.

## Method (exact, no sampling)

- Period spectrum `|S_b|²` for all `b` via one real FFT of the `μ_n` indicator over `Z/p`.
- `E_r^(p) = (1/p)Σ_b |S_b|^{2r}` (full) and `E_off(r) = (1/p)Σ_{b≠0}|S_b|^{2r}` (the object the
  floor actually uses), both EXACT for every `r`.
- `E_r^∞` via the char-0 Bessel even-moment law in EXACT rational arithmetic (sympy `Fraction`).
- Track `A_r`, the step-ratios `A_{r+1}/A_r` and `E_off(r+1)/E_off(r)`, the diagonal share
  `A_r/(n^{2r}/p)`, and the saddle bound `(q·E_off)^{1/2r}/√(n·log q)`.
- Prize-shaped cases `(n,β)`: (8, 5), (8, 6), (16, 4), (16, 4.5), (32, 4), (64, 3), (64, 3.4)
  — pushing n to 64 (the binding tension: FFT needs `p ≲ 1.5·10^7`, so high-n forces lower β).

## Result — REFUTED, two ways, with the mechanism pinned

| n | β | p | rho_tot | n² | rho_off | Bmax² | n·log q |
|---|---|---|---|---|---|---|---|
| 16 | 4.0 | 65617 | 515 | 256 | 138 | 177 | 178 |
| 16 | 4.5 | 262193 | 458 | 256 | 153 | 202 | 200 |
| 32 | 4.0 | 1048609 | 1075 | 1024 | 399 | 528 | 444 |
| 64 | 3.0 | 262337 | 4397 | 4096 | 527 | 714 | 799 |
| 64 | 3.4 | 1383553 | 4296 | 4096 | 687 | 923 | 905 |

(`rho_*` = geometric-mean step-ratio across the band; n=8 omitted — excess is machine-zero,
the known small-n "mirage" where the crossover sits at/above the saddle.)

**1. The TOTAL excess `A_r` is diagonal-dominated.** `A_r → n^{2r}/p` *exactly*: the diagonal
share `A_r/(n^{2r}/p) → 1.0000` (n=64 hits 1.0000 by r=12). This is just the trivial `b=0`
term `|S_0|^{2r}/p = n^{2r}/p` that the char-0 Bessel series has no analog of. Hence the
total-excess step-ratio `A_{r+1}/A_r → n²` exactly. The geometric condition `A_{r+1}/A_r ≤ C`
is **violated**: the "constant" is `n²`, unbounded in n. Any "compare `E_r^(p)` to the Bessel
baseline" instantiation of the geometric-growth idea fails here for a trivial reason.

**2. The OFF-DIAGONAL energy `E_off` (the object the floor actually uses) is TAUTOLOGICAL.**
Stripping the `b=0` term, the step-ratio `E_off(r+1)/E_off(r)` **climbs monotonically in r**
(n=16: 70→166 and still rising; n=32: 150→497; n=64: 306→856) toward the limit
`Bmax² ≈ n·log q` (the worst off-diagonal period, squared). Consequently
`(q·E_off)^{1/2r} → Bmax` — the moment bound converges to **the very quantity it is meant to
bound**. The `(q·E_off)^{1/2r}/floor` column decreases monotonically toward `Bmax/√(n log q) ≈
1.0–1.2`, never below. So even the "right" off-diagonal energy yields no constant `C` with
`B ≤ √C·√(n log q)`: the best it gives is `B ≤ Bmax` (vacuous), and the step-ratio is `n`-dependent
(`~ n·log q`), not a bounded constant.

## Why this is sharper than "the excess is too big"

The deeper finding is #2: the off-diagonal moment method is **structurally tautological at the
saddle**. Because `E_off` is dominated by its largest term once `r` is large, `(q·E_off)^{1/2r}`
relaxes to `Bmax = max_{b≠0}|S_b|` regardless of the *shape* of the moment growth. No
geometric/sub-geometric envelope can produce a bound below `Bmax` by a constant factor, because
the limit of the bound IS `Bmax`. The constant factor visible at small `r` (the `B/floor` column
sitting at ≈1.2 in the band) is the *gap to `Bmax`*, and it shrinks to the prize-floor margin
`Bmax/√(n log q)` (numerically ≈ 1.0–1.2) exactly as `r → r_saddle`. So the moment route can
*confirm* the floor is roughly `√(n log q)` once you already know `Bmax ≈ √(n log q)` — but it
cannot *prove* it. This is consistent with, and gives the precise mechanism for, the prior
thread findings ("deep-moment validity is provably false," "the moment proof route is dead at
prize scale"): the moments aren't merely anomalous, they are **circular** at the depth required.

## Honest scope / what is NOT claimed

- This is a numerical refutation of the *geometric-growth escape* (a proposed proof route), at
  n ≤ 64 (FFT cap). It does NOT refute the floor conjecture `B ≤ C'√(n log q)` itself — the
  `B/floor` ratios stay ≈ 1.0–1.2 in-band, consistent with the floor holding. It says the
  *moment method* cannot prove it.
- The n=8 machine-zero excess is the documented small-n mirage (anomaly onset above the saddle),
  not evidence for the escape.
- The open core is unchanged: a non-moment handle on `Bmax` (Gauss-sum joint independence /
  effective Katz-monodromy, the `B`-form). The contribution here is to **close off the moment
  route as a rescue** with the precise tautology mechanism, so future effort is not spent
  re-attempting a geometric-envelope moment argument.

## Cross-refs

- 389-T15 (the retracted escape) — CONFIRMED, mechanism pinned.
- Prior #407 thread: "Deep-moment validity is PROVABLY false in the prize regime" (forced
  anomaly, crossover `r* → β+1`); "Resolving the contradiction: the moment route is provably
  dead at prize scale"; cosh-MGF / Gaussian-relaxation floor-losing no-go. A36 supplies the
  off-diagonal tautology that underlies all of them.
- MEMORY: [[arklib-389-deep-moment-wall]] (B ≲ n^{3/4+o(1)} via moments; `r_opt/r_max ≈ a/2`).
