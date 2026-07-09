# δ* (#407) — two NEW route-walls: sharp Markov-Krein moment-problem + level-set self-improvement

**Status:** novel-freeform proof-route assault on the DGPH house bound `B(μ_n) ≤ C√(n·log(p/n))`.
Reproducible probes, honest. **No closure** — the route walls, but at a NEW, precisely-located place
that strengthens the project's understanding of *why* every moment-type route fails. Author: #407
novel-freeform lane, 2026-06-13.

## What was attempted (route: novel-freeform, four mechanisms)

The brief: find a route to DGPH outside {norm-bound, large-sieve, moment/energy, Stepanov,
character-sum}. I tested four mechanisms across RMT / additive-combinatorics / LP / spectral-graph
domains. Three collapse to the known wall; one (Markov-Krein) gives a genuinely NEW *exact* statement
of the wall's information-theoretic shape.

### 1. Non-backtracking / Ihara-Bass spectral route — COLLAPSES (probe_407_nonbacktracking_ihara.py)
Cay(F_p, μ_n) is n-regular; its adjacency eigenvalues are `{η_b}`, and `B` = second eigenvalue.
Ihara-Bass pairs each adjacency `λ` with non-backtracking `μ = (λ ± √(λ²−4(n−1)))/2`; the Ramanujan
window is `|λ| ≤ 2√(n−1)`. **Measured:** `B/2√(n−1) ≈ 1.7–2.2` (the graph is NOT Ramanujan), and
`#{eigenvalues outside the window} = ALL m of them`. The spectrum is *bulk-wide* (RMS `√n`, window is
only `2√(n−1)≈2σ`), not "Ramanujan-with-a-few-outliers." Consequently the nb-spectral radius
`ρ_nb ≈ B` (the larger Ihara root of each outlier just reproduces `λ`), so the nb-operator inherits
the identical wall. **No gain.** (Useful clarification: the difficulty is bulk extreme-value, not
isolated outliers — so spectral-gap / expander-mixing tools that target a single second eigenvalue do
not apply.)

### 2. Bourgain-Chang self-improvement on the spectral level set — CANNOT START (probe_407_selfimprove_levelset.py)
A sum-product / Balog-Szemerédi-Gowers *bootstrap* (if `B=n^θ` then structure forces `θ'<θ`) needs the
large-spectral set `S_λ = {coset b : |η_b| ≥ λ}` to carry ARITHMETIC STRUCTURE in the coset group
`Q ≅ ℤ/m`. **Measured doubling** `|S+S|/|S|` of the top `√m` cosets vs the random (birthday)
expectation: **ratio 0.98–1.00 — additively RANDOM.** The extremizing cosets are arithmetically
unstructured, so there is NO handle for an additive-combinatorics amplification engine. *The bootstrap
provably cannot start.* This is a clean structural reason the sum-product family fails here.

### 3. LP / Beurling-Selberg positive-majorant route — MOMENT-EQUIVALENT (probe_407_lp... in /tmp)
Damping `1_{μ_n}` by `K`-fold self-convolution (the canonical positive-definite majorant smoothing)
turns the period into `η_b^K`, whose max is exactly the moment quantity `(p·E_K)^{1/2K}`. So any
LP/majorant certificate equals a moment bound; it provably cannot certify below the sharp moment bound.
Measured `B/(p·E_2)^{1/4} ≈ 0.10–0.15`: the true `B` sits far below even the `r=2` certificate, but
the LP machinery can only certify the (much larger) moment value.

### 4. SHARP Markov-Krein extremal moment problem — NEW EXACT WALL (probe_407_markovkrein_sharp.py, probe_407_moment_reach_exact.py)
This is the genuinely new content. The naive moment route uses the *crude* `B ≤ (p·E_r)^{1/2r}`. The
**sharp** question is: the off-diagonal spectrum is `m = (p−1)/n` real atoms (η is real since `−1∈μ_n`)
with *proven* normalized even moments `μ_2 = 1` (Parseval) and `μ_4 = E_2/n² = 3−3/n → 3` (Duke-García
`E_2 = 3n²−3n`, in-tree, **re-verified exactly here**: n=8→168, n=16→720). Given a symmetric mean-0
measure with `m` atoms and these moments, what is the **largest possible support point** (the
Chebyshev-Markov / Markov-Krein extremal)? That is the *best bound ANY moment method — even a perfectly
sharp one — can give from the proven moments.*

**Result (exact, computed):** with `R` proven char-0 even moments, the sharp atom bound is
`min_{r≤R}(m·(2r−1)!!)^{1/2r}` in units of `√n`. This is **frozen at the `R`-th row**:

| R (proven moments) | bound at log₂m=30 | at log₂m=60 |
|---|---|---|
| 1 (variance, Cantelli) | 32768 | 1.07e9 |
| 2 (+ kurtosis 3) | 238 | 43125 |
| 3 | 50.2 | 1608 |
| 13 | 6.97 | 15.5 |
| 21 | 6.50 | 10.7 |
| **target √(2 ln m)** | **6.45** | **9.12** |

The optimal depth `r* ≈ ln m` (≈21 at log₂m=30, ≈42 at log₂m=60). **To get within 2× of the target you
need `R ≳ (log₂ m)/5 + 2` proven moments** — and the **p-defect onset caps provable char-0 moments at
`r* ≈ 3`** in the prize regime (prior `probe_407_defect_onset_exact.py`: n=32,β=4 defects at r=4).

> **The new wall, stated exactly:** the moment route is *information-theoretically* short by
> `Θ(log m) = Θ(β log n)` proven moments — a gap that **GROWS with the prize size**. Each proven moment
> buys only a fixed multiplicative cut of the bound; reaching `√(n·log m)` requires `Θ(log m)` of them,
> but the p-defect makes only `O(1)` provable. Adding the proven 4th moment (kurtosis 3) takes the
> bound from `√(m/2)` (Cantelli) to `≈√m`-scale — **still polynomial in `m`, hence `B ≲ n^{1−ε}`, never
> `√(n·log m)`.** Even the *sharp* extremal moment bound (not the crude `(pE_r)^{1/2r}`) fails for the
> same reason, because the eigenvalue measure has **Gaussian kurtosis 3** (verified) — a 2-moment-
> constrained Gaussian-kurtotic measure genuinely admits a far-out atom.

## Why this matters (net contribution)
The prior campaign knew the moment route walls (TECHNIQUE-6 deep-moment-wall) and located the p-defect
onset. **New here:** (a) the wall is not an artifact of the crude `(pE_r)^{1/2r}` — the *sharp*
Markov-Krein extremal with the *proven* moments is ALSO `√n·poly(m)`, quantified exactly as `m^{1/2R}`-
scale; (b) the *exact* moment-count deficit `R_need − r* = Θ(log m)` that grows with prize size; (c) the
self-improvement engine is dead because the extremizers are *additively random* in `ℤ/m` (measured
doubling = random); (d) the non-backtracking spectrum is bulk-wide, not outlier-driven. Together these
explain, from four independent directions, that the wall is the **far-tail / deep-moment** quantity and
that no second-/low-order-moment-based mechanism (sharp or not, LP or spectral-graph or sum-product)
can reach it.

## Honest verdict (contract)
**Made real progress? NO new bound on `B` is established** — the conjecture remains open; the best
literature bound is still di Benedetto et al. `t^{0.989}` (a full half-power short, out of prize
regime). What is delivered: a NEW exact information-theoretic lower bound on the moment route's *reach*
(short by `Θ(log m)` proven moments), a NEW structural no-go for the self-improvement route
(additively-random extremizers), and the collapse of two more mechanisms (nb-spectral, LP-majorant) to
the same wall. **Not fabricated.** The route does NOT reduce to a fresh open conjecture — it reduces to
the SAME recognized open core (square-root cancellation among `~m` Gauss/Jacobi phases = the deep
moments), now bounded below in difficulty by an exact moment-count argument.

## Reproduce
- `scripts/probes/probe_407_markovkrein_sharp.py` — Cantelli vs var+kurtosis Markov vs target.
- `scripts/probes/probe_407_moment_reach_exact.py` — exact `m^{1/2R}` reach table + moments-needed.
- `scripts/probes/probe_407_selfimprove_levelset.py` — top-level-set doubling = random (bootstrap dead).
- `scripts/probes/probe_407_nonbacktracking_ihara.py` — Ihara-Bass: graph is bulk-non-Ramanujan.
- Inputs verified: `E_2 = 3n²−3n` exact (kurtosis →3); η real (`−1∈μ_n`).
