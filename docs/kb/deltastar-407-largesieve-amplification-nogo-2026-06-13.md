# δ* (#407) — the large-sieve / amplification route WALLS at L2→L∞ extraction (no-go, pinned)

**Status:** reproducible no-go; honest, NOT a closure. Diagnoses the large-sieve / amplification
attack on `B = max_{b≠0}|η_b|` and pins EXACTLY where and why it fails for thin subgroups
`n = p^{1/β}`, β≈4. Author: δ* lane (#407), 2026-06-13.

## The route and the target

Object: `η_b = Σ_{x∈μ_n} e_p(bx)`, `B = max_{b≠0}|η_b|`, prize target `B ≤ C√(n·log(p/n))`.
Parseval gives the **L2 average exactly**: `(1/p)Σ_b|η_b|² = n` (RMS = √n; verified `RMS²/n = 1.000`).
The target is the **L∞ max** `B² ~ n·log m`, `m=(p−1)/n`. The whole route is: can the large sieve /
an amplifier / a duality argument supply the missing `log m` factor and bound the MAX?

## What was tested (3 probes)

1. `probe_smoothed_max_tautology_407.py` — smoothed-max via positive kernels (Fejér family).
2. `probe_iwaniec_sarnak_gausssum_407.py` — Iwaniec–Sarnak amplification on the **dual** (Gauss-sum)
   side, exploiting the in-tree identity `η_b = (1/m)[−1 + Σ_{k=1}^{m−1} χ̄_k(b)τ(χ_k)]`, `|τ|=√p`.
3. `probe_largesieve_amplification_407.py` — the honest a-priori amplifier bound (min‖A‖ form) +
   classical large-sieve sum check.

## THREE precise walls (all reproducible, n=16,32,64 prize-diagonal, non-Fermat)

### Wall 1 — smoothing the max is a TAUTOLOGY (kernel peak aligns with spike)
For any positive-definite kernel `K` (so `K̂≥0`), `max_b|η_b|² ≤ (1/K(0))·max_c(|η|²∗K)(c)`. Measured:
the RHS **equals B² at the degenerate `K=δ` (F=1) and STRICTLY INCREASES with kernel width** F:

| n | F=1 | F=3 | F=7 | F=15 | F=31 |
|---|-----|-----|-----|------|------|
| 32 (RHS/B²) | 1.00 | 1.08 | 1.20 | 1.62 | 2.61 |
| 64 (RHS/B²) | 1.00 | 1.11 | 1.48 | 1.94 | 2.63 |

The max over the smoothing center `c` is **achieved at `c=b*`, where the kernel peak sits on the
spike unattenuated** ⇒ smoothing can never bring the max below B². Widening the kernel only adds the
`n`-level background (diagonal `n·‖K‖₁/K(0)`), making it worse. The worst frequency b* is a genuine
**isolated integer-b spike** (`|η_{b*±1}|²/B² ≈ 0.01–0.06`, measured) — so the route is not *trivially*
dead by a plateau, but smoothing is still powerless by the alignment tautology.

### Wall 2 — Iwaniec–Sarnak amplification gets NO Hecke gain (Gauss sums are orthogonal-random)
The dual coefficients `c_k = τ(χ_k)` (m−1 of them, each `|c_k|=√p`, verified to 1e-13) satisfy
Jacobi/Hasse–Davenport relations `τ(χ_i)τ(χ_j)=J·τ(χ_iχ_j)` — the would-be "Hecke multiplicativity".
The I-S amplified second moment `AmpM(a) = (1/m)Σ_b|A(b)|²|T(b)|²`, `T=mη+1`, `A=Σ_l a_l χ̄_l`, was
computed exactly. **Result: `AmpM/diagonal = 1.000 ± 0.08`** for every amplifier length L=1…100:

| n | L=3 | L=10 | L=30 | L=100 |
|---|-----|------|------|-------|
| 16 | 1.025 | 1.026 | 1.057 | 1.074 |
| 32 | 0.993 | 0.987 | 0.997 | 1.060 |
| 64 | 1.002 | 1.004 | 1.000 | 0.989 |

The off-diagonal (where the Jacobi relations live) **vanishes after orthogonality over the full
quotient group Q = F_p^×/μ_n**. The Gauss sums behave as an **orthogonal/random system**: AmpM is
purely diagonal `= ‖a‖²·(m−1)·p`. This is *exactly* why I-S works for L-functions/modular forms
(short Hecke amplifier sees multiplicative structure on a SHORT/INCOMPLETE average) but **NOT here**:
the natural b-average is the COMPLETE group, which annihilates the mixing.

### Wall 3 — the honest a-priori bound DIVERGES (short amplifier has zeros = circular)
A valid theorem needs a uniform LOWER bound on `|A(b*)|²` without knowing b*. The only universal one
is `min_b|A(b)|²`, and a **short amplifier (Fourier support L≪m) always has near-zeros on Q**:
measured `min|A|² ≈ 1e−6 … 1e−27`. So the honest a-priori bound `m·AmpM/min_b|A|²` is
**1e7 – 1e29 times the truth** — useless. Making `|A|` bounded below on all of Q requires lower-
bounding a *short character sum over Q*, which is **the same incomplete-subgroup-sum problem**.
The route is provably **CIRCULAR**.

### Confirmation — the classical large sieve sees only the average
`Σ_{j∈R}|η_{b_j}|² / |R| = n` (the L2 average) for EVERY subset R of cosets (random spaced subsets:
mean-of-subset-avg = n exactly; the max-coset spike `~n·log m` is invisible to any first/second-moment
sum). Detecting the single outlier needs the `2k`-th moment with `k≍log m` = the **moment method**,
which is the separately-walled route (char-0/Bessel energy `E_r` valid only to `r≍β`, far below
`r≍log q`; see `deltastar-407-exact-constant`, `deep-moment-wall`).

## Net (honest)

**The large-sieve / amplification route does not reach `√(n log(p/n))`; it walls at the
L2→L∞ extraction step itself.** Best bound this route establishes in the prize regime: only the
**trivial `B ≤ n`** (the diagonal `n·‖K‖₁/K(0)` floor; the amplifier cannot beat the trivial bound).
The three walls are independent and each fatal:
- (1) smoothing is a peak-alignment tautology (max stays ≥ B²);
- (2) no Hecke/Jacobi gain survives full-group orthogonality (amplified moment is purely diagonal);
- (3) the honest bound needs a lower bound on a short character sum over Q = the same open problem.

This **reduces to the same square-root-cancellation core** as every other route (BGK / Paley-graph
almost-Ramanujan / deep-moment). Nothing fabricated.

## Reproduce
- `scripts/probes/probe_smoothed_max_tautology_407.py`
- `scripts/probes/probe_iwaniec_sarnak_gausssum_407.py`
- `scripts/probes/probe_largesieve_amplification_407.py`
