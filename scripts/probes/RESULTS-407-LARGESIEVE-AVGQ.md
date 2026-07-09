# #407 — Large sieve / average-over-q route to the floor (REFUTED, no closure)

Technique `largesieve-avg-q`. The explicit-code prize permits choosing the prime `q`. We attempted to
prove the floor (`κ_r ≤ 1`, i.e. defect-freeness at depth `r`) holds for ALMOST ALL primes
`q ≡ 1 mod n` in `[Q, 2Q]`, `Q ≈ 2^168`, so an explicit good `q` exists — via first/second moment over
`q`. **Verdict: refuted; the route is provably weaker than the existing per-`q` norm bound. No closure.
Honesty contract holds.**

## 1. The correctly-localized object

A prime `q ≡ 1 mod n` (embedding `ζ_n ↦ g`, degree-1 prime `𝔮 = (q, g − ζ_n)`) is BAD at depth `r` iff
`𝔮 | α` for some nonzero sparse `α = Σ_{i≤r} ζ^{x_i} − Σ_{j≤r} ζ^{y_j}` (a sum of `≤ 2r` roots of
unity, `|σ(α)| ≤ 2r` at every archimedean place). Since `𝔮 | α ⟹ q | N(α)`, **the bad primes are
exactly the (correctly-split) odd prime factors of the norm set `{N(α)}`, all bounded by `(2r)^{φ(n)}`.**

Key correction (probe `_secondmoment`, `_finalcount`): the `min |N(α)| = 2` vectors are
**pure-2-power-norm** and never bad for odd `q`; the genuine defect-carriers are the box-interior
**large-odd-norm** `α` (e.g. `n=8, r=3`: largest odd prime factor of any `N(α)` is `313`; for all
`q > 313` there are zero defects). This converges with the earlier Cheng-house DISPROOF_LOG entry.

## 2. First moment (union bound) and the covering criterion

`#bad q in [Q,2Q] ≤ Σ_{α≠0} ω_{≥Q}(N(α)) ≤ A_r · φ(n) · log(2r)/log Q`, with `A_r = #distinct α ≤ n^{2r}`.
`#available primes ~ Q/(φ log Q)`. A good `q` EXISTS when

> **(\*)  `Q > n^{2r} · φ(n)² · log(2r)`.**

Verified (`_avgq`, `_deep`, `_cover`): for fixed `(n,r)`, once `Q > (2r)^{φ/2}` the defect-free
fraction → 1 (the proven norm regime); below it, a good `q` (`D ≤ baseline`) still exists in 78–90% of
the window.

## 3. Three nails — why it fails at prize scale

| nail | finding | probe |
|---|---|---|
| (\*) **reproduces the norm wall** | reach `r ≲ ½ log_n Q − 1` (=3 at `n=2^32, Q~2^256`), **4× SMALLER** than the proven per-`q` norm reach `r_max ≈ 2 log_n q` (=16). Averaging is strictly WORSE than fixing one `q`. Prize needs `r ≈ ln q ≈ 177`. | `_prizescale`, `_finalcount` |
| **thinning is a finite-φ artifact** | a window-prime `~Q` is hit only by `α` with `|N(α)| ≥ Q`, i.e. geo-mean of conjugates `≥ Q^{1/φ}`. At `φ=2^31`, `Q^{1/φ} = 2^{256/2^31} ≈ 1.0000001` ⟹ ~every `α` qualifies, `A_r^{≥Q} ~ n^{2r}`, (\*) collapses to raw. (At small `n` only 0.1–0.5% reach `|N|≈max` — misleading.) | `_finalcount` + closed-form check |
| **2nd moment no rescue at scale** | `M2/M1²` grows (≤188) and `α/badprime` large (30–290) — real overlap, union ≪ first-moment sum — but only at SMALL primes (small-norm resonance); near `Q` defects SPREAD (each large-odd-norm `α` hits its own distinct prime), union ~ sum. | `_dual`, `_secondmoment` |

## 4. The reach comparison (the punchline)

The norm wall can be read on two equivalent axes.

**Depth-`r` axis (fixed `n`, ask the largest defect-free depth):**

| `n` | `log_n q` | per-`q` norm reach `≈ 2 log_n q` | avg-over-`q` reach `≈ ½ log_n Q` | prize depth `ln q` |
|---|---|---|---|---|
| `2^8`  | 32.0 | 64.0 | 15.0 | 177 |
| `2^16` | 16.0 | 32.0 | 7.0  | 177 |
| `2^24` | 10.7 | 21.3 | 4.3  | 177 |
| `2^32` | 8.0  | 16.0 | 3.0  | 177 |

On this axis the averaging is worse by a factor ~4: its union runs over `n^{2r}` terms (`2r` in the
exponent) where the per-`q` norm bound pays only the single `φ = 2^{a−1}` once.

**`n` axis (fixed `q ~ 2^256`, ask the largest defect-free subgroup):** the per-`q` norm regime
`q > house^{φ(n)}` holds iff `256 > φ(n)·log₂(house)`, i.e. `n ≤ 2^8` (the campaign's "`n ≤ 64–256`"
boundary). The average-over-`q` criterion (\*) `Q > n^{2r}φ²log(2r)` is even more restrictive in `n`.

Either way: both reach the SAME norm wall (`n ≤ 2^8` / `r ≲ 2 log_n q`), both `~20×` short of the
prize (`n = 2^32`, `r ≈ ln q`). Averaging gives no new regime.

## 5. Honest bottom line

The heavy first-moment tail (`E_q[#defects]` dominated by the few small-norm `α` with huge
multiplicity) is a genuine obstruction; the second moment correctly quantifies the bad-prime overlap,
but the overlap is concentrated at small primes, not at the window scale `Q`. The route is **refuted**
as a path to the floor depth — it reproduces (and in fact undershoots) the norm-regime wall already
known in-tree. The prize residual (the growing-`n` Gauss-period house = generalized-Paley eigenvalue)
is untouched. No closure; nothing fabricated.

Probes: `probe_largesieve_avgq_407.py`, `probe_largesieve_avgq_deep_407.py`,
`probe_largesieve_cover_407.py`, `probe_largesieve_prizescale_407.py`,
`probe_largesieve_finalcount_407.py`, `probe_largesieve_secondmoment_407.py`,
`probe_largesieve_dual_407.py`. DISPROOF_LOG.md entry: 2026-06-13 "LARGE SIEVE / AVERAGE-OVER-q".
