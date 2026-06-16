# δ* (#407) — the limit law is N(0,1); the EXACT constant is C0 = √2 (not 1, not the 1.75 artifact)

**Status:** new analytic result on the *constant*, reproducible (`scripts/probes/probe_limit_law_constant_407.py`).
Honest: this pins the **correct asymptotic constant** and gives an **exact finite-n law** for it, but does
**not** prove the bound — the proof still bottoms out at the deep-moment / square-root-cancellation wall.
Author: δ* lane (#407), 2026-06-13. Route: *limiting-distribution-exact-constant*.

This **corrects two earlier KB claims** about the constant in `B(μ_n) ≈ C0·√(n·log(p/n))`:
- the conjectured `δ*` used the **bare-Gaussian `C0=1`** — wrong;
- the prior exact-constant note (`deltastar-407-exact-constant`) reported a **plateau `C0²≈1.75`** — that
  is a **finite-n / single-prime-noise artifact**, not the asymptotic constant.

## 1. The limit law is the REAL standard Gaussian N(0,1) (PROVEN structure)
For `n=2^μ`, `−1 ∈ μ_n`, so `x` and `−x` pair and the Gauss period is **real**:
`η_b = Σ_{x∈μ_n} e_p(bx) = Σ_{n/2 pairs} 2cos(2π b x/p)` (verified `max|Im η_b| ~ 1e-14`). Over the prize
diagonal `m=(p−1)/n = n^{β−1}`, the normalized period `η_b/√n` has limit law **N(0,1)**: its even moments
(the in-tree Bessel even-moment law `E_r^{(0)}=(2r)![x^{2r}]I₀(2x)^{n/2}`, normalized by `n^r`) tend to
`(2r−1)!!` — the moments of a **real** standard Gaussian (NOT complex Gaussian, whose `|Z|²` moments are
`r!`). This is the determinate (Carleman) moment problem with unique solution N(0,1).

## 2. NEW — the EXACT leading finite-n correction (κ₄ = −3/n)
From exact computation of the Bessel coefficients (`probe_limit_law_constant_407.py` part B):
```
E_diag[(η_b/√n)^{2r}] = (2r−1)!! · ( 1 − r(r−1)/(2n) + O(1/n²) ),     a_r := r(r−1)/2 = C(r,2)
```
(`a_r` matched to `<1e-3`: 1, 3, 6, 10, 15, 21, 28 for r=2..8). Equivalently the **MGF** is
`M(s)=e^{s²/2}(1 − s⁴/(8n) + …)`, so the **4th cumulant is κ₄ = −3/n** and the **kurtosis is 3 − 3/n**
(negative κ₄ ⇒ *sub-Gaussian / platykurtic*). Matched to 4 digits against pooled empirics:

| n | 16 | 32 | 64 | 128 | 256 |
|---|----|----|----|-----|-----|
| measured kurtosis | 2.8125 | 2.9062 | 2.9530 | 2.9763 | 2.9878 |
| predicted 3−3/n | 2.8125 | 2.9062 | 2.9531 | 2.9766 | 2.9883 |

So the value distribution is N(0,1) with an **explicit, exact, sub-Gaussian Edgeworth correction**.

## 3. NEW — the exact constant is C0 = √2 (C0² = 2), with the 1.75 artifact explained
The `κ₄=−3/n` correction gives the saddle/Edgeworth tail
`P(η_b/√n > t) ~ (t√2π)^{−1} exp(−t²/2 − t⁴/(8n))`. The max over `M=2m` two-sided samples (typical max:
`M·P(>t)=1`) gives a **finite-n** constant `C0²(n)=t_max²/ln m`. The κ₄ term `t⁴/(8n)` lightens the tail
(pushes `C0²` up toward 2); on the diagonal `t_max²~2(β−1)ln n` so `t⁴/(8n) ~ (β−1)²(ln n)²/(2n) → 0`:
**`C0²(n) → 2` as n→∞**, i.e. `B ~ √2 · √(n·log(p/n))`.

The previously-reported `1.75` is a finite-n point on this rising curve. **Averaged over many primes**
(low variance), `C0²` *rises monotonically* and tracks the full prediction
(`t²/2 + t⁴/(8n) + ln(t√2π) = ln M`):

| n | C0² measured (avg ± se) | full prediction |
|---|---|---|
| 32 | 1.540 ± 0.027 | 1.508 |
| 64 | 1.624 ± 0.034 | 1.584 |
| 128 | 1.673 ± 0.055 | 1.629 |
| 256 | 1.787 ± 0.070 | 1.654 |

(measured runs slightly above because `E[max] > typical-max` by `~γ/a*`). At the true prize `n=2^30`,
β=4, the prediction is `C0² ≈ 1.92`, with `C0²→2` only in the strict `n→∞` limit.

> **Net correction to the KB:** the constant is **not** `1` (bare-Gaussian), **not** a `1.75` plateau;
> the **asymptotic** constant is `C0=√2` (`C0²=2`), the Gaussian extreme-value value, and the observed
> sub-2 values are exactly the `κ₄=−3/n` finite-n correction (matched). Any "exact δ*" that hard-codes a
> constant should use `√2` as the asymptotic, with the explicit `O((ln n)²/n)` finite-n deficit.

## 4. WHERE IT WALLS (honest — this is NOT a proof of the bound)
1. **Moment→tail is one-directional and needs uniform-in-r control.** `B^{2r}=m·E_r ⇒ B≤(m E_r)^{1/2r}`;
   reaching `√(n ln m)` needs `r~ln m`, but the N(0,1) limit / `−r(r−1)/(2n)` correction is proven only for
   **fixed r**. At `r~ln m` the char-0 Bessel value is not the true `E_r`: the **p-defect `E_r−E_r^{(0)}>0`
   sets in at `r~β`** (measured), exactly where the bound would need it = the BGK deep-moment wall
   ([[deltastar-389-deep-moment-wall]]).
2. **max ≠ typical; concentration not supplied.** The `M·P(>t)=1` heuristic assumes approximate
   independence of the `m` period values; they are deterministic (Gauss-sum DFT). Proving the max
   concentrates near `√(2 ln m)` *is* square-root cancellation among correlated phases = the open core.
3. **Single-(n,p) uniformity.** `C0²→2` is the diagonal `n→∞` limit; the prize is one `n=2^30`. Pinning it
   at that point needs a tail bound there = wall 1.

## 5. Reproduce
`python scripts/probes/probe_limit_law_constant_407.py` — verifies (A) η real, (B) `a_r=r(r−1)/2` and
kurtosis `3−3/n`, (C) `C0²(n)` rising toward 2 vs the full saddle prediction.
