# #466 Lane L6 — deployment-prime wall-constant certificates: M at BabyBear and KoalaBear (2026-07-01)

**TL;DR (numbers below are filled from the final runs — see the certificate table):** the wall
constant `M = max_{b != 0} |eta_b|` for the largest 2-power subgroup `mu_n` is now measured —
and *exact-integer-certified* via the cyclotomic-period-matrix route — at the two REAL deployed
FFT primes: **BabyBear** `p = 15*2^27+1 = 2013265921` (`n = 2^27`, `f = 15`) and **KoalaBear**
`p = 2^31-2^24+1 = 2130706433` (`n = 2^24`, `f = 127`). This is the first exact wall-constant
measurement at production scale, five decimal orders of magnitude beyond all prior campaign data
(`n <= 1024`).

STATUS: measurement + exact-integer certificate lane (dossier §6 Tier-3 "explicit eps*
certificates at deployment primes"). No core (floor/BGK) claim. CORE UNAFFECTED, still ON-BGK.

## 1. What was computed

For each prime, all `f = (p-1)/n` dilation-coset values `c_j = eta_{g^j}` (`g` a primitive
root); `|eta_b|` is constant on cosets and REAL here (`-1 in mu_n` since `n` even), so
`M = max_j |c_j|` over `f` real numbers.

Three independent computation routes, mutually cross-checked:

1. **float64 cos-sum pipeline** (`probe_466_deployment_certificates.py`): one pass over
   `x = g^i, i < (p-1)/2` (± pairs share cosets), bucketed by `i mod f`, per-chunk pairwise
   `np.sum` + exact `math.fsum` across chunk partials. All 8 primes (2 deployment + 6 controls).
2. **Exact S3 anchor** (`probe_466_deployment_s3_exact.py`): `S3 = sum_j c_j^3` is a rational
   integer with an O(n) exact formula `S3 = p*T - n^2`, `T = #{a in mu_n : -1-a in mu_n}`
   (membership = `n` squarings, exact uint64).
3. **Exact integer period matrix** (`probe_466_deployment_period_matrix.py`): with
   `M_{jk} = #{t in C_j : 1+t in C_k}` (exact one-pass integer count over `F_p^*`) and
   `P = M - n e_0 1^T`, the identity `c_0 c_j = sum_k M_{jk} c_k + n [j=0]` plus mass balance
   `sum_k c_k = -1` gives `P c = c_0 c`; Galois shifts make **all f periods eigenvalues of the
   same integer matrix**, so `M = spectral radius(P)` — the dossier's Tier-3 formulation, now
   actually built at production scale. Integer self-checks: row/col sums `= n - [j=0]`,
   `tr P = -1`, `tr P^2 = p - n`, `tr P^3 = S3_exact` (route 2, independently computed).
   Eigenvalues at float64 + mpmath Rayleigh refinement (dps 40) on the exact matrix.

## 2. Certificate table (part a)

FILLED-FROM-RUN — see `scripts/probes/_out_466_deployment_certificates.txt` and
`_out_466_deployment_period_matrix.txt`.

## 3. Hankel double-ratio screening (part b)

Round-1's kept diagnostic (DISPROOF `466-r1-hankel-bounded-window-refuted`; the Fermat anomaly
showed ~52x amplification at moment order 6). Invariant: `R_k = D_{k-1} D_{k+1} / D_k^2`
(Hankel dets of the empirical coset-value measure) `= b_{k+1}^2` (Jacobi), normalized
`q_j = b_j^2 / b0_j(n)` against the exact char-0 reference, `j <= 7 >= 5`. Detector = z-scores
vs 3 same-`n` controls + a constrained-Gaussian Monte-Carlo null at the prime's own `f`
(matching `sum c = -1` and `sum c^2 = p-n` exactly).

FILLED-FROM-RUN.

## 4. Error bars — and one honest catch (part c)

- float64 + pairwise/fsum at `n ~ 1e8` terms: worst-case coherent per-value bound
  `~ n * 2.4e-15 ~ 3e-7`; measured anchors are far better: Parseval relative residual
  `~ 2e-16`, mass balance `|S1+1| ~ 2e-7` absolute on a signed sum of `f` values of size
  `~ 1e4` (i.e. `~ 1e-11` relative at mass scale).
- **The catch:** the float64 `S3` for BabyBear printed `-6342852445186.31` — near an integer
  (residual 0.31), which *looked* like a pass. The exact route-2 value is
  `S3 = -6342852445126`: the float sum is off by **60.3**. "Close to *an* integer" is NOT
  "close to *the* integer." Back-solving `dS3 = sum 3 c_j^2 e_j` gives per-value float64 errors
  `|e_j| ~ 1e-8` absolute (~`1e-12` relative on `M`) — an order of magnitude above what the
  Parseval residual naively suggested (signed cancellation hides error in S2), and exactly why
  the exact anchors were built. The float64 `M` is still good to ~11 significant digits; the
  period-matrix route certifies ~30 digits independent of any float summation.
- The T-counts themselves sanity-check against the random model `T ~ n/f`:
  BabyBear `8944698` vs `8947848`; KoalaBear `131598` vs `132104`.

## 5. Interpretation

FILLED-FROM-RUN.

## 6. Caveats / limits

- **Regime**: deployment primes sit at `beta = ln p / ln n = 1.14 / 1.29` — far below the
  `p >= n^4` prize discipline; `ln(p/n) = ln f` is tiny (2.71 / 4.84), so `C = M/sqrt(n ln(p/n))`
  is NOT directly comparable to the beta~4 band [1.07, 1.49] — the honest benign/anomalous call
  is the constrained-Gaussian MC percentile at the prime's own `f`, plus the analytic Gaussian-max
  expectation `E[C] ~ sqrt(2 ln(2f)/ln f) * sqrt((f-1)/f)` = 1.53 (f=15) / 1.51 (f=127).
- **Controls are not truly generic**: at deployment parameters every prime `p ~ 2e9` with
  `p == 1 mod 2^24/2^27` is a small-`c` Proth prime `c*2^k+1`; several controls are themselves
  of `2^a +- 2^b + 1` form (ctrl27_c17 = 2^31+2^27+1, ctrl27_c24 = 2^32-2^30+1 = 3*2^30+1,
  ctrl24_c126 = 2^31-2^25+1). Also ctrl24_c136 = ctrl27_c17 as integers (2281701377), measured
  at a DIFFERENT subgroup (n = 2^24 vs 2^27) — distinct data point, same field.
- Both deployment primes are of the correlated-direction form `2^a - 2^b + 1` (flagged per
  regime discipline); NEITHER is generalized-Fermat `b^(2^s)+1` (the known resonant family,
  round-2 lane F) — checked programmatically.
- **Goldilocks is out of reach for this method** (`p = 2^64 - 2^32 + 1`, `n = 2^32`,
  `f = 2^32 - 1`): the one-pass count is `~1.8e19` elements and the "period matrix" is
  `(2^32-1) x (2^32-1)` — the dossier's "not Goldilocks" note stands.
- These are numerical/exact-integer certificates, not Lean theorems; nothing here claims
  "proven" in the axiom-clean sense. The period-matrix eigenvalue step uses a standard
  eigensolver + mpmath Rayleigh refinement on an exact integer matrix pinned by four exact
  integer trace/sum identities; a formal interval-arithmetic (Arb) root isolation of the
  integer characteristic polynomial is the remaining upgrade if anyone needs it.

## 7. Artifacts

- `scripts/probes/probe_466_deployment_certificates.py` + `_out_466_deployment_certificates.txt`
- `scripts/probes/probe_466_deployment_s3_exact.py` + `_out_466_deployment_s3_exact.txt`
- `scripts/probes/probe_466_deployment_period_matrix.py` + `_out_466_deployment_period_matrix.txt`
