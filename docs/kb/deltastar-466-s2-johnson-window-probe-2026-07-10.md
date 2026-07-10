# S2 punctured-Johnson discharge window probe (2026-07-10)

## Status

Numeric quantification (exact rational arithmetic, stdlib-only, deterministic)
of the parameter region discharged by the S2 theorem
`lineAppearingCodewords_card_le_of_punctured_johnson` /
`puncturedListBudget_of_johnson`
(`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_S2PuncturedJohnsonDischarge.lean`).

Probe: `scripts/probes/probe_s2_punctured_johnson_window.py`.

Per line with zero-set size `z` (mandatory range `z in [a, n]`, since
`PuncturedListBudget` only quantifies over non-support-eligible lines),
support `s = n - z`, center agreement `A = a - s` (Lean nat subtraction, so
`A = max(0, a + z - n)`), `N = z(1 - 1/q)`, the theorem caps the appearing
list at `l` iff

```text
(hP)   z/q <= A
(hsq)  (l+1)(A - z/q)^2 > N(N + l((k-1) - z/q)).
```

The condition is linear in `l`; a finite `l` exists iff the slope
`(A - z/q)^2 - N((k-1) - z/q)` is positive (equivalently: the punctured
parameters sit strictly inside the squared Johnson region), or the `l = 0`
inequality `A - z/q > N` already holds.

## 1. Discharged/open windows at prize shapes

Families: `rho = k/n in {1/4, 1/8, 1/16}`, `n in {2^8, 2^10, 2^12}`,
`q = n * 2^7` (scaled stand-in), plus one huge-`q` case
(`n = 2^10, k = 2^8, q = 2^64`).  `a` swept as multiples of
`a_J = ceil(sqrt(nk)) = sqrt(rho) * n`.  Representative rows
(`frac` = fraction of `z in [a, n]` discharged; open band is always a single
contiguous interval):

| family | a/a_J | frac disch. | open z-band | max minimal l |
|---|---|---|---|---|
| n=1024 k=256 q=2^17 | 0.80 | 0.0000 | [410, 1024] (all) | - |
| | 0.95 | 0.0000 | [486, 1024] (all) | - |
| | 1.00 | 0.0039 | [512, 1022] | 3045 |
| | 1.10 | 0.1515 | [563, 954] | 1304 |
| | 1.25 | 0.4545 | [640, 849] | 1242 |
| | 1.50 | **1.0000** | none | 5 |
| n=4096 k=512 q=2^19 (rho=1/8) | 1.00 | 0.0008 | [1448, 4094] | 11489 |
| | 1.50 | 0.4639 | [2172, 3203] | 7418 |
| | 2.00 | **1.0000** | none | 4 |
| n=4096 k=256 q=2^19 (rho=1/16) | 1.00 | 0.0010 | [1024, 4093] | 29542 |
| | 2.00 | 0.5793 | [2048, 2909] | 7710 |
| n=1024 k=256 q=2^64 | 1.00 | 0.0039 | [512, 1022] | 3068 |
| | 1.50 | **1.0000** | none | 5 |

The huge-`q` column is numerically indistinguishable from the scaled
stand-in: at these shapes the `1/q` corrections never move an integer
`z`-boundary.

Minimal `a` at which the ENTIRE `z in [a, n]` range is discharged (stable
across `n`, i.e. a pure rate law):

| rho | a_full / sqrt(nk) | a_full / n |
|---|---|---|
| 1/4 | 1.422 | 0.7109 |
| 1/8 | 1.813-1.815 | 0.641-0.642 |
| 1/16 | 2.375-2.387 | 0.594-0.597 |

## 2. Observed boundary law

Both expectations PASS with **zero** mismatched `z`-values across every
family/`a` pair:

- **E1 PASS** — the open band is EXACTLY the beyond-Johnson region of the
  punctured parameters: `z` is open iff `(a - s)^2 <= z(k-1)` (nat-sub `A`),
  the `1/q` corrections being invisible at integer granularity for
  `q >= n*2^7`.  In particular the low-`z` sub-band `z < n - a` (where
  `A = 0`) is open because the R2B witness split delivers no center
  agreement there; it satisfies `A^2 <= z(k-1)` trivially, so it is part of
  the same beyond-Johnson band, consistent with the hlow-map
  (`docs/kb/deltastar-466b-hlow-map-2026-07-01.md` §3): open band = the H1
  beyond-Johnson list-size problem.
- **E2 PASS** — at every prize-shaped `a` strictly below
  `sqrt(rho) * n = sqrt(nk)` (factors 0.80/0.90/0.95), the mid-band — in
  fact the whole band `[a, n]` — is OPEN.  S2 buys literally nothing below
  the Johnson radius.

The full-discharge threshold is governed by the worst point `z = a`
(smallest zero set in the quantified range), where `A = 2a - n`; setting
`a = x n` the corner condition `(2a-n)^2 > a(k-1)` reads
`(2x-1)^2 > rho x`, whose roots reproduce the observed
`x = 0.7109 (rho=1/4)`, `0.6416 (1/8)`, `0.5964 (1/16)` to all printed
digits.

## 3. Honest statement at prize shape

- S2 is real but strictly within-Johnson: at `a = a_J` it discharges only a
  sliver `z in {n-1, n}`-adjacent (frac ~0.1-0.4%), with large minimal list
  levels (`l` up to ~3*10^4) near the band edge; at `a >= a_full(rho)` it
  discharges every non-support-eligible line outright with tiny `l <= 5`.
- At prize-shaped agreement `a < sqrt(rho) n` (anything at or below the
  Johnson radius, which is where the prize lives), the ENTIRE `z`-range is
  open: the surviving obligation is exactly the beyond-Johnson punctured
  list-size problem, i.e. the same H1 wall as the far branch.  Nothing in
  the numerics suggests hidden slack in the `1/q` terms — the boundary is
  the bare Johnson curve `(a-s)^2 = z(k-1)`.

## Repro

```text
python3 scripts/probes/probe_s2_punctured_johnson_window.py
```

Exact `fractions.Fraction` evaluation of hP/hsq; minimal `l` computed in
closed form from the linear-in-`l` shape with an exact integer fixup; `l`
capped at 10^6 (cap never binds at these shapes).
