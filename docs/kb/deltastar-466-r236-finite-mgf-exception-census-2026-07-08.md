# R236: finite direct-MGF exception census

Status: finite branch evidence for the beta-gated R234 residual route.

## Purpose

R235 proposes a split:

```text
finite/small branch + beta-gated rank-sum residual branch.
```

This note checks how large the finite branch really is by scanning the exact
quotient quarter-MGF, not the crude envelope budget.

## Small branch: M < 512

Command:

```bash
python3 scripts/probes/probe_r229_one_band_mgf_cutoff_scan.py \
  --mode medium --medium-max-a 12 --medium-max-index 511 \
  --min-index 2 --sort mgf --fail-only mgf --top 80
```

Result:

```text
total=1006
mgf_failures=1

n=64 p=7937 M=124
mgf1/4=2.752305
maxX=20.690520
```

The envelope budget fails many rows below `M=512`, but direct MGF only fails
this one row in the tested `a<=12` range.

## Intermediate branch: 512 <= M <= 5000

Exact loop by dyadic width:

```bash
for a in 6 7 8 9 10; do
  python3 scripts/probes/probe_r229_one_band_mgf_cutoff_scan.py \
    --mode medium --medium-max-a $a --medium-max-index 5000 \
    --min-index 512 --sort mgf --fail-only mgf --top 20
done
```

Through `a <= 10`, the direct-MGF failures are exactly the known rows:

```text
n=64  p=48449  M=757   mgf1/4=2.2387
n=64  p=63361  M=990   mgf1/4=2.0015
n=64  p=65537  M=1024  mgf1/4=3.2624
n=64  p=204353 M=3193  mgf1/4=2.6321
n=128 p=65537  M=512   mgf1/4=2.3068
```

No additional direct-MGF failures appeared when extending the width from
`a=8` through `a=10`; only envelope failures increased.

The attempted `a=11,12` continuation was interrupted for runtime after no new
failure pattern had appeared.  Those widths still deserve a dedicated cached
sweep before promoting this to a formal finite census.

## Current exception list

For the proof decomposition, the finite/direct branch should at least cover:

```text
(n,p,M) = (64, 7937,   124)
(n,p,M) = (64, 48449,  757)
(n,p,M) = (64, 63361,  990)
(n,p,M) = (64, 65537,  1024)
(n,p,M) = (64, 204353, 3193)
(n,p,M) = (128,65537,  512)
```

After these rows, the tested beta-gated residual branch

```text
M >= 512 and M >= n^2
```

is numerically viable with the top-8 rank-sum plus residual half-band tail
socket from R234/R235.

No prize closure is claimed.  This note narrows the finite exception branch
and distinguishes true direct-MGF failures from mere envelope-budget failures.
