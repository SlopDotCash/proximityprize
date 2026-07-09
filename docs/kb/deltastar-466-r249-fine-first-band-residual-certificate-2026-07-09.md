# R249 fine first-band residual certificate

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Question

R248 showed that a single bulk cap at `theta = 0.75` plus a high-tail cap is
too coarse for the trim-five residual CDF: raw survival monotonicity overpays
the short band `[0.75, 0.875)`.

R249 searches for finite threshold grids that certify

```text
S(theta) exp(theta / 2) <= 0.6012
```

for the trim-five residual, where `S(theta)` is residual survival divided by
the quotient carrier `M`.

## Probe

New script:

```text
scripts/probes/probe_r249_multiband_residual_certificate.py
```

It precomputes exact survival caps at grid thresholds and tail constants above
the final threshold.  For a band `[t_i, t_{i+1})`, the sufficient finite cost is

```text
S(t_i) * exp(t_{i+1} / 2).
```

## Coarse-grid failure

Command:

```bash
python3 -m py_compile scripts/probes/probe_r249_multiband_residual_certificate.py
python3 scripts/probes/probe_r249_multiband_residual_certificate.py \
  --medium-min-a 8 --medium-max-a 12 --medium-max-index 5000 \
  --min-index 512 --chunk 8192 --trim 5 --target-c 0.6012 \
  --candidates 0.775 0.8 0.825 0.85 0.875 0.9 0.925 0.95 1.0 1.0625 1.125 1.25 \
  --max-extra 5 --top 20
```

The best coarse grid fails:

```text
cost=0.60717528
bands=(0.75, 0.775)
band cost: S(0.75) * exp(0.775/2) = 0.607175
tail cost above 0.775 = 0.599021
```

The obstruction is exactly the first short band: carrying the `S(0.75)` cap
as far as `0.775` loses too much.

## Fine first-band success

Command:

```bash
python3 scripts/probes/probe_r249_multiband_residual_certificate.py \
  --medium-min-a 8 --medium-max-a 12 --medium-max-index 5000 \
  --min-index 512 --chunk 8192 --trim 5 --target-c 0.6012 \
  --candidates 0.7525 0.755 0.7575 0.76 0.7625 0.765 0.7675 0.77 0.7725 0.775 \
    0.78 0.79 0.8 0.825 0.85 0.875 0.9 0.95 1.0 \
  --max-extra 6 --top 20
```

Best grid:

```text
cost=0.60110935
slack=0.00009065
bands=(0.75, 0.7525)
```

Details:

```text
band [0.75,0.7525): S_cap=0.412121, cost=0.600383
  witness n=512 p=760321 M=1485

tail theta>=0.7525: C=0.60110935
  witness theta=0.756650 count=336
  n=512 p=417793 M=816
```

## Route update

The trim-five residual half can be split into two sharply stated proof targets
on the `n >= 256`, `M >= 512` branch:

```text
First-band bulk:
  S(0.75) <= 0.412121

Tail:
  for theta >= 0.7525,
  S(theta) <= 0.6012 * exp(-theta / 2)
```

This finite certificate implies the R238 residual CDF target with tiny slack.
It does not repair the top-five payment, whose `4.5 * sqrt(M log M)` cap was
refuted in R237; it only sharpens the residual half of the split.
