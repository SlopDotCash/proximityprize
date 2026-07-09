# R228 natural quotient-tail sweep

Date: 2026-07-08
Issue: #466 / Proximity Prize

## Claim tested

R227 reduces the prize endpoint to the natural quotient-tail envelope

```text
#{quotient cosets with X >= T} <= 0.6 * M * exp(-T/2) + 2,
```

where `M = (p - 1) / n` and `X` is the normalized squared Gauss-period value
on one representative per `mu_n`-coset.

R220 verified this on the main anchor rows.  R228 broadens the check to medium
dyadic rows and selected large-grid rows with
`scripts/probes/probe_r228_natural_quotient_tail_sweep.py`.

## Results

Smoke command:

```bash
python3 -m py_compile scripts/probes/probe_r228_natural_quotient_tail_sweep.py
python3 scripts/probes/probe_r228_natural_quotient_tail_sweep.py \
  --skip-large --medium-max-a 9 --medium-max-index 128 --chunk 8192 --top 20 --step 0.5
```

Output summary:

```text
R228 natural quotient-tail sweep: C=0.6 K=2.0 step=0.5 min_theta=1.0 tested=221 violations=1
max_excess=0.972079
positive_count=1
```

The violating row is:

```text
excess=0.972079
T=1.00
count=39
n=64
p=6337
M=99
maxX=6.453
mgf1/4=1.3534
```

A broader medium sweep gives additional failures:

```bash
python3 scripts/probes/probe_r228_natural_quotient_tail_sweep.py \
  --skip-large --medium-max-a 11 --medium-max-index 512 --chunk 8192 --top 20 --step 0.5
```

Summary:

```text
R228 natural quotient-tail sweep: C=0.6 K=2.0 step=0.5 min_theta=1.0 tested=932 violations=5
max_excess=1.760647
positive_count=5
```

Top failures:

```text
excess=1.760647  T=1.00  count=78  n=2048  p=417793  M=204
excess=1.431...  T=1.00  count=34  n=1024  p=86017   M=84
excess=0.972079  T=1.00  count=39  n=64    p=6337    M=99
excess=0.373...  T=8.00  count=8   n=128   p=65537   M=512
excess=0.196...  T=11.50 count=3   n=256   p=107777  M=421
```

Filtering to `M >= 128` is not enough:

```bash
python3 scripts/probes/probe_r228_natural_quotient_tail_sweep.py \
  --skip-large --medium-max-a 11 --medium-max-index 512 --chunk 8192 \
  --top 10 --step 0.5 --min-index 128
```

Summary:

```text
tested=667 violations=3
max_excess=1.760647
```

The remaining failures are `M=204`, `M=512`, and `M=421`, so a pure
large-index cutoff below this range does not rescue the `+2` envelope.

The original R220 anchor set remains clean:

```bash
python3 scripts/probes/probe_r228_natural_quotient_tail_sweep.py \
  --skip-large --medium-max-a 2 --medium-max-index 1 --chunk 32768 --top 20 --step 0.5
```

Summary:

```text
tested=4 violations=0
max_excess=-1.002631
```

## Interpretation

The literal universal R227 natural quotient hypothesis with `+2` is false.
The failure is not caused by raw-vs-quotient multiplicity; it occurs directly
on quotient counts.  It also persists when the threshold grid starts at the
R220-compatible `T >= 1`.

This does not invalidate the Lean bookkeeping in R223-R227.  It invalidates
only the clean analytic residual currently fed into R227.  The next viable
versions should add one of:

- a finite exception branch that explicitly covers the observed medium rows;
- a larger additive quotient spike budget;
- a strengthened bulk constant near low thresholds;
- a threshold split that treats `T = 1` and high-spike thresholds separately.

R227 is therefore still a useful endpoint, but the residual should not be
advertised as the prize-winning analytic claim in its current universal form.
