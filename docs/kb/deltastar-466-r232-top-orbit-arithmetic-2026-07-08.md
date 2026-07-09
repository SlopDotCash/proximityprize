# R232: arithmetic indices of top quotient spikes

Status: refines the spike-resonance obstruction.

## Probe

Script:

```text
scripts/probes/probe_r232_top_orbit_arithmetic.py
```

The quotient spectrum is enumerated by representatives

```text
1, g, g^2, ..., g^(M-1),  M = (p - 1) / n,
```

where `g` is a primitive root modulo `p`.  The probe prints the quotient index
`j` for each top spike, together with `gcd(j,M)`, quotient order `M/gcd(j,M)`,
and the spike's contribution to `mean exp(X/4)`.

## Main command

```bash
python3 scripts/probes/probe_r232_top_orbit_arithmetic.py --top 12
```

## Findings

The simple low-order-quotient-character hypothesis is false.

Examples:

```text
n=64 p=65537 M=1024
rank 1: j=0, gcd=1024, qord=1, X=29.7761, contrib=1.6695
```

The Fermat row has a very special top orbit at `j=0`.

But other bad rows are not low-order:

```text
n=64 p=48449 M=757
rank 1: j=592, gcd=1, qord=757, X=24.9925, contrib=0.6830
rank 2: j=733, gcd=1, qord=757, X=18.5827, contrib=0.1376

n=64 p=204353 M=3193
rank 1: j=2711, gcd=1, qord=3193, X=32.1212, contrib=0.9623
rank 2: j=2648, gcd=1, qord=3193, X=23.8508, contrib=0.1217
```

Even nearby passing rows can have high absolute spikes at full order:

```text
n=64 p=421313 M=6583
rank 1: j=6540, gcd=1, qord=6583, X=26.0995, contrib=0.1036
mgf=1.6670
```

The difference is not the absolute maximum alone, but the normalized
rank-weighted contribution.  Large anchors have high absolute maxima but tiny
rank contributions:

```text
n=64 p=16778497 M=262164
rank 1: j=49880, gcd=4, qord=65541, X=27.5838, contrib=0.00377
mgf=1.4139
```

## Interpretation

The bad spikes are not explained by small quotient order.  A proof route based
on classifying low-order quotient characters would miss full-order resonances
like `M=757` and `M=3193`.

The next useful hypothesis should be phase-alignment or rank-weighted:

```text
sum_{j < R} exp(X_(j)/4) / M <= explicit small budget
```

or an ancestry law that bounds how often full-order quotient indices can align
the `n` phases strongly enough to create a large Gauss-period spike.

This narrows the live obstruction from "top spikes exist" to:

```text
prove a rank-weighted anti-concentration theorem for quotient Gauss-period
phase alignments, including full-order quotient indices.
```
