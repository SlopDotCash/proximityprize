# δ* #466 — broad grid stress for dyadic tail envelope (2026-07-08)

## Hypothesis

R66 proposed the dyadic coset tail envelope

```text
N(T) = #{C : |η_C|^2 / σ^2 ≥ T} ≤ M exp(-T/4),
M = (p-1)/n.
```

R67 tries to break it across a broader dyadic grid, including small primes and
low thresholds where bulk effects are most likely to violate a simple
exponential envelope.

Probe: `scripts/probes/probe_r67_dyadic_tail_envelope_grid.py`.

## Scan

Parameters:

```text
n ∈ {8,16,32,64,128}
starts near n^2, n^3, n^4
thresholds T ∈ {1.1,1.25,1.5,2,3,4,6,8,10,12,16,20,24,28,32}
tested rows: 132 exact dyadic coset spectra
```

Worst rows against `M exp(-T/4)`:

```text
ratio   T     count   n    p          cosets    maxX    ratio_exp(-T/3)
--------------------------------------------------------------------------------------
0.5315  1.25  14      16   577        36        6.126   0.5899
0.4801  1.1   31      64   5441       85        7.938   0.5262
0.4702  1.1   15      16   673        42        4.738   0.5153
0.4526  1.1   11      8    257        32        4.784   0.4960
0.4521  1.1   34      64   6337       99        6.453   0.4955
0.4481  1.1   97      16   4561       285       7.259   0.4911
0.4388  1.1   28      8    673        84        6.148   0.4810
0.4339  2     10      32   1217       38        6.843   0.5126
0.4295  1.1   46      128  18049      141       6.369   0.4734
```

Summary:

```text
tested=132 violations_exp(-T/4)=0
```

## Verdict

The R66 envelope survived a much broader falsification pass.  The worst cases
are not the dramatic super-Wick spike examples; they occur at very low
thresholds (`T≈1.1..1.25`) where the bulk of the distribution is being counted.

This makes the candidate theorem more plausible:

```text
For dyadic H = μ_{2^a}, normalized coset magnitudes obey
  N(T) ≤ M exp(-T/4)
for all prize-relevant thresholds T.
```

The scan also suggests that `exp(-T/3)` is often empirically safe, but the
`1/4` exponent is the more conservative proof target.

Proof direction:

* The high-tail part is controlled by exceptional-coset scarcity.
* The low-threshold part is a bulk concentration statement.
* A proof may need to combine two estimates rather than derive the whole
  envelope from a single maximum-period bound.
