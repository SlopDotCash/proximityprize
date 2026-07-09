# R232 top-spike signature inspection

Date: 2026-07-08
Issue: #466 / Proximity Prize

## Question

R231's live route is:

```text
pay top 5 quotient orbits exactly,
prove residual tail above tau = 0.75 with C ~= 0.6012 and K = 0.
```

R232 asks whether the top quotient spikes have a simple arithmetic symmetry
signature, e.g. negation pairs, inverse pairs, or primitive-root exponent
patterns.

## Probe

New script:

```text
scripts/probes/probe_r232_top_spike_signature.py
```

For selected exact rows it prints:

- top quotient values;
- primitive-root exponent/index;
- coset representative;
- signed representative size;
- inverse-coset index;
- negation-coset index;
- whether inverse/negation partners are also among the top rows.

## Rows inspected

```text
n=256 p=771073 M=3012   top4-refuter-fifth-spike
n=512 p=417793 M=816    trim5-C-witness
n=512 p=566273 M=1106   trim5-budget-witness
n=512 p=760321 M=1485   trim6-near-witness
```

Command:

```bash
python3 -m py_compile scripts/probes/probe_r232_top_spike_signature.py
python3 scripts/probes/probe_r232_top_spike_signature.py --top 12 --chunk 8192
```

## Findings

Negation is not a useful pairing: in all inspected dyadic rows, `-1 in mu_n`,
so negation stays in the same quotient coset.  The probe reports
`neg_idx = idx` and `in_top_neg = True` for every top row because it is the
same orbit, not a second companion.

Inversion is also not the missing classification: inverse cosets are usually
not top spikes.  Across the inspected top-12 rows, `in_top_inv` is false.

The top values are genuinely clustered but irregular:

```text
n=256 p=771073:
21.273030 17.872031 16.606841 16.463115 15.064649 ...

n=512 p=566273:
20.718632 18.819262 9.169805 8.395419 8.118605 ...

n=512 p=760321:
10.493838 10.483037 10.083518 9.435276 9.418663 ...
```

The fifth spike obstruction in R231 is visible at `n=256, p=771073`: after
four large rows, the fifth value is still `15.064649`, enough to refute the
top-4 residual on the broader cached subset.

## Interpretation

The top-five theorem probably cannot be a cheap symmetry lemma such as
"top spikes occur in inverse pairs."  The quotient already collapsed the
negation symmetry, and inversion does not preserve the top set.

The next target should be quantitative rather than purely orbit-theoretic:

```text
TopFiveMGFContribution + ResidualTail(C ~= 0.6012, tau = 0.75, K = 0) <= 2.
```

That can be attacked by:

- bounding the sum of the five largest `exp(X/4)` terms directly;
- proving a residual tail after deleting any five orbits, without identifying
  the orbits;
- or classifying spike clusters through additive-side variance/rep3 flatness
  rather than inverse/negation symmetry.
