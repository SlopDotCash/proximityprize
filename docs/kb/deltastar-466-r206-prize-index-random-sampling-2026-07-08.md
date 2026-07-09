# δ* #466 — R206 prize-index random sampling

R200/R202 exact sweeps enumerate every coset only for moderate quotient index
`M = (p - 1) / n`.  The prize tower has `M = 2^128`, so R206 samples random
nonzero frequencies at primes

```text
p = M*n + 1,  M >= 2^128.
```

The probe is:

```text
scripts/probes/probe_r206_prize_index_random_sampling.py
```

For each dyadic `n`, it finds the first prime of the form `M*n + 1` above the
requested minimum index, constructs an element of order `n`, samples random
frequencies `b`, and measures

```text
X_b = |Σ_{h∈μ_n} exp(2πi b h / p)|² / n.
```

It reports empirical `MGF(1/4)`, max sample value, mean, and tail excess against
the sampled version of the R189 envelope

```text
N(T) <= 0.6 S exp(-T/2) + 2.
```

This is not proof evidence; it is a falsification/stress probe aimed at the
actual huge-index prize regime that R203/R205 now isolate.

## Runs

Smoke:

```text
python3 scripts/probes/probe_r206_prize_index_random_sampling.py \
  --ns 64 128 --samples 1000 --seed 206 --min-index-power 128
```

Result:

```text
max_positive_excess=0.000000
worst_mgf=1.517792 n=64 M_offset=66
worst_maxX=16.840520 n=64 M_offset=66
```

Broader sample:

```text
python3 scripts/probes/probe_r206_prize_index_random_sampling.py \
  --ns 64 128 256 512 --samples 5000 --seed 466206 --min-index-power 128
```

Result:

```text
max_positive_excess=0.000000
worst_mgf=1.414945 n=64 M_offset=66
worst_maxX=17.305998 n=64 M_offset=66
```

The broader sample is consistent with the large-index R189/R203 picture:
quarter-MGF near `sqrt(2)`, no sampled tail-envelope violation, and no sign of
the medium-index resonances found by R202.
