# δ* #466 — R202 medium-index direct split

R200 showed that the largest large-branch spike ratio in the tested set is not
at a huge coset count, but near the lower edge (`M = 36`).  R202 tests a more
aggressive split:

```text
M < 1024   -> direct MGF(1/4) <= 2 certificates,
M >= 1024  -> large-index tail plus spike/log-max route.
```

The probe is:

```text
scripts/probes/probe_r202_medium_index_direct_split.py
```

It exhausts rows `p = M*n + 1` prime for dyadic `n = 2^a` and `M < 1024`
through a configurable `a`, then uses the R200 vectorized case generator to
sample rows with `M >= 1024`.

This is a hypothesis test, not a theorem.  A positive direct MGF violation
below the split or a large spike-ratio violation above the split falsifies the
proposed proof partition.

## Result

Smoke:

```text
python3 scripts/probes/probe_r202_medium_index_direct_split.py \
  --medium-max-a 10 --large-max-n 256 --large-max-p 30000000 \
  --large-primes-per-start 1 --chunk 32768
```

found:

```text
medium_tested=1592 large_tested=9
medium_mgf_violations=4
large_spike_target_violations=0
worst_medium_mgf=2.752305 M=124 n=64 p=7937
worst_large_spike_ratio=0.009261 M=1025 n=32 p=32801
```

Deeper vectorized run:

```text
python3 scripts/probes/probe_r202_medium_index_direct_split.py \
  --medium-max-a 14 --large-max-n 512 --large-max-p 350000000 \
  --large-primes-per-start 1 --chunk 4096
```

found:

```text
medium_tested=2161 large_tested=14
medium_mgf_violations=4
large_spike_target_violations=0
worst_medium_mgf=2.752305 M=124 n=64 p=7937
worst_large_spike_ratio=0.009261 M=1025 n=32 p=32801
worst_large_mgf=1.413067 M=262151 n=512 p=134221313
```

Conclusion: the proposed `M < 1024` direct-cert branch is false as a universal
all-primes statement.  The useful surviving hypothesis is instead
large-index-only: in the actual prize tower, the quotient index is enormous at
every child level, so the medium resonant rows should not be part of the final
prize route.
