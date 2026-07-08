# δ* #466 — R213 prize-index tail-rate fit

R212 names the remaining child law with the conservative R189 tail:

```text
N(T) <= 0.6 * S * exp(-T/2) + 2.
```

R213 tests whether the actual `M >= 2^128` prize-index samples support a
stronger exponential rate.  For candidate `alpha`, it reports the least sampled
bulk constant `C` needed for

```text
N(T) <= C * S * exp(-alpha*T) + 2.
```

The probe is:

```text
scripts/probes/probe_r213_prize_index_tail_rate_fit.py
```

This is not proof evidence.  Its job is to generate/refute sharper analytic
hypotheses for the `LargeIndexNormalizedChildLaw` target.

## 2026-07-08 run log

Compile hygiene:

```text
python3 -m py_compile scripts/probes/probe_r213_prize_index_tail_rate_fit.py
```

passed.

Smoke command:

```text
python3 scripts/probes/probe_r213_prize_index_tail_rate_fit.py --ns 64 128 --samples 5000 --seed 213 --min-index-power 128
```

Output:

```text
R213 prize-index tail-rate fit samples=5000 min_index=2^128 K=2.0
n     M_offset  mgf1/4  maxX    meanX   C@a=0.5  C@a=0.625  C@a=0.75  C@a=1
------------------------------------------------------------------------------------------------------------------------
64    66        1.4399  19.125  1.0072  0.5223    1.3228    5.5692    98.7158 
128   191       1.4359  20.020  1.0091  0.5296    0.6827    2.1697    29.0524 

summary
rate=0.5 worst_C=0.529569 n=128 M_offset=191 T=1.00 count=1608
rate=0.625 worst_C=1.322792 n=64 M_offset=66 T=11.50 count=7
rate=0.75 worst_C=5.569163 n=64 M_offset=66 T=11.50 count=7
rate=1 worst_C=98.715771 n=64 M_offset=66 T=11.50 count=7
```

Broad command:

```text
python3 scripts/probes/probe_r213_prize_index_tail_rate_fit.py --ns 64 128 256 512 --samples 20000 --seed 466213 --min-index-power 128
```

Output:

```text
R213 prize-index tail-rate fit samples=20000 min_index=2^128 K=2.0
n     M_offset  mgf1/4  maxX    meanX   C@a=0.5  C@a=0.625  C@a=0.75  C@a=1
------------------------------------------------------------------------------------------------------------------------
64    66        1.3958  14.425  0.9910  0.5241    0.6516    2.2277    39.4863 
128   191       1.4029  15.772  1.0006  0.5357    0.9944    4.4567    109.4125
256   44        1.4144  16.758  1.0074  0.5298    1.2939    8.1377    444.3055
512   64        1.4076  16.350  1.0020  0.5292    0.8445    4.2886    110.6033

summary
rate=0.5 worst_C=0.535670 n=128 M_offset=191 T=1.00 count=6500
rate=0.625 worst_C=1.293853 n=256 M_offset=44 T=14.50 count=5
rate=0.75 worst_C=8.137740 n=256 M_offset=44 T=16.00 count=3
rate=1 worst_C=444.305526 n=256 M_offset=44 T=16.00 count=3
```

Readout: the sampled `alpha = 1/2` constant remains below the conservative
`0.6` target on these rows, while stronger rates are dominated by a handful of
large samples after the two-spike reserve.  This supports keeping the R189/R212
rate for the formal child-law target rather than spending the next proof pass on
a faster exponential tail.
