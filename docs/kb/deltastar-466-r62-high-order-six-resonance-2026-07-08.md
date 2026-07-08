# δ* #466 — high-order six-resonance stress test (2026-07-08)

## Hypothesis

R61 suggested a clean boundary for Wick-normalized moment-ratio monotonicity:
failures appeared at multiples of `6` from `18` upward, while nearby non-`6`
orders stayed monotone.  R62 tested whether this was a structural iff or only
a visible low-range pattern.

Probe: `scripts/probes/probe_r62_high_order_six_resonance.py`.

## Result

Using exact coset spectra with primes `p = 1 mod |H|` near `|H|^3`, the clean
boundary is false:

```text
order p        div6 status first-failure       maxR
----------------------------------------------------------------
   62   238639 False FAIL   R2=0.9790<R3=0.9801  1.4036
   64   262337 False OK     -                    1.0000
   72   373393 True FAIL   R2=0.9819<R3=1.0012  1.2903
   76   439357 False FAIL   R4=0.9458<R5=0.9617  1.0510
   84   592873 True OK     -                    1.0000
   90   729271 True OK     -                    1.0000
   92   778873 False FAIL   R1=1.0000<R2=1.0727  3.9835
  118  1643269 False FAIL   R3=0.9776<R4=0.9859  1.2260
  120  1728121 True FAIL   R2=0.9890<R3=1.0050  2.2918

summary
mismatches: 62 76 84 90 92 96 102 114 118
```

A follow-up scale check at primes near `|H|^4` showed that several cheap-prime
failures disappear:

```text
order 62: p=14777701, fail=None
order 76: p=33363013, fail=None
```

But order `92 = 4*23` still produced failures for some primes near `|H|^4`:

```text
p=71640493 fail R3=0.9783276<R4=0.9783562, maxR=1.3537
p=71641321 fail None
p=71641781 fail None
p=71641873 fail R7=0.8477806<R8=0.8533626, maxR=1.0000
p=71642057 fail None
```

## Verdict

The clean theorem

```text
normalized moment ratios fail iff 6 divides |H|
```

is refuted.

The useful survivor is more precise: `6`-divisibility is a robust obstruction
family, but not the only way monotonicity can fail.  Some failures are
prime-sensitive arithmetic spikes in the Gauss-period spectrum rather than
order-only phenomena.

Updated proof target:

```text
For the prize dyadic family μ_{2^a}, prove monotonicity or tail domination
from its specific 2-adic Gauss-period structure.  Do not prove a theorem that
depends only on the subgroup order lacking a 6-resonance; order 92 is an
adversarial non-6 test case.
```

This pushes the search from subgroup-order classification toward a dyadic
Gauss-period tail theorem: the proof must control arithmetic spikes uniformly
for the `2^a` family, not merely exclude cubic resonance.
