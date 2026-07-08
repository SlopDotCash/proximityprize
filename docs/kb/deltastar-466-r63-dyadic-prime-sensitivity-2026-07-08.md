# δ* #466 — dyadic prime-sensitivity refutes universal monotonicity (2026-07-08)

## Hypothesis

After R62 refuted an order-only classification for general multiplicative
subgroups, R63 tested the actual prize family `H = μ_{2^a}`.  The optimistic
version was:

```text
For every admissible prime p = 1 mod 2^a, the Wick-normalized ratios R_r(μ_{2^a})
are nonincreasing in r.
```

Probe: `scripts/probes/probe_r63_dyadic_prime_sensitivity.py`.

## Result

The universal dyadic monotonicity hypothesis is false.

Exact coset-spectrum scan:

```text
n=32 max_r=16
  n^3      start=32768      primes=8  failures=1 min_gap=-0.999249
    FAIL p=32993 R1=1<R2=1.21072 maxR=5.50341
  n^4      start=1048576    primes=8  failures=0 min_gap=0.00268585

n=64 max_r=16
  n^3      start=262144     primes=8  failures=2 min_gap=-0.200041
    FAIL p=264769 R3=0.976361<R4=1.03805 maxR=1.67898
    FAIL p=265921 R4=0.964666<R5=0.972762 maxR=1
  n^4      start=16777216   primes=5  failures=1 min_gap=-0.610285
    FAIL p=16778497 R4=0.96333<R5=1.01242 maxR=4.21667

n=128 max_r=12
  n^3      start=2097152    primes=5  failures=1 min_gap=-0.00308612
    FAIL p=2101249 R4=0.971489<R5=0.974575 maxR=1
  n^4      start=268435456  primes=2  failures=0 min_gap=0.0078319

n=256 anchor p=16777729
  failures=None R1=1.00000 R2=0.99482 R3=0.97956 R4=0.94525 R5=0.88403 R6=0.79337 R7=0.67767 R8=0.54744
```

Direct rerun of the failing spectra:

```text
n=32 p=32993 q=1031 v2(p-1)=5
  R1=1 R2=1.21072 R3=1.6442 R4=2.33286 R5=3.25131 R6=4.25056 R7=5.08126 R8=5.50341

n=64 p=16778497 q=262164 v2(p-1)=8
  R1=1 R2=0.984301 R3=0.964464 R4=0.96333 R5=1.01242 R6=1.14927
  R7=1.41034 R8=1.81635 R9=2.35387 R10=2.96416
```

## Verdict

The R58/R59 monotonicity bridge cannot be the final prize proof in universal
form.  Even dyadic subgroups have prime-sensitive arithmetic spikes in their
Gauss-period spectra.

The surviving path is weaker and more realistic:

```text
Prove a dyadic Gauss-period tail bound strong enough for the prize, allowing
local increases and bounded super-Wick windows, rather than requiring
R_{r+1} ≤ R_r for every r.
```

Adversarial tests for future proof attempts:

```text
(n,p) = (32,32993), (64,264769), (64,265921), (64,16778497), (128,2101249).
```

Any proposed dyadic moment theorem must explicitly survive these primes.  A
proof that silently propagates from low rungs by monotonicity is proving a
false statement.
