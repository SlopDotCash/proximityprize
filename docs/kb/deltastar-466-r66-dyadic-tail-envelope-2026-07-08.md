# δ* #466 — dyadic exponential tail-count envelope (2026-07-08)

## Hypothesis

R64/R65 suggested replacing false moment monotonicity by an order-statistic
bound for normalized dyadic Gauss-period coset magnitudes:

```text
X_C = |η_C|^2 / σ^2,       M = (p-1)/n,
N(T) = #{cosets C : X_C ≥ T}.
```

R66 tests whether a simple exponential envelope can survive the known
adversarial dyadic primes:

```text
N(T) ≤ M exp(-T/4).
```

Probe: `scripts/probes/probe_r66_dyadic_tail_envelope.py`.

## Result

The envelope survives all tested spike and control cases with large slack.

```text
n   p          kind        cosets    alpha  maxX
----------------------------------------------------------------------
32  32993      spike       1031      0.4336 17.6363
  N1.5=207 N2=160 N3=83 N4=56 N6=22 N8=9 N10=3 N12=3 N16=1

64  264769     spike       4137      0.5205 18.0304
  N1.5=955 N2=656 N3=330 N4=176 N6=51 N8=15 N10=6 N12=3 N16=1

64  16778497   spike       262164    0.4910 27.5838
  N1.5=58183 N2=41555 N3=21871 N4=11712 N6=3515 N8=1064
  N10=355 N12=118 N16=22 N20=2 N24=2

128 2101249    small-spike 16416     0.6066 18.3198
  N1.5=3652 N2=2600 N3=1377 N4=734 N6=226 N8=62 N10=24 N12=9 N16=1

128 268437889  control     2097171   0.5959 23.6882
  N1.5=463755 N2=330664 N3=174942 N4=95115 N6=29386 N8=9352
  N10=3000 N12=954 N16=108 N20=14
```

The fitted worst exponential rate among listed thresholds is always at least
`0.4336`, so the proposed `1/4` rate is not close to tight in this data.

Additional stress scan for `n=32,64` near `n^3` and `n^4`:

```text
stress summary for exp(-T/4)
  n=32 p=32801 worst_ratio=0.3393
  n=64 p=264769 worst_ratio=0.3359
  n=32 p=33377 worst_ratio=0.3348
  n=32 p=33409 worst_ratio=0.3289
  n=32 p=33569 worst_ratio=0.3287
  n=32 p=1049473 worst_ratio=0.3260
  n=64 p=263489 worst_ratio=0.3255
  n=32 p=1049569 worst_ratio=0.3253
```

No violation occurred for the tested thresholds
`T ∈ {1.5,2,3,4,6,8,10,12,16,20,24,28}`.

## Verdict

This is now the most promising bridge shape:

```text
Dyadic Tail Envelope:
For H = μ_{2^a} ⊂ F_p^×, with p = 1 mod 2^a and nonzero additive periods η_C,
the normalized coset magnitudes satisfy

  #{C : |η_C|^2 / σ^2 ≥ T} ≤ M exp(-T/4)

for the threshold range needed by the prize moment argument.
```

If proved, this tail envelope implies high-moment control by layer-cake:

```text
E[X^r] = r ∫_0^∞ T^{r-1} P[X ≥ T] dT
       ≤ r ∫_0^∞ T^{r-1} exp(-T/4) dT
       = 4^r r!,
```

with sharper constants available from the empirical rate `≈0.43+`.

This route allows local super-Wick spikes and explains why monotonicity failed:
the top cosets can dominate a finite window, but the count of such cosets
decays exponentially in normalized height.

Next proof attack:

1. Translate dyadic periods into an explicit Walsh/Rademacher product or
   2-adic Gaussian-period recurrence.
2. Prove a sub-exponential concentration inequality for the coset-indexed
   period values.
3. Feed the resulting layer-cake moment bound into the existing tower/constant
   pipeline as a replacement for monotone propagation.
