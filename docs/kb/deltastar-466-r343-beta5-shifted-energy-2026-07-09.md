# R343: Beta-five shifted energy, asymptotic signal and depth barrier

## Correct production exponent

For the representative production values `n=2^30` and index `m=2^128`,

```
q = n m = n^(1 + 128/30) = n^5.266...
```

Thus the critical convolution depth of the quotient classes `(H-1)/H` is five,
not the depth-three/four shorthand suggested by `q approximately n^4`.

## Exact beta-five cells

`probe_r343_beta5_quotient_energy.py` uses quotient-only baby-step/giant-step
discrete logarithms; it never enumerates the field.  It tests the first primes
`p = 1 mod n` above `n^5`:

```
n=64:  p=1,073,741,953,  m=16,777,218
n=128: p=34,359,740,801, m=268,435,475
```

At depth five:

| `n` | support / `m` | `L2/unif` | `Linf/unif` |
|---:|---:|---:|---:|
| 64 | 327465 / 16777218 | 75.4341 | 908.817 |
| 128 | 9507675 / 268435475 | 35.4775 | 436.798 |

The normalized energy falls by approximately a factor two when `n` doubles.
This is not accidental.  Inversion leaves about `a=n/2` distinct atoms of
weight two.  Before modular collisions, the permutation-diagonal contribution
at depth five has scale

```
m * 5! * 2^10 * (n/2)^5 / n^10 = 3840 m / n^5.
```

For `p approximately n^5`, this is approximately `3840/n`: 60 at `n=64`
and 30 at `n=128`, close to the observed excesses 74.4 and 34.5.  The data are
therefore compatible with genuine quotient flatness as `n` grows.

## Why this does not yet solve the prize

Let `lambda_chi = sum_{r in H\{1}} chi(r-1)`.  Quotient Parseval gives

```
sum_chi |lambda_chi|^(2k) = m * E_k(H-1).
```

Even an optimal fifth-order excess estimate only yields a maximum bound with
an `m^(1/10)` factor.  The prize permits only `sqrt(log m)`.  In general, the
moment penalty is `m^(1/(2k))`; reducing it to `sqrt(log m)` requires

```
k at least log(m) / log(log(m)).
```

So R343 supplies favorable evidence for the shifted-energy model but refutes
constant critical depth as a complete proof strategy.  A winning version must
control the **excess over uniformity** through logarithmic depth, or derive an
independent nonlinear hypercontractive principle that bypasses the ordinary
moment-to-maximum conversion.  The former is the same growing-depth
wraparound wall in new coordinates; the latter remains the genuinely novel
target.
