# #466 R308 — relation-web anatomy: the `c=3` binomial family has excess `60n²−90n`

## Question

R307 refuted the beta-frontier rescue for depth-3 exact Wick: high-beta prime factors of
`c^(n/2)+1 = Norm(c+ζ)` can still violate `E₃ ≤ 15n³`.  But not every binomial norm divisor
is dangerous.  R308 asks what distinguishes the dangerous cases.

## Probe

New script:

```text
scripts/probes/probe_r308_relation_web_anatomy.py
```

It prints the actual collision fibers in the R305/R306 char-zero shadow pushforward.  For a
prime `p ≡ 1 (mod n)`, it groups the exact char-zero 3-sum vectors by their value modulo `p`
and reports the positive `L²` delta per fiber.

Commands:

```bash
python3 scripts/probes/probe_r308_relation_web_anatomy.py \
  --n 128 --p 1716841910146256242328924544641 --top 20

python3 scripts/probes/probe_r308_relation_web_anatomy.py \
  --n 128 --p 59649589127497217 --top 10
```

Outputs:

```text
scripts/probes/_out_466_r308_n128_c3_danger.txt
scripts/probes/_out_466_r308_n128_c4_harmless.txt
scripts/probes/_out_466_r308_n64_c3_danger.txt
```

## Dangerous `c=3` anatomy

For `n = 128`, `p = 1716841910146256242328924544641` (the large prime factor of `3^64+1`,
`β = 14.348`), the power table has:

```text
g^21 = 3,  g^85 = -3,  g^43 = -3^-1,  g^107 = 3^-1.
```

The exact excess is:

```text
excess = 971520 = 1.326923 * headroom.
```

The whole collision web has only three delta levels:

```text
delta=3054 count=128   mass=390912
delta=90   count=256   mass=23040
delta=36   count=15488 mass=557568
```

These sum to:

```text
971520 = 60 * 128^2 - 90 * 128.
```

The largest fibers follow a rigid three-vector pattern.  A typical fiber is:

```text
cnt=381  vec={0: -1}
cnt=3    vec={0: 2, 21: -1}
cnt=1    vec={43: 3}
```

Since `381 = 3n - 3`, its delta is

```text
2 * ((3n-3)*3 + (3n-3)*1 + 3*1) = 24n - 18 = 3054.
```

The same histogram formula was checked for the `n=64`, `c=3` high-beta prime from R307:

```text
excess = 240000 = 60 * 64^2 - 90 * 64.
```

So the live theorem-shaped conjecture is:

```text
C3RelationWebExcess:
  for dyadic n and primes where a primitive n-th root satisfies ζ^d = 3
  with the same nondegenerate orbit pattern, the depth-3 excess equals 60n² - 90n.
```

This immediately beats exact-Wick headroom:

```text
60n² - 90n > 45n² - 40n  iff  n > 10/3.
```

Hence this family gives an infinite-looking obstruction template, conditional on the supply of
prime factors `p ≡ 1 (mod n)` of `3^(n/2)+1`.

## Harmless `c=4` contrast

For `n = 128`, `p = 59649589127497217` (a prime factor of `4^64+1`, `β = 7.961`), the power
table has binomial constants:

```text
g^27 = -4,  g^91 = 4,  g^37 = 4^-1,  g^101 = -4^-1.
```

But the exact pushforward has:

```text
excess = 0
collision residues with positive delta = 0.
```

So danger is not "binomial norm divisor" alone.  It is an arithmetic compatibility between the
small-height relation and the support of 3-sum shadow vectors.

## Consequence

The next proof/refutation target is no longer vague "dangerous norm divisors"; it is the precise
`C3RelationWebExcess` formula.  If proved, it gives a clean infinite obstruction template for the
fixed-depth exact-Wick route.  If refuted at larger `n`, the failure mode should reveal exactly
which orbit nondegeneracy assumption breaks.

No prize closure claimed.  This sharpens the dead exact-Wick route and exposes the relation-web
mass object that any good-prime or log-depth workaround must handle.
