# #466 R307 — binomial norm primes force depth-3 exact-Wick failures at very high beta

## Question

R305 closed the `n = 32` depth-3 census and found the largest exact-Wick violator

```text
p = 21523361 = (3^16 + 1) / 2, beta = 4.872,
```

with the collision mechanism `ζ^5 ≡ -3`: a small-height binomial norm divisor.  This raised
the live rescue hypothesis:

```text
BetaFrontierRescue:
  maybe exact Wick fails only below some moderate beta frontier, and high beta makes the
  depth-3 rung safe.
```

R307 stress-tests that rescue directly by factoring `c^(n/2)+1 = Norm(c+ζ)` for larger dyadic
orders and evaluating exact depth-3 excess at the prime factors `p ≡ 1 (mod n)`.

## Probe

New script:

```text
scripts/probes/probe_r307_binomial_norm_depth3.py
```

It reuses the R305 char-zero 3-sum histogram and evaluates the pushforward energy modulo each
candidate prime. Unlike the older fast scanner, it uses sparse Python-integer evaluation, so it
can test norm factors far beyond `int64`.

Commands:

```bash
python3 scripts/probes/probe_r307_binomial_norm_depth3.py --n 64 --c-min 2 --c-max 7
python3 scripts/probes/probe_r307_binomial_norm_depth3.py --n 128 --c-min 2 --c-max 5
```

Outputs:

```text
scripts/probes/_out_466_r307_n64.txt
scripts/probes/_out_466_r307_n128.txt
```

## Results

For `n = 64`, exact-Wick violations persist deep into high beta:

```text
p = 6700417              beta = 3.779   excess/headroom = 5.868
p = 926510094425921      beta = 8.286   excess/headroom = 1.320
```

The beta `8.286` prime is the large factor of `3^32 + 1`.

For `n = 128`, the same mechanism gets stronger:

```text
p = 67280421310721                         beta = 6.562    excess/headroom = 5.934
p = 1716841910146256242328924544641        beta = 14.348   excess/headroom = 1.327
```

The beta `14.348` prime is the large factor of `3^64 + 1`.

Some binomial norm families are harmless at the tested factors:

```text
n=64:  factors from c=4,5,6,7 often have zero or tiny excess at high beta.
n=128: factors from c=4 and c=5 are zero/tiny at high beta.
```

So the invariant is not "any binomial norm divisor is dangerous"; it is a relation-web mass
condition. But the high-beta rescue is decisively false.

## Consequence

The depth-3 exact-Wick input cannot be repaired by any beta cutoff of the form "take
`p ≥ n^B`" with fixed moderate `B`: already at `n = 128`, a small-height norm divisor gives
a violation at beta `14.348`.

The right local object is now:

```text
RelationWebMass(c, n):
  the collision mass induced by ζ^j = -c on the char-zero 3-sum shadow support.
```

A genuine proof route would need either:

1. a deployment-prime/good-prime exclusion theorem avoiding all dangerous relation webs, or
2. a new log-depth argument that tolerates these fixed-depth failures without compounding them
   into the DC-subtracted wall.

No closure claimed. This round kills `BetaFrontierRescue` and strengthens the good-prime
selector route with explicit high-beta counterexamples.
