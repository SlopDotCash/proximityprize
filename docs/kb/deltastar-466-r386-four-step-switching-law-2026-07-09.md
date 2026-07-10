# Issue #466 R386: four-step switching law

Date: 2026-07-09

## Exact discovery

`scripts/probes/probe_r386_four_step_switching.py` computes the fourfold representation function

```text
rep4(c) = #{(x1,x2,x3,x4) in mu_n^4 : x1+x2+x3+x4=c}.
```

At every tested prize-shaped cell, the maximum over `c != 0` is exactly

```text
max rep4(c) = 12*n - 24.
```

The law survives generic and structured primes:

```text
n=8:  max=72
n=16: max=168
n=32: max=360
n=64: max=744
```

The number of maximizing targets is `n*(n/2-1)`, exactly the number of non-antipodal unordered
pair-sum orbits. This identifies the mechanism: a target with reduced core `{a,b}` receives all
ordered insertions of one antipodal pair `{x,-x}`, with degeneracies subtracting `24` from the
generic `12n` count.

## Switching interpretation

Replacing four walk steps has forward degree about `n^4`. For a nonzero adjustment, reverse degree
is at most `12n-24`, giving expansion of order `n^3`. More generally, replacing `2s` steps should
have a characteristic-zero diagonal reverse fiber of order `n^(s-1)`, hence expansion `n^(s+1)`.
This can be tuned to the field aspect ratio.

## Remaining obstacle

A constant-factor raw mixing bound does not control the prize object: the DC term is enormous and
must cancel with coefficient one. The required next theorem is therefore not merely
`rep4(c) <= 12n`; it is a signed switching identity that separates the exact diagonal/DC flow from
the off-diagonal remainder and bounds only that remainder at Wick scale.

The finite-field equality `max rep4(c)=12n-24` is probe evidence, not yet a Lean theorem. Small
hostile fields violate it, so any theorem needs an explicit prize-regime or no-extra-fiber guard.

## Exhaustive-prime falsification (2026-07-09)

An exhaustive sweep of every prime `p < 200000` with `n | p-1` shows that a simple density guard
such as `p > n^3` does **not** imply the sharp law.  For example,

```text
n=32, p=194977 (> 5*n^3): max rep4(c)=836 > 360=12*n-24.
```

Exceptions persist to `p=41521` for `n=16` and throughout the searched range for `n=32`.
Thus exact characteristic-zero transfer is the wrong finite-field target.  On the other hand, all
searched exceptions remain far below R390's coarse `105n` envelope.  The live route is now:

1. prove a coarse finite-characteristic `O(n)` nonzero-fiber envelope in the prize range; and
2. use it only inside a DC-centered variance/switching identity, since raw pointwise domination
   cannot pay the Wick budget.
