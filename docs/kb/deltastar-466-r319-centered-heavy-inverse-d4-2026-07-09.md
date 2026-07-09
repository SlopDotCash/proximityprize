# R319 Centered Heavy-Inverse Stress at Depth Four

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Why the original wording needed repair

R317 informally said that heavy collision mass should force a small rational
resonance.  The depth-4 census is the strongest available falsifier: at `n=32`
there are 92 arithmetically generic in-window primes called `K-bad`, and none
has a reduced resonance `a/b in mu_n` with `1 <= a,b <= 4`.

However, `K-bad` in that census means

```text
A_4 > 1.05 * E_4^char0,
```

not that `A_4` exceeds the real-Gaussian Wick ceiling `105*n^4`.  The prize
normalization must first subtract the DC mean and then spend the positive
char-zero headroom.

## Exact normalization

Write

```text
E_4(p) = E_4^char0 + W_4,
A_4 = E_4(p) - n^8/p,
H_4 = 105*n^4 - E_4^char0.
```

Then the exact Wick condition is equivalent to

```text
W_4 - n^8/p <= H_4.
```

For `n=32`, the constants are

```text
E_4^char0 = 90889120,
105*n^4   = 110100480,
H_4       = 19211360.
```

`probe_r319_centered_heavy_inverse_d4.py` parses all 92 K-bad rows.  The worst
centered cell is `p=1439393`:

```text
A_4 / (105*n^4) = 0.9274594,
(W_4 - n^8/p) / H_4 = 0.5842693.
```

Thus all 92 generic, nonresonant wraparound examples remain safely below the
actual Wick ceiling.  They refute "all sizable wraparound is resonant" but do
not refute a super-Wick inverse theorem.

## Corrected conjecture

The prize-facing statement must use a fixed exponential threshold, not exact
Wick at every shallow rung:

```text
CenteredHeavyInverse(K):
  A_r > K^r * (2r-1)!! * n^r
  => the heavy shadow-collision component has a low-complexity stabilizer.
```

The stabilizer need not always be a single rational binomial; depth four shows
that generic isolated relations are abundant.  The intended dichotomy is:

```text
isolated/noncoherent components <= K^r Wick,
coherent component => stabilizer => transfer-matrix bound <= K_res^r Wick.
```

This is a weighted inverse theorem for the collision hypergraph.  R318 shows
the known coherent `c=3` component fits the second branch with tiny effective
constant.  R319 shows the generic depth-4 components fit the first branch.

## Status

Conjecture-grade.  The strongest available generic depth-4 falsifier does not
break the centered formulation.  No prize closure is claimed.
