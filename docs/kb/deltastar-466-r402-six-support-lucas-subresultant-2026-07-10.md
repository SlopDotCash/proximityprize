# Issue #466 R402: six-support Lucas/subresultant obstruction

R402 proves the exact structural bridge for the diagonal normalization `c=2`: six distinct pair
supports produce six distinct products `s`, and every product satisfies

```text
s^n = 1
pairLucas(s,n) = 2.
```

Distinctness is kernel-checked from R397's theorem that, at fixed sum, equal products imply equal
unordered supports. Thus a six-support fiber forces the degree-five subresultant of
`X^n-1` and `P_n(X)-2` to vanish modulo the characteristic.

## Exact factor audit

SymPy's integer subresultant PRS gives complete degree-five-content factorizations at the two hostile
dyadic rungs:

```text
n=128:
  2^981 * 17^6 * 43^4 * 127^4 * 131^4 * 193^12 * 257^54
  * 641^18 * 769^12 * 1153^2 * 1409^8

n=256:
  2^2251 * 17^6 * 193^12 * 257^246 * 641^18 * 769^76
  * 1153^2 * 1409^8 * 3329^10 * 7681^2
```

Every prime factor congruent to `1 mod n` is below `n^4` in both rows. The large primes that refute
the lower-support cutoffs do not divide this content:

```text
n=128: 9430378268417 does not divide degree-five content
n=256: 67280421310721 does not divide degree-five content
```

An exact FLINT-backed integer PRS extends the audit to `n=512` (degree-five content: 10,202 bits).
Its complete factorization has distinct prime factors

```text
2, 17, 193, 257, 641, 769, 1153, 1409, 3329, 7681, 10753, 11777,
12289, 13313, 15361, 17921, 18433, 19457, 23041, 25601, 26113,
39937, 59393, 65537.
```

Every factor congruent to `1 mod 512` is at most `65537 < 512^2`, hence far below `512^4`.
Thus all three audited rungs `n=128,256,512` satisfy the stronger empirical law that every
admissible degree-five-content prime is below `n^2`.

Therefore the six-support obstruction is absent in these diagonal cells whenever `p>n^4`. This is
finite exact evidence, not yet a uniform-in-`n` factor theorem and not a proof for non-diagonal
targets. The next arithmetic target is to explain the observed `p<n^2` factor law for the
degree-five subresultant content.
