# Issue #466 R396: simultaneous cyclotomic Bezout certificate

Date: 2026-07-10

R396 formalizes the correct arithmetic certificate for R395. If

```text
A*f + B*g + C*Phi_n = D
```

in `Z[X]`, then any common root of `Phi_n,f,g` modulo a prime `p` forces `p | D`. Consequently a
certificate with `0 < |D| < p` excludes the three-support simultaneous collision.

This works with the simultaneous ideal and therefore distinguishes common-root-at-one-embedding
from the false condition that `p` merely divides both separate norms at potentially different
embeddings. The remaining arithmetic task is constructive: for every three disjoint dyadic pair
supports, produce such a certificate with `|D| < p` in the quartic regime.

## Smith-normal-form evidence

Represent multiplication by the two folded collision polynomials on
`Z[X]/(X^(n/2)+1)` and compute the Smith form of the combined matrix `[M_f | M_g]`. Its largest
invariant factor annihilates the quotient and supplies a simultaneous Bezout constant. On measured
`n=64` six-root cells the Smith form is usually cyclic:

```text
p=204353: index=408706=2p
p=48449:  index in {96898,387592}={2p,8p}
p=7937:   index=15874=2p
p=1217:   index=2434=2p
p=65537:  index=131074=2p
```

An adversarial check refuted the stronger claim that the full ideal **index** is always at most
`n^4`: one disjoint triple at `n=64` has index `23686148 > n^4`, with nontrivial invariant factors
`[2,11843074]`. Crucially the largest invariant factor, and hence the available annihilator, is
`11843074 < n^4`. A further 1000-triple random sweep had maximum annihilator `386` at `n=64`.
However, a targeted obstruction at `n=64, p=11127041` has quotient exponent
`2*193*11127041 > n^4`, refuting a uniform annihilator-size bound as well.

The corrected arithmetic target is prime-factor selective:

```text
q prime, q == 1 (mod n), q divides the simultaneous obstruction  =>  q <= n^4.
```

for three disjoint pair supports (including the five-root diagonal case). R396's exact
`no_common_root_of_not_dvd` consumes this statement: a primitive `n`-th root requires
`p == 1 (mod n)`, while a common root forces `p` to divide every Bezout constant. This selective
prime-factor bound remains conjectural.

An exhaustive `n=16` census checked all `120120` six-element supports and perfect matchings. The
largest nonzero annihilator was `34 = 2*17`, against `n^4 = 65536`; the `56` zero-annihilator cases
are the characteristic-zero vertical configurations in which all three pairs are antipodal and the
common sum is zero, outside R395's nonzero target.

Complete admissible-prime sweeps support the strict quartic cutoff directly:

```text
n=32, p<4n^4: 12 failures of rep2<=4; last p=32993 < n^4=1048576.
n=64, p<4n^4: last failure p=11127041 < n^4=16777216;
               no failure in [n^4,4n^4].
```

The `n=64` failures above `300000` are `355009, 400321, 421313, 665857, 697601, 11127041`, with
maximum multiplicities `6,6,6,8,8,5` respectively. Together with the earlier lower-prime sweep,
this is exhaustive through `4n^4`, not a random sample.
