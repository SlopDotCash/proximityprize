# R342: Difference-quotient walk audit

## Proposed solving hypothesis

Starting from the exact pointwise identity

```
|S_b|^2 - n = sum_{r in H, r != 1} S_{b(r-1)},
```

put the classes `(r-1)H` in the quotient group `F_p^*/H`.  A tempting route is
that the resulting walk mixes after the critical depth

```
k = ceil(log_{n-1}((p-1)/n)).
```

Critical-depth `L2` flatness would imply a square-root bound for every
nontrivial quotient-character eigenvalue.  Combined with a suitable logarithmic
Sobolev inequality for the nonlinear fixed point, this would yield the desired
subgaussian maximum.

## Exact obstruction

The walk does not have `n-1` independent generators.  Inversion forces

```
r^-1 - 1 = (-r^-1)(r-1).
```

For dyadic `H`, both `r` and `-1` lie in `H`, so `(r^-1-1)H=(r-1)H`.
Except for `r=-1`, generators are paired.  The identity and subgroup-membership
statement are formalized in `_R342DifferenceQuotientWalkNoGo.lean`.

## Probe results

`scripts/probes/probe_r342_difference_quotient_walk.py` computes exact quotient
convolution counts.  `L2/unif` is `m sum_x mu(x)^2`; uniform measure has value 1.

At the nominal critical depth:

| `(p,n,m)` | depth | support / `m` | `L2/unif` | `Linf/unif` |
|---|---:|---:|---:|---:|
| `(521,8,65)` | 3 | `18/65` | 4.81 | 9.10 |
| `(100049,8,12506)` | 5 | `46/12506` | 512 | 833 |
| `(1048609,16,65538)` | 5 | `610/65538` | 224 | 663 |
| `(16777601,32,524300)` | 4 | `3479/524300` | 213 | 1090 |

Even at depth 12, the last cell has `L2/unif = 2.44` and
`Linf/unif = 20.17`; the `n=8,p=100049` cell occupies only 235 of 12506 classes.
Thus the literal critical-depth mixing conjecture is false by large factors.

## Surviving target

The only plausible version is asymptotic and must explicitly price permutation
collisions and inversion pairing:

```
E_k^x(H-1) = #{r,s in (H\{1})^k : product(r_i-1)/(s_i-1) in H}
             <= C_k (n-1)^(2k) / m,
```

at a depth `k` large enough that the uniform term dominates the forced diagonal
strata.  This is a high-dimensional shifted-subgroup multiplicative-energy
problem, not free random-walk mixing.  Moreover, eigenvalue square-root bounds
alone do not control the period `L-infinity` norm; a log-Sobolev or nonlinear
hypercontractive bridge remains necessary.  R342 therefore refutes the direct
walk shortcut but leaves a sharply stated two-part research route.
