---
id: deltastar-466-g287-canonical-quadratic-kernel-nogo-2026-07-13
issue: 466
tags: [proximity-gap, delta-star, CORE, weighted-kernel, quadratic, Farkas, no-go]
date: 2026-07-13
author: Sol
status: landed
supersedes: []
---

# G287: canonical linear and quadratic weighted-kernel features are sign-infeasible

## One-line

Reflection parity kills every odd statistic on the even sponsor cone without using linearity, and an
exact positive Farkas circuit kills the first surviving even nonlinear class: no homogeneous
quadratic in the complete generator-independent kernel features `(T2,T4,T8,T16)` tracks the CORE
sign on the genuine `n=16` rank-five/rank-six census.

## Why this is the correct next class

G285 introduces the row-labelled kernel decomposition

```text
W_G(t) = sum_{u in G} 1_{(2-u)G}(t),
H_j = sum_{t in (2-zeta^j)G} R_r(t).
```

Changing the generator `zeta -> zeta^s`, `s in (Z/n)^*`, acts on the input Fourier basis by Galois
permutation. At `n=16`, the complete generator-independent nonprincipal linear basis is the
Ramanujan family

```text
T(H) = (T2,T4,T8,T16),
T_d(H) = p * sum_j c_d(j) H_j.
```

G285 records `T2` and `T4/2`; G287 closes the full four-dimensional span. G286 then observes that
the actual centered sponsor profiles are fixed by value reflection. The fixed-point argument is
not linear:

```text
sigma(c)=c and F(sigma(v))=-F(v)  =>  F(c)=0
```

for every function `F : V -> Q`. Thus no reflection-odd quadratic or higher statistic survives.
The smallest corrected nonlinear class is reflection-even and homogeneous quadratic:

```text
Q_a(T) = sum_{d<=e} a_(d,e) T_d T_e,
```

with ten monomials.

## Exact linear closure

Five genuine cells form a positive circuit in the four gate-signed primitive feature vectors. The
cells are

```text
(p,r)=(113,6),(1889,6),(2129,6),(2593,5),(2593,6).
```

After division by the positive row gcd, their feature vectors are

```text
(1,4,-6,-12),
(10545,23232,53984,113160),
(655,4782,15455,15128),
(4451,10468,16700,49928),
(5977,15129,22602,72588).
```

Their CORE signs are `(-,-,+,+,-)`. The positive integer Farkas weights

```text
(201509006170048, 579259743381, 520097612828,
 4174444248727, 2109973613412)
```

combine the four signed coordinates to zero exactly. Therefore no fixed real/rational linear
combination of the complete canonical basis has the gate sign on all five cells. This upgrades
G285 from the two low-order normals to the full generator-independent linear surface.

## Exact quadratic closure

The probe evaluates all 84 cells with `n=16`, `p<2600`, `p=1 mod 16`, and `r in {5,6}`. It uses the
ten monomials

```text
T2^2, T2*T4, T2*T8, T2*T16, T4^2,
T4*T8, T4*T16, T8^2, T8*T16, T16^2.
```

The L1-normalized max-margin LP has optimum zero. The proof-of-record is exact: eleven cells, all
with `p>=113`, give a rank-ten signed feature matrix whose one-dimensional nullspace has strictly
positive coordinates. The witness cells are

```text
(113,5),(241,6),(337,6),(353,5),(449,5),(769,5),
(977,6),(1217,5),(1249,6),(1777,6),(2273,6).
```

After dividing each linear feature vector by its positive gcd, the positive integer dependence is
checked coordinatewise in Lean and Python. By Farkas separation, if a coefficient vector `a` made
every signed value `sign(A_r) Q_a(T)` positive, its positive weighted sum would be positive. Exact
linearity makes that same sum zero, contradiction. Hence no homogeneous quadratic in the complete
canonical feature vector tracks all eleven gates.

The use of primitive row vectors is exact: if `T=gU`, `g>0`, then `Q(T)=g^2 Q(U)`, so every
quadratic sign is unchanged.

## Asymptotics and literature integration

G285's Jacobi expansion writes each `T_d` as a full `m=(p-1)/n`-term Jacobi average on a twisted
character coset. A quadratic feature `T_d T_e` therefore expands into an `m^2`-term product family.
Classical Weil purity bounds each nonexceptional Jacobi factor by `sqrt(p)`, so each product has
magnitude at most `p`; it supplies neither the relative sign between the two character cosets nor a
comparison to the untwisted CORE factor. The quadratic lift increases fanout from `m` to `m^2`
without reducing the signed family.

This matches the established large-sieve/fanout results G228-G247: half recovery of the untwisted
sponsor factor already needs coefficient mass `(m-n)/(4n)`, namely `2^96`/`2^97`, and no bounded
coordinate or coherent eigensubfamily carries the sign. Taking ten invariant quadratic coordinates
does not change that binding inequality. The exact positive circuit is the finite shadow: even the
entire degree-two invariant ring piece is sign-infeasible before any asymptotic estimate is applied.

FS15-FS18 remain fully consumed. They control fixed-depth, almost-all-prime Wick/resultant windows;
G64/G262 force the rank-six sponsor outside that window. Neither the linear nor quadratic kernel
feature lift selects either sponsor prime or supplies the missing Archimedean full-family sign.

## Formal payload and scope

`Frontier/_G287CanonicalQuadraticKernelNoGo.lean` proves:

- arbitrary reflection-odd statistics vanish on reflection-fixed profiles;
- a reusable positive-circuit/Farkas no-separator theorem;
- the exact five-cell linear relation and full canonical linear no-go;
- the exact eleven-cell quadratic relation and homogeneous quadratic no-go.

The computation of record is
`scripts/probes/g287_canonical_quadratic_kernel_nogo.py`.

Closed: every reflection-odd statistic at any degree, the complete generator-independent linear
kernel-input span at `n=16`, and its full homogeneous quadratic extension on the exact census.

Not closed: cubic or non-polynomial reflection-even statistics, or the full sponsor-labelled
Jacobi covariance itself. A higher-degree polynomial fitted to finite gate labels is not a mechanism;
it would still need an independently specified arithmetic coefficient rule and a production-prime
margin. CORE remains OPEN / ON-BGK.
