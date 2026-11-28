# Individual exterior words and the first-prime eighth-rate list

At length $n=2^{30}$, agreement on $t=\lceil137n/400\rceil$ coordinates leaves at most $n$ codewords of the first named eighth-rate code. This holds on every injective grid and at every positive interleaving width. The closed error count **705,985,249** is safe, so the first failing count is at least **705,985,250**. This raises the previous lower endpoint by 536,871. The exact first failing count remains open. [Earlier low-rate bounds](low-rate-named-adaptive-cofactors.md) · [Exact certificate](../../../scripts/probes/probe_eighth_coupled_cofactor.py)

Write $d=n/8-1$, $R=d/n$ and $s=137/400$. Scalarize an oversized list as in the preceding proof. Use a primary interpolant of order nine and derivative degree at most four. Group factors with at least $L=\lfloor n/25\rfloor$ assigned words. The adaptive order-2000 boards exclude their product at all weights $D\ge\max(3,v)(d-1)$ for derivative degree $v=2,3,4$. A surviving degree-two product has total degree at most two. Its normalized curve count plus $2L$ and the derivative-independent words fits $n$. The small-only case fits as well. For a single large linear factor $g=A+B V$, the ordinary quotient excludes $D\ge7d-1$. At total degree at most five, except when $B$ is squarefree of degree four, the population is bounded by the larger of $5+7d$ and $(n-d)/(t-d)$. This leaves room for $3L$ and the derivative-independent words. The checker verifies those budget comparisons. [Product and low-degree population bounds](low-rate-named-adaptive-cofactors.md#three-budgets-from-degree-bounds) · [Normalized derivative poles](first-order-normalized-curve.md)

## A squarefree quartic excludes each exterior word

Suppose $B$ is a squarefree quartic and $5d-1\le D\le6d-2$. For a physical coordinate $x$ let $o_x$ be the factor's radial order there and let $a_x$ be the vanishing order of $\operatorname{disc}_Y B$. The discriminant is nonzero, has degree at most $6(D-d+1)-12d$, and satisfies $a_x\ge2o_x-3$. Thus
$$
 (2-o_x)_+\le3+a_x-2o_x .
$$
Indeed, $a_x\ge0$ suffices when $o_x$ equals zero or one, and the discriminant order handles $o_x\ge2$. For a certified mean-order floor $Z(D)$ define
$$
 E(D)=\frac32+\frac{6(D-d+1)-12d}{2n}-Z(D).
$$
Summation gives $\sum_x(2-o_x)_+\le2nE(D)$. If $E(D)<0$ the factor is impossible. Otherwise every set of $t$ true hits has total radial order at least $2t-2nE(D)$. For an exterior word $f$, the nonzero polynomial $g(X,f,f')$ has degree at most $D$ and vanishes to the corresponding order at each hit. Hence $2sn-2nE(D)>D$ excludes each exterior word. [Quartic discriminant and local orders](eighth-list-quartic-discriminant.md)

The order-12000 quotient proves one of the two strict inequalities across every one of 64 weight intervals. For each interval it selects a single derivative cap passing the same test at both ends. This suffices because $Z$ is concave in $D$. The squarefree factor now contains every word. Its normalized isolated-section bound is $5+8d=n-3$, and its integral-family bound is $(n-d)/(t-d)<n$. [Isolated and integral cases](first-order-normalized-curve.md)

## Coupling the two cofactor counts

For $6d-1\le D\le7d-2$ use the exterior-word variance argument with $J=77/1000$. The order-20000 board proves either the weight is impossible or the number of exceptional collision classes is at most $nJ$ and fewer than 1000 words lie outside the factor. The 32 weight intervals use the same plane intersection estimate and variance bound $J+1/4$ as before. Fix $M=n-1000$ sections on the factor, let $p_x$ be their true-hit frequency at $x$, and write $\mu=n^{-1}\sum_xp_x\ge s$. For each exceptional class $C$ let $q_C$ be its section frequency. [Exterior-word covariance](low-rate-named-adaptive-cofactors.md#exterior-words-at-the-first-prime-eighth-rate)

A pair of distinct sections pays separately for common true hits and common exceptional classes, with at most $d$ root multiplicities available. Restoring diagonals adds at most $n(1+J)/M$ to the sum of squares. Thus
$$
 \frac1n\sum_C q_C^2\le R+\frac{1+J}{M}-\frac1n\sum_xp_x^2
                  \le R+\frac{1+J}{M}-\mu^2 .
$$
Five anchors determine the cofactor differences. Under uniform sampling without replacement, the expected union fraction of their true hits is at most $1-(1-\mu)^5+10/M$. Their expected number of incidences with exceptional classes is at most $5n\sqrt{J(R+(1+J)/M-\mu^2)}$. Both estimates use the same actual mean $\mu$. [Cofactor evaluation and rank](quarter-list-darboux-cofactors.md#rank-of-the-polynomial-cofactors)

Put $C_0=R+(1+J)/M$. The function $1-(1-u)^5+5\sqrt{J(C_0-u^2)}$ is concave on the feasible interval $s\le u\le\sqrt{C_0}$. Its right derivative at $s$ is nonpositive because $(1-s)^8(C_0-s^2)\le Js^2$. Evaluating the sum at $s$ bounds the cofactor rank by **1,072,473,701** including the six restored dimensions. Its nullity is at least **1,267,123**, and the primitive first integral consequently has ordinate degree $m\le847$. A moving branch label would allow at most $2m+5+72m$ completely split constant fibers. The nullity forces more. With all branch values stationary, the Riccati bound excludes $M$ sections. The named characteristic satisfies the separability and tame-cover requirements. This gives the stated all-center bound. The proof uses the written tame-cover and scalarization results. The verifier checks the finite interpolation and population inequalities. [Split fibers and good reduction](quarter-list-darboux-cofactors.md#moving-branch-values)

```sh
python3 scripts/probes/probe_eighth_coupled_cofactor.py
```
