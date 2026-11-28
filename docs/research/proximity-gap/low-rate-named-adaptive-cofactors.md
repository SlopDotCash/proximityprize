# Four low-rate list bounds at the named budgets

At length $n=2^{30}$ the following closed error counts are safe for every received word on the named field, on every injective grid and at every positive interleaving width. Each row raises the first-failure lower bound to the integer in the last column. The exact named thresholds remain open. [Exact four-row certificate](../../../scripts/probes/probe_low_rate_named_adaptive_cofactors.py)

| Field and rate | Required agreement | List budget | Safe errors | First failure at least |
|---|---:|---:|---:|---:|
| First, $1/8$ | $343/1000$ | $n$ | 705,448,378 | 705,448,379 |
| Second, $1/8$ | $17/50$ | $2n$ | 708,669,603 | 708,669,604 |
| First, $1/16$ | $19/80$ | $n$ | 818,728,140 | 818,728,141 |
| Second, $1/16$ | $237/1000$ | $2n$ | 819,265,011 | 819,265,012 |

Write $d$ for the maximum message degree, $s$ for the agreement fraction and $t=\lceil sn\rceil$. Use the scalarization, weights $1,d,d-1$ and common adaptive interpolation for the product of all factors with at least $L$ assigned words. If the primary has derivative cap $c_0$ and the large product has derivative degree $v$, the assigned positive-derivative small groups cost at most $(c_0-v)L$ words. Indeed each small factor uses at least one degree of the primary in its derivative variable. Factors independent of this variable cover at most the primary total degree $b_0$ in additional words. [Common occupancy for all large factors](joint-list-contact-boards.md#products-of-derivative-degree-two-or-three)

## Three budgets from degree bounds

Use a primary of derivative cap four and the following parameters. A product cutoff $c$ means the adaptive quotient excludes every weight $D\ge c(d-1)$ at the specified derivative degree. The linear cutoff $c_1$ means the ordinary order-3000 quotient excludes weights starting at $c_1d-1$. The checker tests both ends of every required interval and uses 80 variance bins on each adaptive row. It records all local curvature constants, caps, orders and occupancy slopes.

| Field and rate | Primary order | $L$ | Product cutoffs for $v=2,3,4$ | $c_1$ |
|---|---:|---:|---:|---:|
| Second, $1/8$ | 9 | $\lfloor n/16\rfloor$ | 4, 3, 4 | 7 |
| First, $1/16$ | 8 | $\lfloor n/13\rfloor$ | 4, 4, 4 | 8 |
| Second, $1/16$ | 8 | $\lfloor n/9\rfloor$ | 7, 5, 4 | 8 |

If $c=v$, the corresponding product is impossible. For $c>v$ its total degree is at most $c-1$. The normalized differential-curve bound summed over these large factors, plus $(4-v)L+b_0$, fits the required budget on each row. A surviving single linear factor has total degree at most $c_1-1$. For its population use the larger of $(c_1-1)+(2c_1-4)d$ and $(n-d)/(t-d)$ and restore $3L+b_0$. The checker verifies these population inequalities together with the primary surpluses, mixed Bézout comparisons and local-order inequalities. This proves the three rows. [Normalized curve counts](first-order-normalized-curve.md) · [Linear coefficient quotient](linear-contact-quotient.md)

## Exterior words at the first-prime eighth rate

Put $s=343/1000$, $L=\lfloor n/40\rfloor$. The primary of order eight and derivative cap three has positive surplus **8,591,214** and $b_0=21$. The adaptive products of derivative degrees two or three are excluded above $3(d-1)$. The remaining quadratic product has total degree at most two. Its normalized curve count and the possible words in the other groups together fit $n$. The ordinary linear quotient excludes weight $D\ge7d-1$.

For $D<6d-1$ the rational equation $g=A+B V$ has total degree at most five. A squarefree quartic denominator requires $D\ge5d-1$. Its discriminant gives $\mathbb E o\le3/2+[6(D-d+1)-12d]/(2n)$. At uniform order 12000 and cap 6000 the quotient threshold is strictly larger at both endpoints $5d-1,6d-2$. For all other denominators the pole count gives at most $5+7d$ isolated sections, or at most $(n-d)/(t-d)$ family sections. Adding $2L+b_0$ fits the first budget. [Quartic discriminant and pole bounds](eighth-list-quartic-discriminant.md)

It remains to exclude $6d-1\le D\le7d-2$. Put $R=d/n$, $K=[5D+6(D-d+1)-30d]/n$, and let $Z$ denote the normalized mean-order floor at quotient order 20000. Plane intersections bound $\mathbb E(o^2-o-1)_+\le K$. They also bound the exceptional collision classes by $n(K+7-4Z)$, with the tangent $4o-7$ paying for the ordinary intersections at each physical site. Partition the weight range into 32 intervals. The checker chooses one cap on both ends to exclude the interval with $K+7-4Z<0$, or to certify $K+7-4Z\le J=53/1000$. In the latter case, writing $\overline o=\mathbb E o\ge Z$, the same plane estimate gives
$$
 \operatorname{Var}(o)\le K+1+\overline o-\overline o^2
 \le J-6+5\overline o-\overline o^2\le J+1/4 .
$$
[Exceptional collision classes](quarter-list-darboux-cofactors.md#exceptional-collision-classes)

An exterior word $f$ is one for which $g(X,f,f')$ is nonzero. Its polynomial has degree at most $D$, so its physical hits, weighted by local orders $o_x$, have total at most $D$. Suppose there are at least 1000 exterior words and take exactly 1000. Crop each agreement set to mass $sn$, allowing one fractional mark. The mean site occupancy $p$ has mean $s$ and variance at most $R-s^2+(s-R)/1000$ by pairwise agreement. Averaging the polynomial degree bound and using Cauchy–Schwarz now gives
$$
       D/n\ge\mathbb E(po)\ge
       sZ-\sqrt{(J+1/4)(R-s^2+(s-R)/1000)} .
$$
The certified cap gives the opposite strict inequality at both endpoints of each remaining interval, which suffices by concavity of $Z$. Thus fewer than 1000 words are exterior. In an oversized list the rational equation would carry at least $M=n-1000$ actual solutions, even if some were originally assigned to other factors.

Use five anchors, as $\deg_Y A\le6$, $\deg_Y B\le5$ and the leading ordinate coefficient of each cofactor is common. With $\mu\le\sqrt{R+1/M}$, the cofactor rank is at most
$$
     6+n\left[1-(1-\mu)^5+10/M+
              5\sqrt{J(R-s^2+(1+J)/M)}\right].
$$
The integer rank bound is **1,058,494,473**. Its nullity is at least **15,246,351**, giving a rational first integral of ordinate degree $m\le70$ with at least 15,246,352 completely split constant fibers. The vector field has at most six poles on the ordinate projective line. If it has a moving branch value, the tame split-fiber bound with at most six moving labels and at most $2m-2$ distinct branch labels permits at most **5,185** completely split constant fibers. With stationary branch values the equation is Riccati, and the constant-cross-ratio count gives fewer than $M$ solutions at the specified agreement. Both alternatives contradict the oversized list. The first-prime eighth-rate proof uses tame-cover good reduction through the cited split-fiber theorem. [Logarithmic cofactors and first-integral descent](quarter-list-darboux-cofactors.md#from-cofactor-relations-to-completely-split-fibers) · [Moving branch and Riccati bounds](quarter-list-darboux-cofactors.md#moving-branch-values)

```sh
python3 scripts/probes/probe_low_rate_named_adaptive_cofactors.py
```
