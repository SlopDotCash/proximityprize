# Second-prime quarter-rate list safety at 61/125 agreement

At rate $1/4$ and length $n=2^{30}$, every word on any injective grid of the second named field has at most $2n$ codewords at **549,755,813 errors**, at every positive interleaving width. The first failure is therefore at least **549,755,814**. Relative agreement $61/125$ suffices. This extends the order-twelve cubic result by **1,948,641** errors. The named failure witness is at 771,741,384 errors, and the exact first failure remains open. [Cubic pivot and pole-degree argument](quarter-list-second-darboux.md) · [Exact finite certificate](../../../scripts/probes/probe_quarter_second_quartic_darboux.py) · [Failure witness](quarter-locator-reweighting.md)

Use $d=n/4-1$, $t=\lceil61n/125\rceil$ and weights $1,d,d-1$. The primary has order eleven, derivative cap four, weight cutoff $P=11t$, total degree cap $b=21$, and positive surplus **590,560,315**. Scalarize as usual. Set $L=\lfloor n/40\rfloor$ and take the squarefree product of primary factors with at least $L$ assigned solutions. Relative to the cubic proof, derivative degree four now occurs and the small groups cost at most $4L+b$ words.

Write $D$ for the product weight and $v$ for its derivative degree. The following six rows use the joint adaptive quotient. The columns $r,h,\lambda$ give its order, derivative cap and occupancy slope. The constants $b_2,j_2$ bound the two local curvature terms, and $k$ is the number of equal subintervals used for the occupancy variance. For each row the checker tests every local integer multiplicity and both ends of the displayed weight interval using the same data. It verifies the eligible population separately for every large factor. The least surplus over all rows is **157,830,852,005,691**. [Adaptive product proof and notation](joint-list-contact-boards.md#products-of-derivative-degree-two-or-three)

| $v$ | Weight interval | $r$ | $h$ | $\lambda$ | $b_2$ | $j_2$ | $k$ |
|---:|---|---:|---:|---:|---:|---:|---:|
| 3 | $[3(d-1),P-1]$ | 2000 | 500 | 3600 | 4.868 | .071 | 12 |
| 4 | $[4(d-1),P-1]$ | 2000 | 500 | 3600 | 6.493 | .071 | 12 |
| 2 | $[6d-2,7d-2]$ | 10000 | 2500 | 18000 | 3.242 | .073 | 80 |
| 2 | $[7d-2,8d-2]$ | 10000 | 3000 | 17500 | 3.065 | .104 | 80 |
| 2 | $[8d-2,12d-2]$ | 10000 | 3500 | 17000 | 2.892 | .142 | 80 |
| 2 | $[12d-2,P-1]$ | 2000 | 1300 | 3200 | 1.795 | .351 | 80 |

For a derivative-quadratic product below $6d-2$, write $a$ for the ordinate degree of the coefficient of $V^2$. If the leading coefficient in that ordinate has $X$-order $j$ at a site, its radial block gives $o\le a+j+\min(j,2)\le a+2j$. Since the coefficient has degree at most $D-2(d-1)-ad$, the mean radial order obeys
$$
           \mathbb E o\le a+2[D-2(d-1)-ad]/n .
$$
The bound increases with $a$ because $2d<n$. On the integer interval $[(2+i)d-2,(3+i)d-3]$ it therefore suffices to use $a=i$, for $i=0,1,2,3$. The uniform order-6000 quotient gives a strictly larger mean-order lower bound on each interval, with a constant derivative cap chosen for both endpoints. The mixed Bézout bound is below the retained population in each group. This excludes every remaining product of derivative degree two. [Leading coefficient block proof](quarter-list-darboux-cofactors.md#reduction-to-a-rational-differential-equation)

An oversized list would now imply one rational factor $A+B V$ containing at least $M=2n-4L-b=2040109447$ words. The order-3000 uniform quotient excludes $D\ge6d-1$. The normalized differential-curve count handles total degree at most four even after restoring $4L+b$ words. For total degree five use the four-anchor cofactor proof across $5(d-1)\le D\le6d-2$. The order-20000 tests certify at most $0.53n$ exceptional collision classes. They give cofactor rank at most **1,347,093,591** and nullity at least **693,015,856**. The descended first integral has ordinate degree at most two. Its vector field has at most two poles counted with multiplicity, whereas the degree-five equation requires at least three. This closes the second named budget. The proof in this case uses the differential descent and the pole count on the ordinate projective line. [Cofactor rank and degree-five contradiction](quarter-list-second-darboux.md) · [Differential descent](quarter-list-darboux-cofactors.md#from-cofactor-relations-to-completely-split-fibers)

```sh
python3 scripts/probes/probe_quarter_second_quartic_darboux.py
```
