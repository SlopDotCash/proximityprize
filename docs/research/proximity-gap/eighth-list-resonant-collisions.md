# Contact orders at a singular point and the eighth-rate list

At the first named prime, $n=2^{30}$ and rate $1/8$, agreement $s=273/800$ gives a list of at most $n$ on every injective grid at every positive interleaving width. Safety holds through **707,327,426 errors**. First failure is at least **707,327,427**. The exact named threshold remains open. [Previous slope-count proof](eighth-list-collision-multiplicities.md) · [Exact board](../../../scripts/probes/probe_eighth_resonant_collisions.py)

## A local contact calculation

Consider a primitive plane differential equation $A+B Y'=0$ on a smooth section graph over a field of characteristic zero or $p>d^2$, where every pair of distinct retained graphs has contact order at most $d$. At a common zero $P$ of $A,B$ write $I_P(A,B)$ for their local intersection length. The logarithmic residue row from an anchor has entries proportional to the orders of its differences from the other sections through $P$. Set aside the anchor columns. If $I_P(A,B)\le2$, every sampled anchor through $P$ contributes the same row, with at most one exceptional section whose selection can cost one additional row.

For the proof write $v=f'(x)$ for an attained slope. The vector $(1,v)$ is an eigenvector of the Jacobian of $(B,-A)$ at $P$, by the linear Taylor equation for an invariant graph. Its eigenvalue and the other eigenvalue are
$$
 \lambda=B_X+vB_Y,\qquad \lambda'=-A_Y-vB_Y .
$$
Suppose $f,g$ have the same slope and $h=f-g$ has order $m\ge2$. Subtracting their differential equations and expanding the divided differences of $A,B$ in $Y$ gives
$$
 B(X,f)h'=-\left(\frac{A(X,f)-A(X,g)}{f-g}
             +g'\frac{B(X,f)-B(X,g)}{f-g}\right)h .
$$
The coefficient at order $m$ yields $m\lambda=\lambda'$, including the case $\lambda=0$.

When $I_P=1$ the linear terms of $A,B$ are independent. Thus $\lambda\ne0$ and $\lambda'/\lambda$ determines the integer $m$ uniquely in $[2,d]$. If a second eigenline also had two sections, its contact order $m'$ would give $mm'=1$ in the field, impossible for $2\le m,m'\le d$ under the characteristic assumption. For a scalar Jacobian all slopes have eigenvalue ratio one, so no pair is tangent. For a nonscalar Jacobian there are at most two eigenlines. Hence all tangent pairs lie in one slope class, have the same contact order, and there is at most one section of a different slope when the tangent class is nontrivial. Every anchor in the tangent class has the same residue row.

For $I_P=2$ the determinant is zero. A tangent pair would give $\lambda=\lambda'=0$, since $m$ is nonzero in the field. In coordinates $U=X-x$, $W=Y-f(X)$ the two generators of the intersection ideal may be written as $B(X,f+W)$ and $A(X,f+W)+f'B(X,f+W)=W C(U,W)$. Here $C(0,0)=-\lambda'=0$ and $B(X,f)$ has order at least two since its linear coefficient is $\lambda=0$. Additivity of the plane intersection gives
$$
 I_P(B,WC)=\operatorname{ord}_{U} B(X,f)+I_P(B,C)\ge3 .
$$
The primitive equation ensures these intersection lengths are finite. Thus at length two every pair through the point meets simply.

## Charging the transformed exceptional slopes

Retain $M=n-1000$ sections on one of the large linear factors. With total degree $b=5$ or $6$ write $r=b-1$, $R=d/n$ and $o_x$ for the physical radial orders. Away from the received ordinates, each collision class is a common zero of $A,B$ and consumes its full plane intersection length. At a received point, each exceptional tangent class has a residual differential equation after blowing up. The excess over the tangent $4o_x-7$ pays its full local intersection length as well.

Indeed, for $o\ge2$ with a nonzero initial pair $(-V_0L,UL)$ of degree $o-1$, put $V_0=Uz$ and divide by $U^{o-1}$ to obtain $A_1,B_1$. Write $A_1+zB_1=U D_1$. At each realized zero of $L(1,z)$ the residual section $z$ solves $D_1+B_1z'=0$. In the transform the intersection of $A_1,B_1$ splits into the multiplicity of $L(1,z)$ there and the full intersection of $D_1,B_1$. Counting the initial $(o-1)^2$ and all projective roots of $L$ reserves $o^2-o-1\ge4o-7$. [Both blow-up charts](quarter-list-darboux-cofactors.md#exceptional-collision-classes)

When both initial forms vanish, or when $o=1$, divide instead by $U^o$ and denote the resulting transforms by $A_1,B_1$. The residual equation is $C+UB_1z'=0$, where $C=A_1+zB_1$. The polynomial $C(0,z)$ is nonzero by the exact radial order and has degree at most $o+1$. At each realized slope $v$ its residual charge is
$$
 I_v(C,UB_1)=\operatorname{ord}_v C(0,z)+I_v(A_1,B_1).
$$
Summed over finite slopes this is at most $o+1+I_P(A,B)-o^2$. To see the last comparison when the original multiplicities differ, at least one equals $o$. The other transform retains its extra power of $U$, whose intersections with the first transform are bounded by $o$ per power over all tangent directions. The strict-transform intersection formula gives the stated estimate. Therefore at least $o^2-o-1\ge4o-7$ remains. At $o=0$ no pair can share the received ordinate because its slope equation is either inconsistent or regular. The bound accommodates this site as well. At a physical exceptional slope the original order of a pair difference is one plus that of the transformed pair; the first unit is already counted in the common true-hit row. All transformed graphs are polynomials of degree at most $d$, so the local contact calculation still applies.

## Cofactor rank and the named comparison

Give each class $C$ weight $w_C=1$ at local intersection length at most two, and weight $w_C=3$ at larger length. The plane budget just proved gives $\sum w_C\le nJ$. Each exceptional class consumes an additional pair multiplicity, so its frequency $q_C$ satisfies
$$
 n^{-1}\sum_Cq_C^2\le R+(1+J)/M-\mu^2 ,
$$
where $\mu\ge s$ is the actual true-hit mean. Write $F_r(u)=1-(1-u)^r$. Under independent anchor sampling a low-length class needs at most $F_r(q_C)+r/M$ expected rows by the local lemma. A high-length class needs at most $rq_C$. The true-hit rows contribute at most $nF_r(\mu)$. Sampling without replacement adds at most $\binom r2/M$ per union event, of which there are at most $n(1+J)$. [Residue rows of the polynomial cofactors](quarter-list-darboux-cofactors.md#rank-of-the-polynomial-cofactors)

Choose positive constants $a,c$ so that $F_r(q)\le a+cq^2$ on $[0,1]$ and $12ac\ge r^2$. The latter gives $rq\le3a+cq^2$. The rank is at most
$$
 r+1+n\left[F_r(\mu)+aJ+c\bigl(R+(1+J)/M-\mu^2\bigr)
       +\frac{\binom r2(1+J)+rJ}{M}\right].
$$
The certificate proves the first inequality from a tangent to $F_r$ and a quadratic discriminant. It also checks $F_r'(s)\le2cs$, so the expression is largest at $\mu=s$.

| Total degree $b$ | $J$ | $a$ | $c$ | Rank at most | Nullity at least | First-integral degree at most |
|---:|---:|---:|---:|---:|---:|---:|
| 5 | $0.395$ | $0.288$ | $8.45$ | 1,071,251,124 | 2,489,700 | 431 |
| 6 | $0.162$ | $0.516$ | $4.05$ | 1,067,472,642 | 6,268,182 | 171 |

Apply the quartic primary and the degree-two, three and four adaptive product tests of the previous proof at $s=273/800$. Ordinary comparison excludes linear weights above degree six. Degree-five cases without a squarefree quartic denominator fit the budget by normalized pole counting. Partition each remaining degree band into 96 weight intervals. On a squarefree quartic interval either the discriminant excludes the factor or each exterior word individually, or the same plane comparison as for degree six applies. In the individual-exclusion case the absolute bound is $5+8d=n-3$ for isolated sections; the integral-family bound also fits. In each surviving plane case the mean-order test certifies both the displayed $J$ and the variance comparison excluding 1000 exterior words. The resulting cofactor nullities exceed the tame bounds for completely split fibers with moving branch values, and the Riccati bound excludes stationary branch values. The proof uses these written geometric results and the finite arithmetic verifier. [Discriminant and exterior words](eighth-list-coupled-cofactor.md) · [Primitive first integrals](quarter-list-darboux-cofactors.md#from-cofactor-relations-to-completely-split-fibers)

```sh
python3 scripts/probes/probe_eighth_resonant_collisions.py
```
