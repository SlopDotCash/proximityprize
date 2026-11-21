# Exact two-head window at rate one eighth

Let $16\mid n$, $n\ge2^{30}$, $k=n/8$, $d=k-1$, and take any injective $n$-point Reed–Solomon domain over a finite field of characteristic $p>3n^2$. Define
\[
 t_0=\lfloor(n+3d+4)/3\rfloor+1,\qquad E=n-t_0 .
\]
The worst-case two-row MCA numerator is **exactly $2(e+1)$** for every $7n/16\le e\le E$. Each integer budget $7n/8\le B\le2(E+1)+1$ has first failing error count $\lfloor B/2\rfloor$. At $n=2^{30}$ the exact error interval is **469762048 through 581610154**, and the budget interval reaches **1163220311**. In particular the error interval extends above $n/2$ by 44,739,242 errors. This is a written proof with checked integer inequalities.

## A small cubic

Suppose there are $2(e+1)+1$ distinct bad labels at some $7n/16-1\le e\le E$. Take their chosen polynomial witnesses. Every witness has at least $t=n-e\ge t_0$ agreements. Write $k_0$ for the algebraic closure of the field. The monomials $X^aZ^iY^j$ with $j\le3$, $i+j\le11$ and $a+jd<t_0$ outnumber the $12n$ site-line constraints by $42t_0-58d-12n>0$, since $t_0\ge11n/24$ and $d=n/8-1$. They give an interpolant of total $(Z,Y)$-degree at most 11, value degree at most three and weight below $t_0$ vanishing on every selected point over $k_0(X)$.

Suppose a primitive irreducible cubic-in-$Y$ factor $F$ occurs. Its total degree $m$ in $(Z,Y)$ is at most 11 and its weight $W<t_0\le11n/24+2$. The remaining factors are independent of $Y$ and account for at most 11 labels. Hence $F$ has at least $2(e+1)+1-11\ge7n/8-10$ selected points.

Use the [persistent-polar and finite Jacobian matrix argument](second-prime-terminal-cubic.md). Take $J=W-d$, $s=10000000$, $\mu=16$, $a=16$, and $\eta=\lceil n/16\rceil=n/16$. The value degree is three, so all the local branch and polar formulas there apply. The characteristic bound exceeds all the discriminant and separability degrees. A zero second scalar derivative permits at most three sections by the inverse-derivative bound. Otherwise, let $g$ be the generic polar gcd degree and $R$ the total local multiplicity on received lines.

If $g\ge3J-\eta$, the [local intersection inequality](second-prime-persistent-singularities.md#local-charges-for-the-two-derivatives) gives $5R\le2n+23W-54d+8\eta$, thus $R<126n/100$. For the polynomial jet interpolation,
\[
 (s-1)(3\mu t_0-3d)>(s+1)\mu R+11n\tbinom{\mu+1}{2}.
\]
It suffices to substitute $t_0=11n/24$, $d=n/8$ on the left and $R=126n/100$ on the right. The resulting auxiliary has value degree below three, while its scalar resultant with $F$ has degree at most $3s+16$.

If $g<3J-\eta$, the degree-$a$ Jacobian matrix has parameter height at most $aH$, $H=6m-9\le57$. Its ambient dimension is
\[
 N=(3a+3)a(7W-9d-3)\le(3a+3)a\bigl((77/24-9/8)n+20\bigr).
\]
The sufficient strict surplus $(s+1)(a\eta-3d)>aHN$ follows on replacing $d$ by $n/8$ on the left and using this bound on $N$ on the right. Hence a nonzero auxiliary of weight below $aJ$ and value degree below three vanishes on every simple selected section. At most $11\cdot10$ labels are exceptional, and its nonzero scalar resultant has degree at most $3s+22$. Both cases contradict $7n/8-10>3s+22+110$. No irreducible cubic factor can therefore occur.

## Two large heads contain all selected points

The degree-two factor argument gives at most 4128 selected labels on any irreducible quadratic component. Its parameter degree is at most 11, so using the more generous cap 34 from the [terminal factor count](second-prime-terminal-reduction.md#factors-and-populations) is valid. In particular $2d+1-\lceil70n/2048\rceil$ identity sites, with at most $34$ misses per site on a 2048-label component, still force 35 witnesses with triple intersection greater than $d$. The explicit inequality is $(2014-102)(2d-70n/2048)>2014d$.

An irreducible value-linear component has at most 184 selected points unless it is an affine secant over $k_0(X)$. Indeed, with 185 labels and the actual parameter-degree bound 11, the identity sites $U$ have $(185-11)|U|\ge185t_0-11n$. At most ten labels miss each identity site. Take the twelve with fewest misses: each misses at most $10|U|/(185-11)$ sites. Each triple shares at least $144|U|/174>d$, so all twelve lie on one secant. Restriction to it has scalar degree at most 11 and twelve roots, forcing the secant factor.

There are at most three distinct positive-value-degree factors and at most 11 exceptional labels on parameter-only factors. Any affine secant admits at most $e+1$ labels. If at most one secant had more than $e/3+1$ points, the whole family would have at most
\[
 (e+1)+2(e/3+1)+3\cdot4128+11<2(e+1)+1
\]
labels, a contradiction. Two distinct secants therefore each have occupancy $L>e/3+1$. Their core sizes $c_1,c_2$ are at least $t-2$, since $(L-1)(t-c_i)\le e$ whenever $c_i<t$. The two cores overlap in at most $d$ sites. An outside point agrees on at most $d$ sites of each of them, because it differs as a polynomial from each of the corresponding heads at its scalar. Hence an outside point has at most
\[
 n-(c_1+c_2-d)+2d\le n-2t+3d+4<t
\]
agreements. Consequently the two secants cover every selected point and give at most $2(e+1)$ labels, contrary to the proposed family.

## Attainment and the first failing count

For $7n/16\le e\le E+1$ let $h=\max(0,2(n-e-1)-n)\le k-2$ and choose $h$ common sites with locator $H$. Give heads $(0,0)$ and $(XH,H)$ a private set of $n-e-1-h$ coordinates apiece, in addition to the common sites. Put their corresponding received pairs there. Every private site gives one fresh scalar $-x$ to the opposite head. At each remaining site choose a pair agreeing with the two heads at two new distinct prescribed scalar labels. Solving the two linear equations makes both fresh. The selected labels can avoid $-x$ and all earlier labels because $|\mathbb F|>3n^2$. Each head has $n-e-1\ge k$ defining sites, so only that head could jointly explain its support; the fresh point disagrees in at least one of the two received entries. This gives $2(e+1)$ distinct literal bad labels.

For $e^*=\lfloor B/2\rfloor$ in the stated budget interval, the upper result covers $e^*-1$, including $7n/16-1$, while the attack covers $e^*$, including $E+1$. Hence $2e^*\le B<2(e^*+1)$ gives the first failure and operational real threshold $e^*/n$. The earlier [two-head construction and rate-eighth interval through one half](PROGRESS.md#2026-11-21--general-rate-range-of-the-two-line-argument) use the same fresh-site principle. [Finite and uniform arithmetic certificate](../../../scripts/probes/probe_rate_eighth_two_head_window.py)
