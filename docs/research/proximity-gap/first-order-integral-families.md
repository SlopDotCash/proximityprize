# Counting integral families and isolated sections of a first-order equation

At the four radii below, the list budget needed at length $n=2^{30}$ is at most **89, 59, 35 and 22 times $n$**, respectively, on every injective grid at every positive width in sufficiently large characteristic. The numerical examples have literal 128-bit budgets equal to those four bounds. The two designated benchmark primes have budgets $n$ and $2n$, so these four examples are different inputs to the prize. The comparison column uses the same four radii. [Previous finite bounds](carbon-list-tight-first-order.md) · [Exact slot, degree and primality checks](../../../scripts/probes/probe_first_order_integral_families.py)

| Rate | Safe errors | Previous list bound | New list bound | Integers $(r,b,v)$ |
|---:|---:|---:|---:|---:|
| $1/2$ | 318,504,960 | $407n$ | $89n$ | $(13,18,3)$ |
| $1/4$ | 547,618,816 | $341n$ | $59n$ | $(12,23,3)$ |
| $1/8$ | 706,478,080 | $263n$ | $35n$ | $(10,27,3)$ |
| $1/16$ | 816,840,704 | $222n$ | $22n$ | $(7,25,4)$ |

The first-order interpolation and the existence of a linear list bound a constant distance beyond Johnson are established results. Here the additional calculation bounds the number of words on an entire family by its generic evaluation degree and subtracts the forced intersection at infinity when counting isolated sections. The local rank, derivative recurrence and their geometric antecedents are described in the existing theory. [Dao, Kominers and Thaler](https://eprint.iacr.org/2026/2056) · [Gabizon](https://eprint.iacr.org/2026/2048) · [Canonical first-order rank](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/RoundedCounts.lean) · [Taylor chart](hidden-derivative-agreement-cuts.md)

## The finite bound

Let $d=k-1\ge1$, $n\ge t>d$, and take positive integers $r,b,v$ with $v\le b$. Work in characteristic zero or characteristic $p>\max(rt+1,b,d+1)$. Suppose the number of triples $(i,j,h)$ of nonnegative integers satisfying
$$
 j+h\le b,\quad h\le v,\quad i+dj+(d-1)h<rt
$$
exceeds $n$ times the local cost
$$
 C(r,v)=\sum_{s=0}^{r-1}\sum_{q=0}^{s+v}
 \min\{r-s,\min(s,q)-\max(0,q-v)+1\}.
$$
Then every closed ball requiring $t$ agreements contains at most
$$
  2bv-v^2+d(4bv-b-2v^2-v)+b+
  \frac{bv(n-d)}{t-d}                                             \tag{1}
$$
words. The final term permits up to $b$ different families each of evaluation degree $v$. All terms are independent of field size and interleaving width. A column of any finite width embeds linearly over the base into its rational function extension, preserving all agreements and degrees.

Use a nonzero polynomial $F(X,Z,V)$ supported on the indicated triples. At a site $(x,y)$ set $X=x+u$, $Z=y+uz$, $V=z+uw$. Require the coefficients of $u$ of order below $r$ to vanish identically in $z,w$. For a translated monomial $u^i(uz)^j(z+uw)^h$ put $s=i+j$ and $q=j+h$. Its surviving rows are indexed by $0\le l<r-s$ from $u^{s+l}z^{q-l}w^l$. At fixed $s,q$ there are at most $\min(s,q)-\max(0,q-v)+1$ choices for $j$ and at most $r-s$ rows. Translation does not increase the cap on $h$. Summing the resulting rank bounds proves existence by the strict dimension surplus. For any word $f$ agreeing at a site write $f(x+u)=y+uz(u)$. Substituting $w=z'(u)$ shows $F(X,f,f')$ has order at least $r$ there. Its degree is below $rt$, so $t$ agreements force the polynomial identity.

## Isolated solutions

Factor $F$ over the algebraic closure of the scalar field, removing content in $X$. Each word solves one of the factors. Write $g$ for a primitive irreducible factor, $B$ for its total degree in $(Z,V)$, and $v_0$ for its $V$-degree. If $v_0=0$ it has at most $B$ distinct roots over the rational function field $K=k(X)$. Otherwise let $T=g_V$ and $A=-g_X-Vg_Z$. On the curve $g=0$ the derivation extending $d/dX$ has $\partial Z=V$, $\partial V=A/T$ wherever $T\ne0$. The positive $V$-degree is smaller than the characteristic, so $g,T$ are coprime.

For $j\ge1$ write $\partial^j Z=P_j/T^{2(j-1)}$, starting with $P_1=V$. In passing from $P=P_j$ to $P_{j+1}$ a valid numerator is
$$
 T^2(P_X+VP_Z)+TAP_V-2(j-1)P\,[T(T_X+VT_Z)+AT_V].
$$
Its total degree increases by at most $2B-2$, and its $V$-degree by at most $2v_0-1$. In particular $P_{d+1}$ has respective caps $D=1+2d(B-1)$ and $w=1+d(2v_0-1)$. Every polynomial solution with $T(X,f,f')\ne0$ makes $P_{d+1}=0$ since its degree is at most $d$.

For any polynomial $P$ coprime to $g$, with total degree $D'$ and $V$-degree $w'$, the number of their common affine points over an algebraic closure of $K$ is at most
$$
 v_0D'+(B-v_0)w'.
$$
In the projective plane with coordinates $[Z:V:H]$, the point $[0:1:0]$ has multiplicities at least $B-v_0$ and $D'-w'$ on the two homogenized curves. Their local intersection multiplicity is at least the product when both multiplicities are positive. Subtract from the total Bézout count $BD'$. The displayed upper bound is increasing in either degree cap, including when the actual degree drops. Coprime plane polynomials acquire no common component under field extension.

If $g\nmid P_{d+1}$ apply this bound both to $P_{d+1}$ and to $T$, whose degrees are at most $B-1$ and $v_0-1$. Distinct words give distinct affine points over $K$. Including the solutions with $T=0$, this counts at most
$$
 C(B,v_0,d)=2Bv_0-v_0^2+d(4Bv_0-B-2v_0^2-v_0)
$$
solutions. The same bound more than covers the singular solutions on a component where $g\mid P_{d+1}$.

## Entire families of polynomial solutions

Suppose $g\mid P_{d+1}$ and take a transcendental initial coordinate $\xi$ over $k$. Use constants $k'=\overline{k(\xi)}$ with respect to the independent variable $X$. An original polynomial solution regular over $K$ specializes to a point $(z,w)=(f(\xi),f'(\xi))$ with nonzero $T(\xi,z,w)$. Consider an irreducible component $C$ of $g(\xi,z,w)=0$ carrying such a point. At its generic point take the Taylor polynomial $f$ of degree at most $d$ with the derivatives prescribed by the rational recurrence, evaluated at $(\xi,z,w)$. All these coefficients are regular wherever $T(\xi,z,w)\ne0$, and $f(\xi)=z$, $f'(\xi)=w$.

This $f$ satisfies $g(X,f,f')=0$ identically. To see this in positive characteristic choose $N=rt+1<p$. On the localized differential ring $k[X,Z,V,T^{-1}]/(g)$, the truncated exponential $a\mapsto\sum_{j=0}^{N-1}\partial^j(a)u^j/j!$ is multiplicative modulo $u^N$ by Leibniz's rule. Evaluate its coefficients at the generic initial point. It sends $X$ to $\xi+u$, and sends $Z,V$ to $f(\xi+u),f'(\xi+u)$ modulo $u^N$, since $\partial^{d+1}Z$ and all its derivatives vanish in that ring. Thus the equation holds modulo $u^N$. The substitution has degree below $rt$ by additivity of weighted degree on factors of $F$. It holds as a polynomial identity. The same truncation works in characteristic zero. The rational recurrence recovers every original regular polynomial solution from its initial point by ordinary Taylor reconstruction.

On the smooth projective model of $C$ over $k'$, consider the rational function $f(X)$ with independent parameter $X$. We have
$$
 k'(C)(X)=k'(X)(f(X),f'(X)).
$$
Indeed $T(X,f,f')$ is nonzero by its value at $X=\xi$. The recurrence under the derivation fixing all coefficients of $f$ recovers all further derivatives in the right-hand field. Taylor expansion from $X$ back to $\xi$ recovers $z,w$. These generate the function field of $C$. In particular $f(X)$ is nonconstant as a function on $C$ over $k'(X)$: if algebraic over $k'(X)$, then $f'(X)$ would also be algebraic since the equation in $V$ has a simple root there. The displayed field has transcendence degree one over $k'(X)$. Thus $g(X,f,V)$ is a nonzero polynomial in $V$, and the generic map $f(X)$ has degree at most $v_0$ by the field equality.

For each place of $C$, the generic pole order of $f(X)$ is the maximum pole order of its polynomial coefficients, with zero allowed. The leading polar coefficients cannot cancel as a polynomial in the independent $X$. The total of these maxima is the generic degree just bounded. Every specialization $f(x)$ at a physical site that is nonconstant on $C$ therefore has degree at most $v_0$. At most $v_0$ regular initial points can map to the received value there. If a specialization is constant and agrees with the received word, count it as a common site. There are at most $d$ common sites: otherwise all polynomials in the family coincide by interpolation. Equivalently, $d+1$ constant specializations make all coefficients constant by Vandermonde inversion. For $c$ common sites and $M$ retained words, $M(t-c)\le (n-c)v_0$, giving $M\le v_0(n-d)/(t-d)$. Passing to the smooth model covers singular initial points as well, since the initial Taylor coefficients are regular on the chart and every closed point has a preimage on the normalization.

There are at most $B$ initial components and their total contribution is bounded by $Bv_0(n-d)/(t-d)$. Finally the $C(B,v_0,d)$ terms are superadditive in the bidegrees with $1\le v_0\le B$: expanding a sum of two degree pairs gives nonnegative cross terms. The function is increasing in both bounds within this range. Sum over the irreducible factors, charging the ordinate-only factors by their degrees, to get (1).

## The four benchmark-length examples

In the order of the table let $(c,h,a)$ be $(89,4,11),(59,10,5),(35,11,3),(22,89,5)$. Take $p=c\,2^{158}+h\,2^{100}+1$. Each has budget $\lfloor p/2^{128}\rfloor=cn$ and exceeds $rt+1$. The verifier checks $a^{(p-1)/2}\equiv -1\pmod p$. Consequently for each prime divisor $l$ of $p$, the order of $a$ modulo $l$ has the full $2$-part of $p-1$, in particular $2^{100}\mid l-1$. As $(2^{100}+1)^2>p$, each $p$ is prime. The same certificate gives the generator $a^{(p-1)/n}$ of the order-$n$ subgroup. Exact finite surpluses are 70,779,660, 203,424,974, 68,159,102 and 41,944,885. The geometric counting argument is written. Lean checks the mixed degree charge, its superadditivity, and all four finite slot and list comparisons against the canonical first-order rank count. [Kernel-checked comparisons](../../../ArkLib/Research/ProximityGap/Frontier/FirstOrderIntegralFamilyCounts.lean) The verifier also checks finite examples of evaluating a two-sheeted polynomial family. [Executable certificate](../../../scripts/probes/probe_first_order_integral_families.py)
