# Sixteenth-rate list safety from a second jet interpolant

At the second named prime, every closed Reed–Solomon ball of **805,531,368 errors** at length $n=2^{30}$ and rate $1/16$ contains at most $2n$ words. The first failure therefore occurs at or after **805,531,369 errors**. This applies to any injective grid and every positive interleaving width. The proof uses the local rank from hidden-derivative interpolation a second time, after restricting to an irreducible differential equation containing candidate words. [Exact finite certificate](../../../scripts/probes/probe_sixteenth_list_quotient_jets.py) · [First-order interpolation of Dao, Kominers and Thaler](https://eprint.iacr.org/2026/2056)

Put $d=n/16-1$, $t=n/4-225000$, $s=t/n$ and $R=d/n$. Identify interleaved words with scalar polynomials over a common finite extension and pass to the algebraic closure $k$. Give $X,Y,V$ weights $1,d,d-1$. Write $N(w,h)$ for the number of monomials of weight strictly less than $w$ and $V$-degree at most $h$. The weight of a product is the sum of weights. [Scalar extension](../../../ArkLib/Research/ProximityGap/Frontier/ListScalarExtension.lean)

## The local quotient

At a received point $(x,y)$ use the substitution
$$
 X=x+u,\qquad Y=y+uz,\qquad V=z+uw .
$$
For an actual polynomial word $f$ hitting the point, $z=(f(x+u)-y)/u$ and $w=z'$. Write $o_x(F)$ for the order in $u$ of the substitution before specializing $z,w$. It is additive on nonzero products. The dimension of the space of local images modulo $u^r$ at $V$-degree $\le h$ is
$$
 C(r,h)=(h+1)r(r+1)/2-
 \sum_{b=0}^{r-1}(2b+1-r)_+(b+h+1-r)_+ .
$$
Set $C(r,h)=0$ for $r\le0$. To see the formula, expand $u^i(Y-y)^jV^k$ and group by $b=i+j$ and $a=j+k$. The rows of a block are indexed by $0\le l<r-b$ with coefficients $\binom{k}{l}$, multiplying $u^{b+l}z^{a-l}w^l$. Allowed $k$ form a consecutive interval. The rank is the smaller of its size and $r-b$, by the Vandermonde determinant, in the stated large characteristic. Summing these truncated diagonal lengths gives $C$. The same count is implemented in the [canonical local-rank definitions](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/RoundedCounts.lean).

Suppose an irreducible polynomial $g$ of positive $V$-degree $v$ and weight $D_g$ contains a group of words, meaning $g(X,f,f')=0$ identically for every word in the group. For a second unknown polynomial $H$ of $V$-degree at most $h$ impose at each received point that its local image modulo $u^r$ belongs to the image of multiples of $g$, with local multipliers of $V$-degree at most $h-v$. Multiplication embeds the entire local image space of order $r-o_x(g)$ and that derivative-degree cap: its kernel before truncation is precisely the functions of order at least $r-o_x(g)$ by additivity. Consequently the number of linear conditions at the point is at most
$$
                  C(r,h)-C(r-o_x(g),h-v).
$$
When the word actually solves $g$, its local $H$-evaluation has a zero of order at least $r$ at an agreement. If $H$ has weight below $rt$, it vanishes identically on every group member with $t$ agreements. Global multiples of $g$ in the source have dimension $N(rt-D_g,h-v)$ by additivity of the two degree bounds. Thus a strict inequality
$$
 N(rt,h)-N(rt-D_g,h-v)>
 \sum_x [C(r,h)-C(r-o_x(g),h-v)]                                      \tag{1}
$$
produces such an $H$ coprime to $g$ over $k(X)$. Affine Bézout then bounds the number of group members by the product of the total degrees in $(Y,V)$ of $H$ and $g$, since distinct words give distinct jet points over $k(X)$.

## Bounding the mean contact order

Applying the ordinary local constraints with $r=5,h=2$ gives a nonzero primary interpolant of weight at most $5t-1$ with surplus 674,073,128. Factor it in $k[X,Y,V]$. Its total degree in $Y,V$ is at most 19. Factors not involving $V$ together contain at most 19 words, since each nonconstant factor in $Y$ has at most its degree many roots over $k(X)$, and factors in $X$ only contain none. There are at most two factors of positive $V$-degree. Consider a group of at least $n-100$ words on one such factor. The other group sizes will be covered directly by the final cap.

The polynomial $g_V$ is nonzero and coprime to $g$ over $k(X)$, since $v$ is 1 or 2 in the named characteristic. Discard the at most $19^2$ exceptional words on both. The retained size $M$ exceeds $M_0=n-1000$. Choose exactly $t$ hits for each retained word and let $c_x$ count them at each site. Distinct words share at most $d$ hits, so
$$
 \frac1n\sum_x(c_x/M-s)^2\le\sigma^2=R-s^2+(s-R)/M_0.
$$
The local substitution converts differentiation with respect to $V$ into $u^{-1}\partial_w$. Hence $g_V(X,f,f')$, of degree at most $D_g-d+1$ and nonzero on each retained word, has multiplicity at least $o_x(g)-1$ at each of its chosen hits. This gives $\sum_x c_x o_x(g)\le M(t+D_g-d+1)$.

At each site $g(x,Y,V)$ is nonzero, since otherwise $X-x$ divides $g$. Choose a nonzero coefficient of $(Y-y)^j V^k$ in this specialization. The corresponding block with $b=j$, $a=j+k$ in the local expansion has a nonzero column coefficient. Its at most $v+1$ columns are separated by their first $v+1$ binomial rows. Consequently $0\le o_x(g)\le j+v\le D_g/d+v$. This bound includes all points where the full derivative line lies on the surface. The variance of numbers in an interval of length $D_g/d+v$ is at most one quarter of its squared length. Cauchy–Schwarz in the preceding weighted sum now gives the uniform bound
$$
 \frac1n\sum_x o_x(g)\le U(D_g,v)
 =1+\frac{D_g-d+1}{t}+\frac{D_g/d+v}{2s}\sigma .                       \tag{2}
$$

## The two finite exclusions

Use $r=2500$. For $v=1$ take $h=1975$ and for $v=2$ take $h=625$. Put $J=C(r,h-v)-C(r-1,h-v)$. The finite verifier checks every required successive increment up to the primary local-order bound $19+v$, giving
$$
 C(r,h)-C(r-o_x(g),h-v)\le C(r,h)-C(r,h-v)+J o_x(g).
$$
Substitute the mean from (2) into (1). As a function of the unknown weight $D_g$, its lower bound on the surplus is concave: $N(rt-D_g,h-v)$ is a sum of positive parts of affine functions of $D_g$, and $U(D_g,v)$ is affine. Checking the endpoints therefore suffices. The arithmetic uses a rational upper bound on $\sigma$ rounded up to a multiple of $10^{-9}$.

| $v$ | Lower weight | Upper weight | Lower-end surplus, rounded down | Upper-end surplus, rounded down |
|---:|---:|---:|---:|---:|
| 1 | $9n/16-15$ | $5t-1$ | 22,264,566,186,843 | 2,732,977,875,336,257 |
| 2 | $2(d-1)$ | $5t-1$ | 547,943,952,596,483 | 691,774,511,456,737 |

In both rows the Bézout product is below $M_0$, contradicting the group size. Thus a large group can lie only on a linear differential factor of weight $D_g<9n/16-15$.

## Counting the remaining linear factors

Write $g=A(X,Y)+B(X,Y)V$ and $E=D_g-d+1$. The coefficients $A,B$ are coprime over $k(X)[Y]$, so $B(X,f)$ is nonzero for every solution. Put $L=B\partial_X-A\partial_Y$ and $\delta=L/B$ on $k(X,Y)$. The operator $L$ increases weight by at most $E-1$. Writing $\delta^k Y=P_k/B^{2k-1}$ gives
$$
 P_1=-A,\qquad P_{k+1}=B L(P_k)-(2k-1)P_k L(B).
$$
Induction gives weighted degree $\le D_g+d(2E-1)$ for $P_{d+1}$. Every polynomial solution of degree at most $d$ is a root of $P_{d+1}$ in $Y$ over $k(X)$. If it is nonzero their number is at most $2E+\lfloor D_g/d\rfloor-1\le1,073,741,805$. This also bounds any group smaller than $n-100$.

If $P_{d+1}=0$, choose an initial $x_0$ outside the poles and the zeros of $B(X,f)$ of the finite list, and with $B(x_0,Y)\ne0$. For the generic initial value $z$ the regular equation has a unique truncated solution over $k(z)$ up to order $p-1$, by power-series recursion using the unit $B(x_0,z)$. Its derivatives at the initial point are the specializations of $\delta^jY$. All derivatives of orders $d+1$ through $p-1$ vanish. Truncating at degree $d$ therefore gives a polynomial $f_z(X)$ whose substitution in $g$ vanishes modulo $(X-x_0)^{p-1}$. It vanishes identically because its degree is at most $D_g<p-1$. The same construction specializes at every chosen initial value.

Over $k(X)$ the rational map $z\mapsto f_z(X)$ has a left inverse given by $\sum_{j=0}^d (x_0-X)^j\delta^jY/j!$, since the Taylor expansion of a degree-$d$ polynomial is exact. Thus generic evaluation has degree one in $z$. At any physical site evaluation is either degree at most one or constant: take a least common denominator in $k[z]$ for the Taylor coefficients. For each of its roots some coefficient of the numerator polynomial in $X$ remains nonzero there, so no such factor cancels over $k(X)$. Generic degree one therefore bounds both degrees in $z$ of this fixed denominator and numerator. The denominator is nonzero at every selected initial value. At most $d$ sites are constant, by comparing any two distinct word polynomials, so $Mt\le dM+n-d$. This gives a smaller bound than the isolated count.

Finally, twice the isolated cap plus the 19 possible words on $V$-independent factors is smaller than $2n+1$. The primary interpolant therefore excludes an over-budget list. The result is a written proof with exact finite arithmetic; the complete first failing error count remains open.
