# A quadratic interpolation bound at the second prime

Put $n=1073741824$, $d=67108863$, $t=425022954$ and $e=n-t=648718870$. On every injective evaluation domain of length $n$ over a prime field of characteristic $p>2n$, dimension $d+1$, every received pair has at most **1867863086** MCA-bad scalars at $e$ errors. In particular the second prime, whose budget is $2n$, has operational supremum at least **648718871/n**. The established three-head upper endpoint is $715827882/n$. This is a written proof. The numerical checks use [the exact integer probe](../../../scripts/probes/probe_second_prime_quadratic_discriminant.py).

## An interpolant of degree two in the folded value

Fix received rows $u,v$. For each bad scalar $z$ choose a witnessing polynomial $P_z$ of degree at most $d$ with at least $t$ agreements. Its witness prevents the joint pair from agreeing on the whole witness set. Work over the algebraic closure of the prime field, retaining the original scalars. Put $h=2097152$. Seek a nonzero polynomial

$$
Q(X,Y,Z)=a(X,Z)Y^2+b(X,Z)Y+c(X,Z)
$$

with monomials $X^iY^j Z^l$ satisfying $0≤j≤2, i+dj<t, j+l≤ h$. There are $3ht-(3h-2)d$ monomials. The identities $Q(x,u(x)+Zv(x),Z)=0$ for all $n$ domain sites impose at most $n(h+1)$ homogeneous linear constraints. The surplus is 2097150. At any chosen scalar $z$, $Q(X,P_z(X),z)$ has degree less than $t$ and vanishes at $t$ sites. Hence it is identically zero. We only use this last identity below. Any common factor of all coefficients depending on $X$ alone may be divided out, preserving the identities for every $P_z$.

## Quadratic fibers and the Sylvester determinant

First suppose $a≠0$. Write $Δ=b^2-4ac$, of $Z$-degree at most $2h$ and $X$-degree at most $2t-2d-2<p$. The exceptional $z$ for which $a(X,z)$ is the zero polynomial number at most $h$. If $Δ≠0$, unique factorization gives $Δ=s(Z)V(X,Z)^2 H(X,Z)$, with $s$ squarefree and $H$ the product of the distinct odd-multiplicity irreducibles that depend on $X$. Its $X$-squarefreeness over $\overline{\mathbb F}_p(Z)$ follows from Gauss's lemma and the characteristic bound. All three factors are polynomials.

If $r=\deg_X H>0$, the polynomial $S(Z)=\operatorname{Res}_X(H,\partial_X H)$ is nonzero, of degree at most $(2r-1)\deg_Z H$. Discard scalars where $a(X,z)$ or $V(X,z)$ is the zero polynomial, $s(z)=0$, or the $X$-leading coefficient of $H$ vanishes. These cost at most $h+h+2h+2h=6h$, by taking one nonzero coefficient of every nonzero polynomial whose entire specialization vanishes. For any remaining witness,
$$ (2a(X,z)P_z(X)+b(X,z))^2 = Δ(X,z), $$
so $H(X,z)$ is a square up to a nonzero scalar. Its $r$ roots counted with multiplicities occupy at most $r/2$ distinct sites over the algebraic closure. The specialized Sylvester matrix of $H,H_X$ has corank at least $r/2$, since its corank equals the degree of their gcd and $0<r<p$. A polynomial matrix losing rank by $k$ at $z$ has determinant divisible by $(Z-z)^k$: use a constant invertible row operation making $k$ rows zero at $z$, then divide those rows by $Z-z$. Comparison with $\deg S$ gives at most $4\deg_Z H≤8h$ additional witnesses. Thus $16h$ already bounds the entire count in this case.

Otherwise absorb a constant $H$ into the factorization. For $Δ=0$ use $s=1,V=0$. Away from at most $h$ scalars where $a(X,z)$ is identically zero, attach to each chosen witness a $λ$ with
$$ λ^2=s(z),\qquad 2a(X,z)P_z(X)+b(X,z)=λ V(X,z). $$
Such a sign exists by the difference-of-squares identity over a field, including at a zero of $s$. If $s$ is constant there are at most two components, one for each constant sign. If $s$ is nonconstant then $λ^2=s(Z)$ is irreducible over $\overline{\mathbb F}_p(Z)$ and there is a single component. Each selected scalar occurs just once.

## From a component to a secant

Consider a component carrying $M≥e+2$ chosen witnesses. Remove the domain sites where $a(x,Z)$ is identically zero. There are at most $t-2d-1$ of these since a nonzero coefficient of $a$ as a polynomial in $Z$ has that $X$-degree bound. At each surviving site put
$$ F_x(Z)=2a(x,Z)(u(x)+Zv(x))+b(x,Z). $$
Let $U$ consist of those surviving sites where $F_x=λ V(x,Z)$ is an identity on the component. At any other surviving site this equality can hold for at most $2h+2$ of the chosen scalars. For a constant sign the difference is a nonzero polynomial of degree at most $h+1$. In the irreducible case its norm $F_x^2-sV(x,Z)^2$ is nonzero and has degree at most $2h+2$. Actual agreement always implies this equality. Thus
$$ |U|\ge 2d+1-\left\lceil(2h+2)n/M\right\rceil \ge 127275425. $$
At a site of $U$, any chosen witness with $a(x,z)≠0$ actually agrees. As $a(x,Z)$ is nonzero there, the total count of misses across these sites and all $M$ witnesses is at most $hn$. Put $L=8388607$. At most $\lfloor hn/(L+1)\rfloor=268435456$ witnesses miss more than $L$ sites of $U$. Any three of the remaining witnesses agree jointly with their respective folds on more than $d$ common sites, because $127275425-3L>d$. Fix two remaining points $(z,P_z)$ and interpolate a polynomial secant $A+ZB$ through them. The difference between the third polynomial and its secant value has degree at most $d$ and vanishes on these common sites, so the third point belongs to the secant. The chosen two suffice for all remaining points. If there are fewer than three, the same cardinality bound is immediate.

A secant carries at most $e+1$ bad scalars. If its joint core $C={x:(A(x),B(x))=(u(x),v(x))}$ has at least $t-1$ sites, each bad witness needs one fresh agreement outside $C$, where at most one scalar can agree. This gives $n-|C|≤e+1$. If $|C|<t-1$, every scalar on the secant needs at least $t-|C|$ fresh sites, disjoint between scalars, hence their number is at most $1+\lfloor e/(t-|C|)\rfloor$. This proves $M≤e+1+268435456$ on each component, a bound that also covers $M<e+2$. Two components and the generous exceptional allowance $16h$ give 1867863086 bad scalars.

If the interpolant has degree one in $Y$, write it $bY+c$ and divide out any common factors in $X$ alone. If $b(x,Z)$ vanishes identically at a site, $c(x,Z)$ must be nonzero there as a polynomial in $Z$. Then $c(x,z)=0$ for every witness by the polynomial identity, giving at most $h$ witnesses. Otherwise use all sites and let $U$ be those where $b(x,Z)(u(x)+Zv(x))+c(x,Z)$ vanishes identically. At a site outside $U$ there are at most $h+1$ agreeing scalars. At a site of $U$ there are at most $h$ misses. Thus $|U|\ge t-\lceil(h+1)n/M\rceil$ and the same secant argument applies, with one component. An interpolant independent of $Y$ bounds the entire count by $h$ since one of its coefficients in $X$ is nonzero.

The argument uses characteristic $p>2n$ only to ensure that the squarefree derivative and the quadratic discriminant behave as stated. Multiplicity-one interpolation itself works over all fields. For $Y$-degree at least three, a specialized polynomial can have a polynomial root while its discriminant still has odd-multiplicity factors. The quadratic fiber count above does not supply the analogous classification at the last open predecessor.
