# Interpolating along received lines on a fixed component

Let $k$ be an algebraically closed field, $D\subset k$ consist of $n$ distinct evaluation sites, and $F\in k[X,Z,Y]$ be primitive over $k[X]$ and irreducible in $k(X)[Z,Y]$. Write $b=\deg_Y F\ge1$ and $m=\deg_{Z,Y}F$. Take $M$ distinct labels $z\in k$, a degree-at-most-$d$ polynomial $q_z\in k[X]$ for each, and assume $F(X,z,q_z(X))=0$. Each $q_z$ agrees at $t$ or more sites with the received line $L_x(z)=u(x)+zv(x)$.

At $x\in D$, expand $F(x+\epsilon,Z,L_x(Z)+w)$ in $\epsilon,w$ over $k[Z]$. Let $\ell_x$ be the smallest total degree of a nonzero term over $k(Z)$. Primitivity over $k[X]$ implies $F(x,Z,Y)\ne0$, so $0\le\ell_x\le b$. Choose one lowest-degree pivot using graded lexicographic order, with coefficient $a_x(Z)\ne0$ of degree at most $m$.

## Finite bound

Take integers $\mu\ge b$, $0\le E<t$, and $s\ge0$. Put $t'=t-E$, $B_\mu=\binom{\mu+1}{2}$. Suppose $\mu t'>(b-1)d$. A family as above cannot satisfy both inequalities
\[
\begin{split}
 (s+1)\bigl(b\mu t'-\tbinom b2d\bigr)&>
 \bigl(s+b+m B_\mu\bigr)\sum_{x\in D}
 \bigl(\mu\ell_x-\tbinom{\ell_x}{2}\bigr),\\
 M-\left\lfloor\frac{mn}{E+1}\right\rfloor&> b s+(b-1)m .
\end{split}
\]
This test includes singularities of the plane fibers and scalars where a local pivot vanishes.

Seek $R(X,Z,Y)$ on the monomials $Z^iY^jX^a$ with $0\le i\le s$, $0\le j<b$ and $a+jd<\mu t'$. Their number is the left side of the first inequality. At site $x$, work in $V=k(Z)[\epsilon,w]/(\epsilon,w)^\mu$. Require the class of $R$ to belong to $FV$. A basis of $FV$ consists of the translates $\epsilon^i w^j F$ with $i+j<\mu-\ell_x$. Their lowest terms are distinct in the chosen monomial order. They span since all other translates have order at least $\mu$. The number of independent restrictions in $k(Z)$ is therefore $B_\mu-\binom{\mu-\ell_x+1}{2}=\mu\ell_x-\binom{\ell_x}{2}$.

To count actual constraints over $k$, use the square pivot minor on those distinct leading monomials. Order the columns by their leading monomials; the minor is triangular with determinant a power of $a_x$. Every column entry has $Z$-degree at most $m$. The truncated entries of $R(x+\epsilon,Z,L_x+w)$ have $Z$-degree at most $s+b-1$. One determinant per nonpivot row tests membership. Each has $Z$-degree at most $s+b-1+mB_\mu$ and depends linearly on the coefficients of $R$. Requiring all these polynomials to vanish costs at most the right side of the first inequality. Thus a nonzero $R$ exists.

For a scalar with $a_x(z)\ne0$, the pivot minor remains invertible after specialization, so the truncated class of $R$ is a multiple of $F$ also over $k$. An agreement at $x$ then implies $(X-x)^\mu\mid R(X,z,q_z(X))$, upon substituting $w=q_z(X)-L_x(z)$ and $\epsilon=X-x$. Across all sites at most $mn$ scalar-site pairs have zero pivot. At most $\lfloor mn/(E+1)\rfloor$ scalars can lose more than $E$ agreements. Each remaining scalar yields at least $\mu t'$ roots with multiplicity, while $\deg_X R(X,z,q_z(X))<\mu t'$. Thus its specialization vanishes identically.

Finally $R$ is coprime to $F$ over $k(X,Z)$ because it is nonzero and has smaller $Y$-degree. The $Y$-resultant is a nonzero polynomial in $Z$ of degree at most $b s+(b-1)m$ over $k(X)$. All the remaining scalar labels are its distinct roots, contradicting the second inequality.

The test improves when the interpolation polynomial has low multiplicity at the received lines. A repeated factor in an affine specialization alone does not determine $\ell_x$: its definition uses both local variables. Numerical applications must bound the sum of these two-variable multiplicities.

## The second prime at 677602242 errors

Set $n=1073741824$, $d=67108863$, $t=396139582$ and $e=n-t$. Suppose $2n+1$ distinct bad scalars have been selected. We prove a contradiction. As in the [moving-cubic proof](second-prime-moving-cubic.md), let $D_v(h,T)=\sum_{j=0}^{\min(h,v)}(h-j+1)\max(0,T-jd)$ count the monomials of total $(Z,Y)$-degree at most $h$, value-degree at most $v$, and coordinate weight less than $T$.

There is a degree-13 interpolant of value degree at most three, because $D_3(13,t)-14n=76973154>0$. It must contain a factor $F$ irreducible over $k(X)$ of value degree three. Indeed the low-degree component argument in the [progress ledger](PROGRESS.md) bounds each nonlinear quadratic by 4128 labels and each nonlinear value-linear component by 184 at the smaller agreement count 357913943 and degree allowance 34. Here these bounds still apply: the linear-factor proof uses only the lower bound on agreements, and for a quadratic the singular-leading-coefficient loss is at most $t-2d-1$ so its ordinary identity-site bound $2d+1-O(34n/M)$ is unchanged. At most three heads contribute at most $3(e+1)$, and adding $3\cdot4128+13$ stays below $2n$. A cubic factor therefore carries at least $M=2n+1-13$ selected points. A second interpolant exists by $D_5(7,t)-8n=120595519>0$. Bézout forces $F$ to divide it, hence $m=\deg_{Z,Y}F\le7$. If $m=5$, all factors remaining in the degree-13 cubic interpolant are independent of $Y$ and give at most eight other scalar labels. The moving-cubic bound now gives $21+32d+8<2n$. At $m\le4$ it gives a smaller total. The identically zero derivative case gives a head or a small component by the same inverse-Taylor proof. It remains to consider $m=6$ or $7$.

Let $W$ be the largest $X$-weight plus $d$ times the $Y$-exponent of a monomial of $F$. All ordinary interpolation polynomials counted by $D_5(10000,t)$ have total degree at most 10000, so every member of their kernel is divisible by $F$, since $M>10000\cdot7$. The kernel has dimension at least $D_5(10000,t)-10001n=2962672586458$. If $W\ge230220154$, the quotient has total degree at most 9994, value-degree at most two and weight below $t-230220154$. Its dimension is at most $D_2(9994,t-230220154)=2962672577556$. The difference of 8902 forces $W\le230220153$.

For a general irreducible component of value degree $b$, the reverse second derivative numerator
\[
 N=F_{ZZ}F_Y^2-2F_{ZY}F_YF_Z+F_{YY}F_Z^2
\]
has weight at most $3W-2d$ and value-degree at most $3b-2$. If it vanishes on $F$, the inverse-Taylor argument in the scalar variable gives $y=c_0+c_1 Z$ with $c_i$ algebraic over $k(X)$. The numerator and denominator representing $c_0,c_1$ have scalar and value degrees at most $m+1$, and the characteristic exceeds their minimal-polynomial height bounds. The conjugate affine lines each carry at most one $k(X)$-rational selected point unless they descend to $k(X)$, contradicting $b=3$. Otherwise the weighted resultant bounds the total intersection multiplicity by $H=(6b-2)W-3b^2d$. Translation by $L_x(Z)$ preserves the numerator since $L_x''=0$. At an identity site it vanishes to local order at least $3\ell_x-2$. Local plane intersection multiplicity is at least the product of the two orders. Therefore $7\sum_x\ell_x\le6n+H$, using $\ell(3\ell-2)\ge7\ell-6$. The [quartic proof](second-prime-quartic-intrinsic.md) gives the details of the local resultant argument.

For $b=3$, this bounds $\sum\ell_x$ by $1187719155$. Since $\binom{\ell}{2}\ge\ell-1$ for positive $\ell$, the total jet codimension at $\mu=160$ is at most $189921087469$. Apply the finite bound above with $s=700000000$, $E=256$, $m\le7$. There are $132961885113645549891$ coefficients and at most $132961885083309467447$ constraints. At least $2118237741$ labels survive the exceptional pivots. Their number exceeds the resultant degree bound $2100000014$. This excludes the remaining cubic.

Thus the rate-sixteenth first bad error count at the second prime is at least **677602243**. The safe-count calculation uses the prime field only through the previous characteristic bounds and its budget $2n$. It applies to every injective evaluation domain at these parameters. The unconditional upper count **715827882** comes from the separate three-core construction on the named smooth domain. The incidence and geometric argument here is written mathematics. [Kernel-checked numerical comparison](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeIntrinsicArithmetic.lean)

## A uniform bound at rate one sixteenth with a linear field budget

For **every** multiple $N$ of 16 with $N\ge2^{30}$, every prime $p>2N$, and any injective $N$-point evaluation domain, the degree-$d=N/16-1$ code has at most $2N$ bad scalars at $5N/8$ errors. In particular $p\ge 2^{129}N$ suffices for 128-bit MCA security at this closed radius. Put $t=3N/8$. The cubic interpolant with $(h,b)=(13,3)$ has surplus at least $3N/8$ by using $d\le N/16$ in the coefficient count.

Here are the uniform low-degree estimates needed to force an irreducible cubic factor. Every affine head carries at most $5N/8+1$ labels. A nonlinear factor of value degree one and total degree at most 13 carrying at least 1000 points would have an identity set of size $U\ge(1000t-13N)/(1000-13)$. At every identity site at most 13 labels can miss. The 14 least-missing points each miss at most $13U/(1000-13)$ identity sites. Every triple thus has more than $d$ joint agreement sites, forcing these 14 points onto a secant, contrary to the factor degree. For value degree two, use the [square-discriminant argument](second-prime-quadratic-discriminant.md) with $h=13$. The moving squarefree case costs at most 208 labels since the $X$-degree of the discriminant is less than $p$. In the remaining case there are at most 13 leading-coefficient exceptions and two parameter components. On a component with at least 1000 labels the ordinary identity-site count is at least
\[
 U\ge 2d+1-28N/1000 .
\]
This follows by losing at most $t-2d-1$ identically zero leading-coefficient sites and by double counting at the other sites. At any identity site at most 13 labels can miss. The 14 least-missing points each miss at most $13U/(1000-13)$, giving more than $d$ common agreements for every triple and the same forbidden secant. Hence each nonlinear factor contributes at most 2013 labels. At most three heads, three such extra bounds, and 13 vertical labels together give less than $2N$. A hypothetical $2N+1$ family must therefore place at least $2N+1-13$ points on one irreducible cubic $F$, with $m\le13$.

All $(h,v)=(10000,5)$ interpolants are divisible by $F$ since $2N+1-13>130000$. If its weight were $W\ge41N/192$, its quotients would have total degree at most 9997, value-degree at most two and weight below $t-41N/192$. In the dimension comparison substitute $N/16$ for $d$ to lower-bound the source. In the quotient this substitution decreases the upper count by at most $29989$, the sum of $j(9998-j)$ for $j=0,1,2$. The resulting source lower bound minus quotient upper bound is at least $9929N/64-29989>0$. Thus $W<41N/192$. The reverse derivative argument gives
\[
 \sum_x\ell_x\le (6N+16W-27d)/7 < 53N/48+4.
\]
Its zero-derivative case uses a scalar-degree bound below $2\cdot3(13+1)+3<p$.

In the finite jet inequality use $\mu=64$, $s=10000000$, $E=256$, $m=13$. The source minus the equation bound is at least
\[
 \frac{458273591}{48}N -(s+1)49152-256(s+3+13\cdot2080)>0.
\]
The surviving labels number at least $2N+1-13-13N/257>3s+26$. The resulting contradiction proves the bound. The proof uses no cancellation estimate and holds on arbitrary injective prime-field domains. An exact threshold at an individual field would additionally require a matching bad instance or a stronger safe count.

## The other three prize rates at the same linear field budget

For every multiple $N$ of 32 with $N\ge2^{30}$ and every prime $p>2N$, the four rates $1/2,1/4,1/8,1/16$ on arbitrary injective domains have bad-scalar count at most $2N$ at the respective **closed radii**
\[
 \frac14,\qquad\frac{13}{32},\qquad\frac{17}{32},\qquad\frac58 .
\]
Thus $p\ge2^{129}N$ suffices for 128-bit security at all four radii. The half-rate case follows from the [general apolar endpoint](../../../ArkLib/Research/ProximityGap/Frontier/ApolarPowerBound.lean): for $k=N/2$, $e=N/4$ and $N=k+2e$, the numerator is at most $(e+1)\lfloor (N+1)/(e+1)\rfloor\le N+1$. The rate-sixteenth proof is above.

For rate $1/4$ take $t=19N/32$, $d=N/4-1$. For rate $1/8$ take $t=15N/32$, $d=N/8-1$. Both have $t-d=11N/32+1$. With $h=32$ the quadratic interpolant has coefficient surplus $3h(t-d)+2d-(h+1)N=96+2d>0$. An irreducible quadratic with a moving odd part in its discriminant carries at most $16h=512$ labels. The characteristic is greater than the discriminant's coordinate degree. Otherwise separate the two sign components as in the [quadratic proof](second-prime-quadratic-discriminant.md). A group of at least 4096 labels has at least $U=2d+1-66N/4096$ ordinary identity sites. At any one of them at most 32 labels can miss. The 33 least-missing labels on the group each miss at most $32|U'|/(4096-32)$ sites of the actual identity set $U'$ of size at least $U$. Every triple shares more than $d$ sites since $(1-96/4064)U>d$ in both cases. The 33 points therefore lie on a secant, exceeding the factor's total degree of 32. The nonlinear quadratic contributes at most $2\cdot4095+32$ labels.

For a nonlinear value-linear factor, first remove common $X$-content from its coefficients. At a site where the restriction to the received line vanishes identically the leading coefficient is then a nonzero parameter polynomial of degree at most 32. With 4096 or more witnesses the identity set has size at least $(4096t-32N)/(4096-32)$, and again the 33 least-missing points have every triple on more than $d$ common sites. A value-linear factor with two or more collinear witnesses that is an affine line contributes at most $e+1$ by the fresh-site bound. Counting at most two such heads, two nonlinear component allowances and 32 vertical labels leaves $2(e+1)+2(2\cdot4095+32)+32<2N$ in both rows. The assertions here give uniform safe radii; the tests for an exact first bad count require a corresponding failure construction.
