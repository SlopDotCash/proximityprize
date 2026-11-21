# Paley discrepancy on product strata of the subgroup sumset

Let $H=\langle g\rangle$ have order $n=2^{30}$ in either named prize field,
$\chi$ be its quadratic character extended by zero, and $\epsilon=\chi(g)$.
Put $t_a(i)=g^i+g^{a-i}$ and $T_a=\{t_a(i):i\in\mathbb Z/n\}$. These
sets classify sums of two subgroup elements by the exponent of their product.
The certified fourth-energy floor implies that each nonzero sum has at most
one unordered representation, so it belongs to exactly one stratum of $H+H$.
Two exponents in $T_a$ give the same coordinate exactly when they agree or
sum to $a$ modulo $n$. Even $a$ gives $n/2+1$ points and odd $a$ gives $n/2$.
[Fourth-energy floor](../../../ArkLib/Data/CodingTheory/ProximityGap/SidonEnergyIff.lean) ·
[Lean trace fibers](../../../ArkLib/Research/ProximityGap/Frontier/PaleyInversionTrace.lean)

Write $S(A,B)=\sum_{x\in A,y\in B}\chi(x-y)$. The complete discrepancy of
every stratum follows from the two columns below by
$S(T_{a+2k},T_{a+2k})=\epsilon^kS(T_a,T_a)$.

| Prime | $S(T_0,T_0)$ | $S(T_1,T_1)$ | $(H_0,H_1,H_2,H_3)$ |
| --- | ---: | ---: | --- |
| First | 1,617,901,344 | −65,858,000 | $(9311,1000,-42240,1000)$ |
| Second | 3,686,242,496 | −1,801,854,912 | $(-44849,10208,43408,-10208)$ |

Here $h_j=\chi(g^j-1)$ and $H_c=\sum_{j\equiv c\pmod4}h_j$.
The four one-dimensional class sums were evaluated with GMP, pairing $j$ and
$-j$ via $h_{-j}=\epsilon^j h_j$ and checking each worker's endpoint by
modular powering. Their totals reproduce the independent full rows $-30929$
and $-1441$. The maximum absolute complete discrepancy is below seven times
the size of its stratum at both named primes.
[Exact scan and direct small-field controls](../../../scripts/probes/probe_sponsor_paley_trace.cpp)

## Reduction to four integers

Both primes have $\chi(-1)=1$. Factoring a trace difference gives

$$
\chi(t_a(i)-t_a(j))=\epsilon^{i+a}h_{i-j}h_{i+j-a}.
$$

Indeed for $x,y\ne0$ the difference of $x+s/x$ and $y+s/y$, multiplied
by $x$, is $(x/y-1)(xy-s)$. Taking quadratic characters proves the identity
even at collisions. The image of $(i,j)\mapsto(r,s)=(i-j,i+j)$ consists of
all pairs of the same parity, each with two lifts. For both lifts
$\epsilon^i=\epsilon^{(r+s)/2}$ since $4\mid n$.
Put $E=H_0+\epsilon H_2$ and $O=H_1+\epsilon H_3$.
At $a=0$, splitting the sum by parity gives the complete **multiset** sum
$D_0=2(E^2+\epsilon O^2)$. At $a=1$, the two indices $r,s-1$ have opposite
parity. Writing them as $2u,2v+1$ in either order gives
$\epsilon^{i+1}=\epsilon^{u+v}$, and hence $D_1=4EO$.

Every point in $T_1$ has two lifts, so $S(T_1,T_1)=EO$.
In $T_0$, the two fixed points $2,-2$ have one lift each. The indicator of
the ordinary set is half the sum of its multiplicity function and the
indicator of $\{2,-2\}$. For either endpoint $e$, the character sum
$\sum_i\chi(t_0(i)-e)$ equals $\sum_i\epsilon^i-1$ by
$t_0(i)\mp2=(g^i\mp1)^2/g^i$. The ordered endpoint-pair sum is two. Thus

$$
4S(T_0,T_0)=2(E^2+\epsilon O^2)+4n\mathbf 1_{\epsilon=1}-2.
$$

## Rectangles cut out by exponent intervals

For a fixed product exponent $a$, let $I,J$ be intervals of exponents on
which $t_a$ is separately injective. Put
$K_1=449676$ and $K_2=448831$, the certified bounds on the absolute values
of the complete Fourier coefficients of $h$. Then

$$
|S(t_a(I),t_a(J))|\le 2K^2\big(2+\log(n/2)\big)^2.
$$

At either prime this gives a relative error below $1.19\%$ whenever both
intervals contain at least $2^{27}$ exponents. The same estimate applies to
arithmetic progressions in the exponents with steps coprime to $n$ and the
same injectivity condition. [Production Fourier certificate](../../../scripts/probes/probe_sponsor_paley_spectrum.cpp)

To see the bound, write $e(k)=\exp(2\pi\mathrm i k/n)$ and
$V(k)=\sum_jh_je(kj)$. Twist the kernel by $e(ui+vj)$, and let
$u'=u$ at the first prime and $u'=u+n/2$ at the second. If $u'$ and $v$
have different parity, the two lifts cancel. Otherwise take
$A=(u'-v)/2$ and $B=(u'+v)/2$. The twist $e(u'i+vj)$ becomes
$e(Ar+Bs)$. Inserting the same-parity condition on $r,s$ gives the complete
double transform

$$
\epsilon^a\left[
e(Ba)V(A)V(B)+e((B+n/2)a)V(A+n/2)V(B+n/2)
\right].
$$

Every double Fourier coefficient therefore has magnitude at most $2K^2$.
With Fourier coefficients normalized by $1/n$, an interval indicator
has coefficient at zero at most one, and its $k$th coefficient has magnitude
at most $1/(2\min(k,n-k))$ by the geometric series. Summing gives the bound
$1+\sum_{j=1}^{n/2}1/j\le 2+\log(n/2)<23$ for the sum of the absolute
coefficients. Expand both interval indicators and apply the triangle inequality.
A unit step permutes the Fourier coefficients.

The field factorizations, set multiplicities, and two-to-one cyclic change of
coordinates are Lean theorems.
The finite prime values use the GMP scan. Its small controls compare every
twist against a direct ordered field-pair sum. They also check every double
Fourier coefficient at $a=0,1$ in the control fields by reduction at a primitive
root of unity. The rectangle estimate uses the previously recorded numerical
spectrum certificate. Arbitrary polynomial-size subsets in the classical
Paley conjecture remain open.

## Between two different products

There are three mixed results. The first controls arbitrary subsets on two
large sets of different product parities. The second controls arbitrary
subsets in two *fixed* different strata on smaller evaluation domains.
The third allows unions of whole strata at the second prime.

### Doubled points and adjacent sums

Write $D=2H$ and $E=(1+g)H$. Every element $2x$ is the sum of the pair
$(x,x)$ and has product $x^2$. Every element $(1+g)y$ comes from $(y,gy)$
and has product $gy^2$. The products thus belong to opposite parity classes
in $H$. Both outputs are nonzero. By uniqueness of the unordered representation
of a nonzero sum, the two output cosets are disjoint. Each has $2^{30}$ points.

For any $A\subseteq D$ and $B\subseteq E$ the bound is
$|S(A,B)|\le K\sqrt{|A||B|}$. Indeed the entry at $(2g^i,(1+g)g^j)$ is
$\chi(2)\epsilon^i\chi(1-cg^{j-i})$ for $c=(1+g)/2$. Removing the signs
on the rows leaves a circulant whose singular values are the magnitudes of the
Fourier coefficients of $\chi(1-cg^i)$. For this ratio all 128 residue-class
transforms are evaluated. Reflection pairs rows only for the earlier
within-coset certificate.

| Prime | Cross-coset bound $K$ | Signed row at the ratio $c$ | Maximizing frequency residue |
| --- | ---: | ---: | ---: |
| First | 415,408 | −30,612 | 968,006 |
| Second | 409,401 | 40,304 | 3,607,316 |

Within either coset the earlier certificate gives $K_0=449676$ and $448831$
at the two primes respectively. The block matrix on $D\cup E$ therefore has
norm at most $K_0+K$, namely **865,084** and **858,232**, by separating its
diagonal and off-diagonal blocks.
There are $2^{31}$ distinct sites in this union. Each of the $2^{30}$ product
strata contributes exactly two antipodal points, since a prescribed square
$x^2$ or $gy^2$ has two roots in $H$. Thus the union bound includes
arbitrary choices between these two coordinates over any sets of product
indices, even with both parities mixed on both sides. The common-summand
section $s\mapsto z+s/z$ for fixed $z\in H$ provides a separate one-point
section through every product. Its differences are $(s-t)/z$, so the earlier
within-coset bound applies directly to arbitrary subsets of that section.

To reproduce, compile the existing integer spectrum verifier with C++17 and
GMP and run it with `first 128 4 1073741824 double-adjacent` and the corresponding
`second` command. For the complete rectangle the sum is $n\chi(2)$ times
the row sum at the first prime and zero at the second by nonsquare scaling.
The exact cross sums are **−32,869,384,716,288** and **0**. The first-prime
Paley graph induced on $D\cup E$ is regular of degree 1,073,711,053. Its
row sum is $-30929-30612=-61541$ on either coset because $2$ and $1+g$ are
squares and replacing $j$ by $-j$ preserves the first-prime subgroup signs.
[Cross-coset transform](../../../scripts/probes/probe_sponsor_paley_spectrum.cpp)

More generally the nonzero sumset is the disjoint union of
$C_d=(1+g^d)H$ for $0\le d<n/2$. Indeed the ratio of the two summands of a
nonzero sum is unique up to inversion by the Sidon property. A nonzero stratum
$T_a$ selects the two points $\pm(1+g^d)g^{(a-d)/2}$ from every $C_d$ with
$d\equiv a\pmod2$ and no points from the other cosets. Thus the certificates
above compute one even and one odd ratio class in this entire partition.

For any collection of these classes, put $c_d=1+g^d$.
Simultaneous cyclic Fourier transformation in the exponent of $H$, after
removing the common row sign $\epsilon^i$, splits its Paley matrix into
$n$ frequency blocks. The block at $k$ has entries
$\chi(c_d)\sum_j\chi(1-(c_e/c_d)g^j)e(kj)$. Its largest singular value,
maximized over $k$, is exactly the operator norm on the union. This gives
a finite matrix target for extending the two-class bound to larger parts
of the sumset. On an individual nonzero product stratum the Fourier
coefficients along each occupied coset vanish at every odd frequency because
the two points are antipodal.

### Subsets of fixed adjacent strata

Let $U\subseteq H$ have order $32768$. Put $A_0=\{x+1/x:x\in U\}$ and
$B_0=\{y+g/y:y\in U\}$. Then $A_0\subseteq T_0$ has 16,385 points.
The inverse-pair partner $g/y$ never belongs to $U$, so $B_0\subseteq T_1$
has 32,768 points. For all $A\subseteq A_0$ and $B\subseteq B_0$, the
following integer bounds hold.

| Prime | $S(A_0,B_0)$ | Upper bound on squared operator norm |
| --- | ---: | ---: |
| First | 71,472 | 1,643,914 |
| Second | −23,964 | 1,643,844 |

In particular the relative discrepancy is below $15.66\%$ whenever both
subsets have at least $8192$ points. Simultaneous dilation by $g^i$ carries
these bounds to the pair of strata $(T_{2i},T_{2i+1})$, covering $2^{29}$
different pairs at each named prime with a specified subdomain in each stratum.

The verifier computes the exact signed rectangular matrix in row blocks of
size at most 512 by Jacobi evaluation. For each block $P$, bitwise population
counts give every entry of $G=PP^\mathsf T$, with zeros handled separately.
For symmetric integer $G$, the maximum absolute row sum is an initial bound
on $\|G\|_2$. To improve it, square $G$ exactly. Divide by an integer $s$ and
round entrywise to a symmetric matrix $Q$ of integers of magnitude at most
65536. Compute the maximum absolute row sum $e$ of $G^2-sQ$ exactly.
Any integer upper bound $b$ on $\|Q\|_2$ gives
$\|G\|_2\le\lceil\sqrt{sb+e}\rceil$. Three recursive steps suffice.
The full squared operator norm is at most the sum over blocks of their squared
operator norms, since $\|Pv\|_2^2$ adds over disjoint row blocks. Applying
this to the two indicator vectors proves the displayed bounds. Small controls
check the positive-semidefinite inequality independently using rational
elimination. The production command is `probe first 32768 512 4` or
`probe second 32768 512 4` after compiling with C++17 and GMP.
[Integer Gram verifier](../../../scripts/probes/probe_sponsor_mixed_trace_norm.cpp)

### Sweeping different products at the second prime

Start with any two nonempty sets $A\subseteq T_0\setminus\{0\}$ and
$B\subseteq T_1$. For $1\le k,l\le n/2$, define $U_k=\bigcup_{i<k}g^i A$
and $V_l=\bigcup_{j<l}g^j B$. All products represented on the first side are
even and all on the second are odd. Within each union the products are different,
so the sizes are $k|A|$ and $l|B|$. Multiplication by $g$ loses at most the
initial seed from each union. It negates the total character sum when applied
on both sides. The triangle inequality for the lost and gained points gives

$$
\frac{|S(U_k,V_l)|}{|U_k||V_l|}\le \frac1k+\frac1l .
$$

For example, $k=l=65536$ gives a relative bound of $1/32768$ for arbitrary seed
subsets. [Lean sweep theorem](../../../ArkLib/Research/ProximityGap/Frontier/PaleyMixedProductTraces.lean)

### What the original spectrum can say about a fixed mixed pair

Write the two product parameters as $s,t\in H$, $s\ne t$, and put $y=hx$.
For $h\ne1$ the character on this ratio diagonal is

$$
\chi(1-h)\chi(x)\chi(x^2-c_h),\qquad
c_h=\frac{t/h-s}{1-h}.
$$

On a named subgroup one has $c_h\in H$ **if and only if** $t=sh^2$.
In fact $t+c_h h^2=sh+c_hh$. If $c_h\in H$, a nonzero common sum on these
two sides must have identical unordered pairs. Either ordering would give
$h=1$ or $s=t$. A zero sum gives $c_h=-s$ and $t=sh^2$. Conversely this
relation gives $c_h=-s\in H$. Thus outside the two roots of $h^2=t/s$ and
the elementary rows $h=1,t/s$, the mixed sum calls for character rows outside
the original subgroup. A relative power saving on the whole $T_0\times T_1$ rectangle at
a named prime remains open. [Lean classification](../../../ArkLib/Research/ProximityGap/Frontier/PaleyMixedProductTraces.lean)

There are uniform signed counts on subfamilies of pairs for *every* choice of
distinct products. For example, the $n$ pairs $(x+s/x,x+t/x)$ are distinct.
If two values of $x$ give the same pair while differing, their product would
have to equal both $s$ and $t$. The character on such a pair is
$\chi(s-t)\chi(x)$. At the second prime the matching sum is zero. Thus
$|S(T_s,T_t)|\le |T_s||T_t|-n$ for every mixed pair there, where this
last formula uses field elements as product subscripts. At the first prime
this matching is monochromatic.

For products $s$ and $t=h^2s$ in the same parity class, the pairs
$(z,hz)$ and $(z,-hz)$ for $z\in T_s\setminus\{0\}$ also give exactly
$n$ distinct entries if $t\ne s$. Their sum is
$(\chi(1-h)+\chi(1+h))\sum_{z\in T_s}\chi(z)$. For the base products
$1,g$ the latter single sum equals $E+1,O$ respectively in the notation
of the four class sums above. Indeed, before removing doubled lifts the
sum over $x=g^i$ is $\sum_i\epsilon^{i+a}h_{2i-a+n/2}$ at $a=0,1$.
The fixed endpoints $\pm2$ each have character one at either named prime.
Thus the two base sums are $-32928,2000$ at the first prime and
$-88256,20416$ at the second. Scaling gives the single sums for all remaining
products. These $n$-entry subfamilies give only a small relative improvement
in the bound on the full fixed rectangular sum.

### A single stratum against two reciprocal products

At the second prize prime let $A_s=T(s)\setminus\{0\}$, for any $s\in H$.
For every odd $k$, put $q=g^k$. Then
$$
S\big(A_s,A_{q^2s}\cup A_{q^{-2}s}\big)=0.
$$
Each side of the rectangle is an ordinary set. The source has exactly
$n/2$ points for every product, since an even product adds two fixed
points and includes zero, whereas an odd product has no fixed points
and omits zero. The target has exactly $n$ points. If $s$ has odd product
exponent, all three sets in the formula are already the full product strata.

For every finite set $A$, exchanging the summation variables gives
$S(A,qA)=\chi(-q)S(A,q^{-1}A)$. Each difference transforms by
$y-qx=(-q)(x-q^{-1}y)$. The second prime has $\chi(-1)=1$ and
$\chi(q)=-1$, so the two sums cancel exactly. Dilation carries $A_s$
to $A_{q^2s}$ by multiplying both summands by $q$. Since $q$ has order
$2^{30}$, the three products $s,q^2s,q^{-2}s$ are distinct. The uniqueness
of nonzero two-term sums makes the two target strata disjoint. The identity
also holds for any union of distinct such reciprocal pairs about $s$.
For one such pair the individual sums have the same absolute value,
which may be positive. At the first prime the subgroup consists of squares,
so the reflected sums have the same sign.

A small prime gives a nonzero individual sum. In $\mathbb F_{313}$ take the
order-eight generator $q=188$ and product $s=188$. The full stratum is
$\{20,124,189,293\}$. Its two target strata are $\{4,150,163,309\}$ and
$\{6,100,213,307\}$. Evaluating the quadratic characters on the two
$4\times4$ rectangles gives $+8$ and $-8$.

The Lean theorem on the named field takes the additive Sidon property as its
only computational premise. The independent exhaustive fourth-energy scan
supplies that premise; the signed identity holds without it for the sum
of the two separate rectangles.
[Lean theorem](../../../ArkLib/Research/ProximityGap/Frontier/PaleyMixedProductTraces.lean) ·
[Production Sidon scan](../../../scripts/probes/probe_sponsor_phi.cpp)
