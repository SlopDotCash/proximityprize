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
spectrum certificate. Mixed product strata and arbitrary polynomial-size
subsets in the classical Paley conjecture remain open.
