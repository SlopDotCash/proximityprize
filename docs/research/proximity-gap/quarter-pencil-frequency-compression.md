# Frequency compression for three fibers of an arbitrary polynomial pencil

On the first named quarter-rate grid, a failure at **447,392,428 errors** requires **at least eleven distinct monomial degrees** in the combined support of the reduced pair. The proof works over any field containing the grid. On every normalized dyadic quotient of size at least $2^{28}$, eight or fewer degrees cannot give a three-head score above $9N/16$, for arbitrary coefficients and arbitrary targets. On smaller quotients the same criterion gives the cutoffs below. [First-failure equivalence](quarter-successor-split-pencil.md) · [Three-head score](quarter-three-head-root-score.md) · [Earlier four- and five-frequency bounds](quarter-sparse-pencil-scores.md)

## A bound for every exponent multiplier

Let $H=\mu_N$ in a field, and let $P,Q$ be coprime polynomials defining a nonconstant rational map of degree $m$. Their coefficients and target values may lie in an extension field. Suppose the gcd of the combined exponent differences is one. Their joint support contains zero, since otherwise $X$ divides them both. For any $0<u<N$ put $g=\gcd(u,N)$ and $t=N/g$. Let $W$ be the length of an integer interval containing representatives modulo $N$ of all the exponents multiplied by $u$; one may rotate this interval around the circle. For any three distinct target values let $r$ be their total preimage size in $H$. If $3W<N$, then
\[
                     r\le 2m+3W(1-2m/N)                                      \tag{1}
\]
provided $2m\le N$.

To count cosets on which the rational map is constant, write
\[
   P(X)=\sum_{j=0}^{t-1}X^jP_j(X^t),\qquad Q(X)=\sum_{j=0}^{t-1}X^jQ_j(X^t).
\]
Every coefficient polynomial has degree at most $\lfloor m/t\rfloor$. At least one minor $P_iQ_j-P_jQ_i$ is nonzero. Otherwise all columns $(P_j,Q_j)$ are proportional over the rational function field, so $P/Q$ is a rational function of $X^t$. Substituting $X^t$ into a reduced numerator and denominator preserves coprimality by Bézout's identity. Uniqueness of a reduced pair would then make every original exponent divisible by $t>1$.

On a coset $a\mu_t$, if the map takes a single projective value, the linear combination of its two rows giving that value vanishes at all $t$ sites. After reducing modulo $X^t-a^t$ its degree is below $t$, so every coefficient vanishes. Thus the minor vanishes at $a^t$. Distinct cosets have distinct $a^t$, and the total number of sites in constant cosets is at most $2t\lfloor m/t\rfloor\le 2m$.

Now let $K$ count sites in cosets constant at one of the *selected* targets. On any other coset parametrize by $x=a y^u$ for $y\in H$, with $g$ preimages at every site. For each selected target its defining polynomial on that coset, multiplied by a common Laurent monomial and with exponents reduced modulo $N$, has degree at most $W$. It is nonzero since some site misses that target. The coset thus supplies at most $3W/g$ selected sites. Summation gives
\[
                 r\le K+3W(1-K/N).
\]
The right side increases with $K$ when $3W<N$. Using $K\le2m$ proves (1). This bound also applies to a dense support whenever a particular multiplier gives a short enough interval.

The coset argument also bounds agreement with a prescribed value on each partially covered coset. [Coset interpolation and equality cases](quarter-split-coset-interpolation.md)

## Packing the exponents on a torus

Suppose the support is $0,e_1,\ldots,e_{s-1}$. The $N$ points $i(e_1,\ldots,e_{s-1})$ for $i$ modulo $N$ are distinct on the real torus $(\mathbb R/N\mathbb Z)^{s-1}$, by the gcd condition. In real coordinates adjoin $x_0=0$. The open region $\max_j x_j-\min_j x_j<w$ has volume $s w^{s-1}$. If $x_0$ is least, all the remaining coordinates are in $(0,w)$ up to measure-zero boundaries. If some $x_j$ is least, its range is $(-w,0)$ and each of the other $s-2$ variable coordinates lies in an interval of length $w$. Each of the $s$ choices therefore contributes $w^{s-1}$.

For $0<2w<N$ this region injects into the torus. When $Ns w^{s-1}>N^{s-1}$, its $N$ translates around the displayed points overlap. Subtract the two representatives at an overlap. Their coordinate range, including zero, is less than $2w$ by the triangle inequality for the range. The difference of the two translate indices gives $0<u<N$ with integer representatives for all $u e_j$ in a common interval of width $W<2w$; integrality holds because the translate centers and torus periods are integral.

## Score and full-fiber consequences

For $m<N/4$, the elementary bound $r\le3m$ gives $2r-3m\le9N/16$ when $m\le3N/16$. Above this degree, $W<N/10$ in (1) gives
\[
       2r-3m\le m+6W(1-2m/N)<3N/5-m/5<9N/16 .
\]
Take $w=N/20$. Thus **$Ns>20^{s-1}$** suffices. In order of support sizes five, six, seven and eight, the smallest sufficient dyadic grid sizes are **$2^{15},2^{20},2^{24},2^{28}$**. For a general joint support, first divide all exponent differences by their gcd $b$. The original degree is $b m$ and each site on the normalized quotient has $k=\gcd(b,n)$ preimages. The original score is at most $k$ times the normalized score because $k\le b$.

At the first named successor all three fibers must have the full degree $D=n/4-2$, $n=2^{30}$. Normalization gives $D=bm$. Each fiber has at most $k m$ points, forcing $b=k$. Hence $b$ is a power of two dividing $D$, namely one or two. On the normalized grid $N=n/b\ge2^{29}$ we therefore have $r=3m$ and $m/N=D/n$. By (1) any compressed width below $N/3$ must obey
\[
                         W\ge \frac{m}{3(1-2m/N)}.
\]
For $2\le s\le10$ one has $Ns>(1201/100)^{s-1}$. Choosing $w=100N/1201$ gives $W/N<200/1201<D/[3(n-2D)]$, a contradiction. The eleven-degree necessity follows for every witnessing pair, including ones factoring through $X^2$. [Exact arithmetic and finite-field tests](../../../scripts/probes/probe_quarter_pencil_frequency_compression.py)

At the first named half-rate successor, **268,435,457 errors**, at least two triangle pencils must each have three complete fibers of odd degree $n/4-1$. The same proof forces **each** of these reduced pairs to use at least eleven degrees. Indeed the only normalization is $b=1$, and the required width ratio increases with the relative degree. The identical necessity holds for any three full fibers at the adjacent odd degree $n/4+1$ on either named field. [Two required half-rate pencils](half-successor-pencil-monodromy.md)
