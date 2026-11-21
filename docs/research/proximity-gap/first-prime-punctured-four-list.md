# A punctured scalar list decides the first half-rate successor

Let $H$ be the first named field's multiplicative subgroup of order $n=2^{30}=4h$, and give the half-rate code its literal bad-scalar budget $n$. Put $e=h+1=268435457$ and fix any $a\in H$. The following are equivalent under the written half-rate interpolation theorem.

1. Some received pair on $H$ has more than $n$ MCA-bad scalars at $e$ errors.
2. On $H\setminus\{a\}$ some word lies within $e$ errors of **four distinct polynomials of degree at most $2h-2$**.
3. On $H$ some word lies within $e$ errors of four distinct polynomials of degree at most $2h-1$ which all match it at $a$.

If these conditions hold, a single received pair has at least $n+2$ bad scalars. Together with the general $n+3$ upper bound the worst count in the failing case is therefore either $n+2$ or $n+3$. The construction from a punctured list is elementary; the reduction from unrestricted MCA uses the factor-exclusion and four-head count. Existence of this particular punctured list over the named field is open. [Written four-head extraction](half-rate-successor-multiplicity.md#counting-the-heads) · [Kernel-checked support counts and polynomial separation](../../../ArkLib/Research/ProximityGap/Frontier/PuncturedFourWordProfile.lean)

## From the received pair to the punctured code

The interpolation theorem gives four collinear polynomial heads with at least $3h-2$ joint agreements each and just one site $a'$ covered by none of their cores. They have the form $(A,B)+D_i(S,T)$ with $S,T$ coprime, $\max(\deg S,\deg T)=1$ and $\deg D_i\le2h-2$ after translating one head to zero. At each covered site $(S,T)$ never vanishes simultaneously, so the received pair determines one scalar coordinate along that line. All agreeing heads give that scalar. This gives four words within $h+1$ errors of a single scalar word on $H\setminus\{a'\}$. Multiplication of coordinates by $a'/a$ transports the punctured list to $H\setminus\{a\}$. Multiplying every punctured polynomial and the received word by $X-a$ and extending the center by zero proves 2 implies 3. Conversely subtract the first polynomial from all four heads and the center in 3. Since all differences vanish at $a$, divide by $X-a$ to recover 2.

## The three possible error patterns

On the $4h-1$ remaining sites let $E_i$ be the four error sets, $m_j$ the number of sites in exactly $j$ of them, and $B=\sum_i(h+1-|E_i|)$. Two distinct degree-at-most-$2h-2$ polynomials differ in at least $2h+1$ coordinates. Hence $|E_i\cup E_j|\ge2h+1$. At a site in $r$ error sets the number of the six pairwise unions containing it is $0,3,5,6,6$ respectively for $r=0,1,2,3,4$. Counting those incidences and the individual errors gives
$$
2B+m_0+m_3+3m_4\le1,\qquad m_2+2m_3+3m_4=5-B+m_0 .
$$
Thus every head has exactly $h+1$ errors, no site misses all four heads, and the only possibilities are as follows.

| $m_0$ | $m_2$ | $m_3$ | Intersections of pairs of error sets |
|---:|---:|---:|---|
| 0 | 5 | 0 | five distinct overlaps, one missing edge |
| 1 | 6 | 0 | six distinct overlaps |
| 0 | 3 | 1 | three edges share one triple-error site, the other three have distinct sites |

Indeed a pair intersects at most once by the union bound. When it intersects, both heads agree with the center on exactly $2h-2$ sites in the punctured domain. These sites exhaust all possible roots of their difference. In particular the two values at the missing site $a$ are distinct. At least three distinct head values occur at $a$ in the first row, and all four are distinct there in each of the last two rows.

## Constructing bad scalars with no interpolation assumption

Write $D_i$ for the four punctured polynomials, $y$ for the center. Use the row-pair heads $W_i=(XD_i,D_i)$, of degrees below $2h$. Away from $a$ set $u(x)=(xy(x),y(x))$. Every site there except the $m_0$ sites matching all heads supplies its distinct scalar $-x$, assigned to a mismatched head. At $a$, let $v$ range over the distinct $D_i(a)$. Choose $u_1(a)$ outside these at most four values. The scalar for each $v$ is
$$\gamma_v=(a v-u_0(a))/(u_1(a)-v).$$
Choose $u_0(a)\ne a u_1(a)$ and exclude the at most $4(n-1)$ values giving an earlier scalar. The named field has room. The $\gamma_v$ are then distinct, since equality for two distinct $v$ would give $u_0(a)=a u_1(a)$.

The core of every head has $3h-2\ge2h$ points. For every assigned scalar, adding its fresh coordinate gives $3h-1=n-e$ agreements for the folded head. Any two polynomial rows explaining this witness agree with the assigned pair on the core and hence everywhere. This contradicts the given fresh mismatch. There are $n-1-m_0+\#\{D_i(a)\}$ labels, which is at least $n+2$ in all three cases and equals $n+3$ in the triple-error case.

## A full odd pencil is necessary

Return to the extended four-word list. Each of the three overlap patterns contains a triangle of head indices whose three error intersections are distinct singleton sites. For the triple-error pattern use the head outside the triple and two of its heads. For the graph with five edges use either triangle avoiding the missing edge. For the triangle $i,j,k$, let $Q_i$ be $E_i$ with its two triangle intersections removed, and define $Q_j,Q_k$ similarly. These three disjoint sets have size $h-1$. The complement $Z$ of the three error sets in the full domain has size $h$. The difference of the two extended polynomials with indices $i,j$ vanishes on $Z\cup Q_k$, exactly its $2h-1$ allowed distinct roots. Cancelling the common vanisher on $Z$ from the three edge differences gives a nontrivial linear dependence among $L_{Q_i},L_{Q_j},L_{Q_k}$, with all coefficients nonzero. Thus an over-budget example requires three **full** fibers of degree $2^{28}-1$. A four-cycle with only a partially filled third fiber cannot realize the punctured criterion. For comparison the full-fiber case is impossible on the complex $2^{30}$th roots by the sharp degree gap. The positive-characteristic component-size restrictions apply at the actual production length. [Complex degree gap](quarter-three-heads-32-fibers.md#a-sharp-degree-gap-on-complex-dyadic-roots) · [Named-field full-fiber restriction](production-fiber-correspondence.md)
