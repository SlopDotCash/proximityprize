# Exact first-prime quarter-rate three-head threshold from polynomial root counts

Let $H$ be the order-$n=2^{30}$ subgroup in the first named prime, and put $D=n/4-2=268435454$. For a polynomial $f$ write $r(f)$ for its number of distinct roots in $H$. Take the integer maximum
\[
 S=\max_{P,Q}\bigl(2[r(P)+r(Q)+r(P-Q)]-3m\bigr),\qquad
 m=\max(\deg P,\deg Q)\le D,
\]
over coprime $P,Q$ with $P,Q,P-Q$ nonzero. Constants are allowed, with distinct nonzero values. This is an optimization over **two ordinary scalar polynomials** on the actual subgroup. Its value is independent of the error count and received rows.

Write $E_3=1+\lfloor(3489660928-S)/6\rfloor$. This is the **exact first error count admitting an over-budget pair explained by three collinear polynomial heads** in the known bracket, including the attack at **480946859**. For the unrestricted MCA first failure $E$, the proof gives
\[
 \min(E,469762049)=\min(E_3,469762049).
\]
Thus $S\ge671088641$ gives the exact unrestricted value $E=E_3$. If $S\le671088640$, every count through 469762048 is secure and the remaining unrestricted interval is $[469762049,E_3]$. The known bounds on $S$ are **603979776 through 805306362**. Determining $S$ and excluding any earlier four-head or outsider overrun in the second case remain open. The unrestricted reduction invokes the written geometric interval theorem. [Quartic classification and its formalization boundary](quarter-collinear-interval.md) · [Known cubic witness](quarter-three-heads-32-fibers.md#attainment)

The exact maximum over geometrically Galois maps is 402653184. A degree-fourteen search through more than 151 million reflection-invariant endpoint pairs on the 64-site quotient also falls below the incumbent. [Symmetry proof and fixed-prime search](quarter-root-score-symmetry.md)

## The best allocation on fixed polynomial differences

An over-budget three-head family in this bracket has distinct scalar labels assigned to the heads. Every head receives at least $n+1-2(e+1)$ labels because a single head has at most $e+1$. Each has core size at least $t-\lfloor e/(n-2(e+1))\rfloor$, for $t=n-e$. The core union and the count of fresh labels exclude constant direction just as in the quartic proof, also at the single additional endpoint $e=480946859$. The determinant inequality forces any three heads covering an overrun to be collinear. Normalize their polynomial row differences along a primitive direction to obtain scalar polynomials $0,f,g$ of degrees at most $D$. The three heads are distinct, hence $f,g,f-g$ are nonzero.

Let $r$ be the number of simultaneous roots of $f,g$ on $H$, and $a,b,c$ the numbers of points where precisely one of the three pairs coincides, indexed by the head excluded. Set $x=a+b+c$. The three-head incidence inequality bounds the assigned population by
\[
 L\le V=3n-6(t-1)+2x+3r.
\]
Here the sum of the three full pair-root counts is $x+3r$ and their common intersection has size $r$. The inequality already charges any head requiring several fresh sites per assigned label. [Local count](quarter-successor-split-pencil.md#seven-units-of-slack)

Whenever $V>n$ the **upper bound is attained** on the same domain by a new received pair. Use actual polynomial heads $(Xh,h)$ for $h=0,f,g$. Receive their common value at each triple site and the coincident value at each pair-only site. The three initial core sizes are $r+b+c,r+a+c,r+a+b$, each at most $2D<t-1$ throughout the bracket. On the all-distinct sites, assign exactly enough private sites to bring every core to $t-1$. The number of unused sites is
\[
 h=n-3(t-1)+2r+x.
\]
It is nonnegative since $V=n-r+2h>n$. All $n-r-h$ ordinary sites have a foreign head and furnish distinct labels via the direction $-x_{\mathrm{site}}$. At the $h$ holes choose three more labels per site. The simultaneous avoidance construction applies since the square of the total count is below the field order. The count is exactly $n-r+2h=V$. Lean checks this construction from the actual polynomial root classes, the asymmetric private-class counts and the necessary arithmetic. [Root-profile witness and allocation theorem](../../../ArkLib/Research/ProximityGap/Frontier/ThreeHeadRootScore.lean)

## Choosing the common locator

Write $f=JP$, $g=JQ$ with coprime $P,Q$. Their root sets and the roots of $P-Q$ are pairwise disjoint. Their reduced degree is $m$, so $\deg J\le D-m$. Pair-only sites contribute at most $r(P)+r(Q)+r(P-Q)$, and common sites contribute at most $D-m$. Conversely choose a locator $J$ on exactly $D-m$ domain points outside all three reduced root sets. There is room since $r(P)+r(Q)+r(P-Q)\le3m$ and $n-3m\ge D-m$. This gives $r=D-m$ and attains every reduced root as a pair-only site. Thus the maximum of $2x+3r$ is exactly $3D+S$.

Consequently a three-head overrun at $e$ occurs exactly when
\[
 3n-6(n-e-1)+3D+S>n,
\]
and then the expression on the left is the exact largest three-head population. The first strict inequality gives the formula for $E_3$. The reduced cubic on the order-16 quotient, pulled back to $H$, has $m=3n/16$ and three full fibers, giving $S\ge3m=603979776$. The general root bound gives $S\le3D=805306362$. Together these put $E_3$ in $[447392428,480946859]$. Equality $S=3D$ requires a degree-$D$ full split pencil and gives the lower endpoint. The value $3D-1$ is impossible: at degree $D$ each missing root costs two units, and at smaller degrees the score is at most $3D-3$. Thus the split-pencil criterion at the first unresolved step is recovered exactly. At every count through 469762048 the quartic proof shows an unrestricted overrun must already have three heads, yielding the displayed comparison of first failures.

## A rank test using only subgroup sites

For each target integer $s\ge603979776$, the condition $S\ge s$ has a finite rank test on the actual prime field. Choose a degree $m\le D$ and three disjoint subsets $A,B,C\subset H$ of sizes at most $m$ with $2(|A|+|B|+|C|)\ge3m+s$. Let $L_A,L_B$ be the monic vanishers on the first two sets. Form a matrix with one row for each $z\in C$:
\[
 \bigl(L_A(z)z^i\bigr)_{0\le i\le m-|A|}\quad
 \bigl(-L_B(z)z^j\bigr)_{0\le j\le m-|B|}.
\]
The test is whether **any** such matrix has column rank below $2m-|A|-|B|+2$. It uses only evaluation sites and field operations. Enumerating the admissible subsets at the production length remains computationally prohibitive.

A contributing pair gives a kernel vector by taking its three actual root subsets. Conversely a nonzero vector in the kernel gives $P=L_AU,Q=L_BV$ with $P-Q$ vanishing on $C$. The total size exceeds $2m$ since $s>m$, so each union of two sets has more than $m$ sites. This rules out $P=0$, $Q=0$ or $P=Q$ for a nonzero vector. Divide out their gcd of degree $g$. At most $g$ selected sites disappear because the three specified sets are disjoint, whereas the maximum degree falls to at most $m-g$. The reduced score therefore increases by at least $g$ relative to the target lower bound. The resulting coprime pair certifies $S\ge s$. For the cutoff governing unrestricted safety through 469762048, one may fix $s=671088641$.

## Partial fibers in the order-64 prefix family

On the order-64 quotient, give both monic degree-15 endpoints disjoint root sets that each consist of one exponent coset of each size $8,4,2,1$. Over the actual first prime the largest third fiber has **four** points. The exact census covers 55,301,400 disjoint pairs from 145,600 sets after translation reduction. It tallies every nonzero ratio on the complement, including ratio one. Thus this family has maximum quotient score $2(15+15+4)-3\cdot15=23$, below the lifted cubic's quotient score 36. [Fixed-field census](../../../scripts/probes/probe_rate_quarter_mu64_prefix_locator_p1.cpp)

For a four-point example use the probe's primitive root $321066668146402433440778728016715546214271526818$. The two root-set bitmasks, with bit $i$ indicating exponent $i$, are `0x105012d0105010d` and `0x9010981090109830`. The ratio of their monic vanishers equals $256226834236320182178292549052558086956599848896$ precisely at exponents $1,25,41,49$.
