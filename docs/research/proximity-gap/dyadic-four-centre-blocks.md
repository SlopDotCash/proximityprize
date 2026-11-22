# Four antipodal centers and a finite-field obstruction

On complex dyadic roots, equal values of a signed monic locator ratio at two distinct pairs of antipodal centers force its signed support to be invariant under the antipode. At order 256 in either named prime field, constancy on two complete four-site orbits similarly forces equality of the two opposite-pair populations in every four-site orbit. At order 1,024 the latter implication fails for every choice of two four-site center orbits, already for ratios of degree at most 180. The positive and negative results allow arbitrary internal assignments on the remaining sites.

At production length there are even equal-cardinality, disjoint numerator and denominator sets of size at most **188,743,680** whose ratio agrees on **8,388,608 prescribed sites**, the union of any two cosets of the order-$2^{22}$ subgroup, while the corresponding complex comparisons fail. This degree is below the first half-rate successor pencil degree $268,435,455$. The construction controls two selected center cosets. A split pencil also requires a complete third fiber with its prescribed degree. [Production pencil requirements](half-four-fiber-parity.md)

## Two antipodal pairs over the complex numbers

Let $N=2^k\ge8$, let $z$ be primitive of order $N$, and write the locator ratio as $R(X)=\prod_j(X-z^j)^{w(j)}$ for integer weights. Centers avoid the support. For $1\le j<N/4$ introduce
$$
 \phi_j=\frac{1-z^j}{1+z^j}.
$$
These $N/4-1$ chord ratios are multiplicatively independent modulo roots of unity. To prove this, use the independent primitive units $1-z^r$, with $r$ odd modulo sign. If $j=2^a d$ with $d$ odd, the factorization of $1-z^j$ uses precisely the odd classes $r\equiv\pm d\bmod N/2^a$, once each, up to a root of unity. For $1+z^j=1-z^{j+N/2}$ the corresponding classes satisfy $r\equiv\pm(d+N/2^{a+1})\bmod N/2^a$. These two sets are the equal-size children of a single class modulo sign at modulus $N/2^{a+1}$. As $j$ runs from 1 through $N/4-1$, each pair of children occurs once: for fixed $a$ take precisely the odd $d<N/2^{a+2}$. Hence the primitive-unit exponent vectors are differences of the indicators of sibling sets. Two such vectors have disjoint supports or one is constant on the other's support. Their dot product is zero and each squared length is positive. Independence follows. [Independence of primitive dyadic units](quarter-dyadic-parity.md#independence-of-the-dyadic-cyclotomic-factors)

Write $v(j)=w(j)-w(j+N/2)$. In the comparison $R(z^x)/R(-z^x)$, group the sites about $x$ by the four offsets $j,-j,j+N/2,-j+N/2$. The first two give equal chord ratios up to sign, the last two their reciprocals up to sign. The offsets $\pm N/4$ contribute fourth roots of unity. Thus equality forces
$$
 v(x+j)+v(x-j)=0\qquad(1\le j<N/4).
$$
Reflection and antiperiodicity extend this equality to every offset. It holds at zero since the centers avoid the support, and at the quarter turns by antiperiodicity alone. A second antipodal pair centered at $y\not\equiv x\bmod N/2$ gives another antireflection. Their composition makes $v$ periodic under $2(y-x)\ne0$ in the cyclic group of order $N$. Every nonzero translation generates a subgroup containing the antipode. Hence $v=0$. The Lean theorem verifies the antireflection argument for any integer-valued signal on a dyadic cyclic group. [Dyadic reflection proof](../../../ArkLib/Research/ProximityGap/Frontier/DyadicAntiperiodicReflection.lean)

## Four-site orbits at length 256

At either named prime, suppose $R$ is constant on the four-site orbit with exponent representative $a$ at length 256. For its numerator and denominator take disjoint simple sets, so $w$ is ternary. Taking products over opposite pairs gives a weighted ratio on the order-128 quotient with weights $s(j)=w(j)+w(j+128)$, which agree at its antipodal centers with exponents $a,a+64$. Put $v(j)=s(j)-s(j+64)$. The chord exponents $v(a+j)+v(a-j)$ now have absolute value at most eight. [Coset product identity](dyadic-orbit-norm-split-pencils.md#norms-of-evaluations-on-complete-cosets)

Using the full order-128 unit logarithms, the verifier checks the logarithm of each $\phi_j^{128}$ and an integer basis of the kernel modulo $(p-1)/128$. The circumscribed ball of squared radius $31\cdot 8^2$ has exactly five lattice points in each field. Only the origin lies in the cube of radius eight. Thus a single complete four-site center orbit forces exactly the antireflection $v(j)=-v(2a-j)$ on all 128 quotient indices. Two distinct such orbits then force
$$
 w(j)+w(j+128)=w(j+64)+w(j+192)\qquad\text{for all }j.
$$
This conclusion concerns the signed populations of opposite pairs. A nonzero difference of these populations at any site rules out constancy on eight such centers. [Unit logarithms and full-group certificates](mu128-unit-ellipsoid-transfer.md) · [Exact antipodal verification](../../../scripts/probes/probe_dyadic_antipodal_blocks.py)

Consider now three disjoint full fibers $A,B,C$ of an odd-degree pencil on this length-256 grid. If $A$ contains two four-site orbits then the $B/C$ ratio gives $v_B=v_C$, where $v_i$ is the difference of the counts of fiber $i$ on the two opposite pairs of each orbit. Two four-site orbits in $B$ also give $v_A=v_C$. Alternatively, a four-site orbit in each of $B,C$ gives two distinct antireflections of $v_A-v_C=v_A-v_B$, so again $v_A=v_B=v_C$. A nonzero common difference would place at least one member of all three disjoint fibers on the same two-site half. Thus every difference vanishes and each fiber has even cardinality, a contradiction. **If one fiber contains at least two four-site orbits, the other two fibers together contain at most one.** This applies in particular to the degree-63 pencils extracted from half-rate four-lists. [Split-pencil extraction](half-four-fiber-parity.md)

The same verifier proves that on the order-64 quotient, **all** equal ratio comparisons with weights $|s(j)|\le32$ lift to characteristic zero. Thus original lengths through 2,048 admit the weighted reduction for complete cosets with this quotient. For each displacement form the integer comparison matrix $M$, removing the two center columns. The energy bound $\sum s(j)^2\le62\cdot32^2$ gives the existing covariance ellipsoid for $e=Ms$. At the antipodal shift omit its dependent coordinate. Across 32 displacements its lattice has 36 points in the first prime and 32 in the second, counting the origin in each displacement. For each of the four extra points, set $\lambda=(MM^\top)^{-1}e$ in independent coordinates. The exact strict inequality $\lambda^\top e>32\lVert M^\top\lambda\rVert_1$ excludes every supported weight vector. The verifier checks both lattice-basis orders. [Exact ellipsoid procedure](../../../scripts/probes/probe_mu128_unit_ellipsoid.py)

## The same population implication fails from length 1,024

Let $n$ be dyadic and $s$ a power of two with $2s\mid n$. Fix any two different cosets $C_a,C_b$ of $\mu_{2s}$, where $C_a$ is represented by the exponent $a$ modulo $n/(2s)$. The reflection $\rho(x)=z^{a+b}/x$ exchanges them and pairs the other cosets. At most two remaining cosets can be fixed, so at least $M=n/(4s)-2$ pairs of other cosets are available (in the applications $4s\mid n$). For each pair pick one of its cosets $C$. Each of its two $\mu_s$ halves, together with its reflected image, gives a choice of $2s$ sites. Each choice is invariant under $\mu_s$ and $\rho$.

Select $d$ of the $M$ pairs and a choice in each, producing $\binom{M}{d}2^d$ simple sets $P$ of degree $2sd$. At representatives $x,y$ of the two $\mu_s$ halves of $C_a$, the normalized locator evaluations $L_P(x)/L_P(y)$ have at most $p-1$ values. If the family is larger, two distinct sets collide. Cancel their common sites and form the resulting ratio $R$. Its two locator degrees are equal and at most $2sd$.

Every chosen site occurs in a reflection pair of product $z^{a+b}$. The reciprocal identity for each original monic locator is therefore $L_P(z^{a+b}/X)=(z^{a+b})^{sd}X^{-2sd}L_P(X)$. Rotation by $\mu_s$ also preserves the locator. The ratio is invariant under both actions, so the collision at $x,y$ makes $R$ constant throughout both prescribed cosets. At least one pair of data cosets has different choices in the two sets. In its chosen representative coset the signed population of one half differs from that of the other, even after common sites cancel.

Over the complex roots the same locators are unions of $\mu_s$ cosets and factor through $X^s$. Their quotient on the order-$n/s$ grid has two antipodal center pairs. A difference in the two half populations contradicts the characteristic-zero theorem above, so their finite-field constancy cannot lift.

| Length | $s$ | Prescribed centers | Selected pairs $d$ | Degree bound | Fields |
|---:|---:|---:|---:|---:|---|
| 1,024 | 2 | 8 | 45 | 180 | Both |
| $2^{30}$ | $2^{21}$ | 8,388,608 | 45 | 188,743,680 | Both |
| $2^{30}$ | 2 | 8 | 6 | 24 | First |
| $2^{30}$ | 2 | 8 | 7 | 28 | Second |

The first two rows have $M=126$. The last two have $M=134,217,726$. Each displayed choice meets the strict counting inequality by exact integer arithmetic. Taking any 126 available coset pairs extends the first conclusion to every supported dyadic $n\ge1024$. The counting proof supplies existence and the degree bounds. The corresponding implication at length 512 remains open here. [Integer count and positive certificates](../../../scripts/probes/probe_dyadic_antipodal_blocks.py)
