# An exact three-map criterion for four-head failure at the quarter-rate seam

Let $n=4d+4$, $k=d+1$ and consider $e=n/2$ errors. For the named second prime, $n=2^{30}$ and the bad-label budget is $2n$. The existence of a four-head overrun on the prescribed subgroup $H$ is equivalent to the data and count below. This gives a construction from rational maps as well as a necessary condition. The arbitrary three-map case on the production subgroup remains open. [Necessity of saturation](quarter-saturated-symmetry.md) · [Constant involution on side directions](quarter-saturated-opposite-directions.md)

## Field and divisor data

Write $F$ for the named field. In the split case choose three nonconstant maps $z_i=p_i/q_i$ over $F$. In the nonsplit case work in its quadratic extension $K$, with the coefficient involution $\sigma$, and require $\sigma(z_i)=1/z_i$ as rational functions with the coordinate indeterminate fixed. In either case choose each numerator and denominator coprime and put $m_i=\max(\deg p_i,\deg q_i)$. Require $m_1+m_2+m_3=d$.

For each complementary pair $j<k$, put $U_{jk}^{\pm}=p_jq_k\pm p_kq_j$. Require their six zero divisors to be simple, disjoint, and supported on exactly $H$ minus four distinct singleton sites. Equivalently, for the monic quartic $K_4$ of the singleton points, the polynomial identity
\[
 K_4(X)\prod_{j<k} U^+_{jk}(X) U^-_{jk}(X)=c(X^n-1),\qquad c\ne0,
\]
must hold. Since the six degree bounds add up to $4d$, this also forces each signed factor to have degree $m_j+m_k$. For an arbitrary injective domain replace $X^n-1$ by its full monic domain locator.

The split or nonsplit distinction follows by taking eigen-coordinates for the field-rational projective involution on directions. In those coordinates it acts as $z\mapsto-z$. If its two fixed directions are conjugate, choose conjugate linear coordinates for the numerator and denominator, so field conjugation acts as $z\mapsto1/\sigma(z)$ on projective direction values. A map defined on the original field line in these coordinates satisfies $\sigma(z_i)=1/z_i$. The complete signed coincidence divisors are the six double strata by the fixed-direction theorem.

In the nonsplit case one can normalize $q_i=\sigma(p_i)$ simultaneously for each pair. Coprimality and $\sigma(z_i)=1/z_i$ give $\sigma(p_i)=c_i q_i$ and $\sigma(q_i)=c_i p_i$ for a constant with $c_i\sigma(c_i)=1$. Rescale the pair by $1+c_i$ when $c_i\ne-1$ and by a nonzero trace-zero constant when $c_i=-1$. Then its two entries are conjugate. The degree and divisor conditions are independent of these rescalings.

## Reconstruction and the exact fresh-label count

For $\{i,j,k\}=\{1,2,3\}$ define $P_i=p_i q_jq_k$, $Q_i=q_i p_jp_k$. Each has degree at most $d$. Use the four sign vectors
\[
 (+++),\quad (+--),\quad (-+-),\quad (--+).
\]
For a sign vector $s_h$ use the head $(s_h\cdot P,s_h\cdot Q)$ in split eigen-coordinates. In the nonsplit case its two entries are conjugate; write them as $(U,V)$. With a fixed nonzero $\theta\in K$ satisfying $\sigma(\theta)=-\theta$, the physical head is $((U+V)/2,(U-V)/(2\theta))$ over $F$. This fixed linear change preserves the six coincidence strata and identifies the norm-one direction circle with the physical projective line.

For the side joining heads $0,i$, the difference is, up to its common sign, $2U^+_{jk}(q_i,p_i)$. For the opposite side it is $2U^-_{jk}(q_i,-p_i)$, again up to a common sign. Therefore the exact pairs of equal heads are $(0,i)$ at the plus roots and $(j,k)$ at the minus roots. Coprimality guarantees the remaining vector factor is nonzero at every geometric point. The four holes have four distinct head values. Lean verifies all six vector identities and the conjugacy of the reconstructed rows. [Algebraic reconstruction](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSlopeReconstruction.lean)

Receive the repeated head on every double site. Assign the four holes bijectively to the four heads and receive their designated values. Each head now has $2d+1=n/2-1$ joint sites. At a double site of $U^\pm_{jk}$ the two mismatching head directions are exactly $\{z_j(x),-z_j(x)\}$. They are distinct, since a common zero or pole of the two participating maps would place the site in both signed divisors. At a hole $x$ assigned to $h$, the three directions are
\[
 s_{h,1}z_1(x),\quad s_{h,2}z_2(x),\quad s_{h,3}z_3(x),
\]
with the sign table above and projective interpretation at poles. These formulas hold on the ordinary projective line in the split case and on the norm-one circle in the nonsplit case.

Let $M$ denote the number of distinct unordered pairs of double-site directions; their union has exactly $2M$ elements. Let $T$ be the number of distinct singleton directions outside this union for the chosen assignment. The required count $2M+T>2n$ holds exactly when $M=4d$ and $T\ge9$, or $M=4d-1$ and $T\ge11$. This is the full hole condition, including repeats between holes. To get actual finite scalar labels, choose a common invertible physical row change sending a missing projective direction to the point omitted by the affine scalar parametrization. Such a direction exists because $|F|+1>2n+4$. All counted directions then give distinct finite scalars on the same received pair. Each agrees with the corresponding folded head on its joint core and a fresh site. A simultaneous explanation of the support by two degree-at-most-$d$ polynomials would agree with the head on more than $d$ core sites and so could not fit the mismatching fresh site. Every counted scalar is therefore literally bad. Conversely a saturated overrun must assign one hole per head and its finite directions belong to these same sets, giving the stated criterion. [Formal fresh-core event theorem](../../../ArkLib/Research/ProximityGap/Frontier/_HalfPredecessorCoreFreshDecode.lean)

## An actual length-16 witness on a selected injective domain

Over the second named prime, take $n=16$, $k=4$, $e=8$ and
\[
z_1=(8X+9)/(X+2),\quad z_2=(X+3)/(4X+5),\quad z_3=(3X+8)/(5X+1).
\]
The six signed quadratics each have two distinct roots in the field. Their twelve roots are disjoint, and the four holes are $1,2,3,4$, assigned to heads $0,1,2,3$ in order. All 24 double directions and all twelve singleton directions are distinct. No row change is needed here. The exact checker constructs the sixteen-site received pair, interpolates the folded polynomial on each eight-site support, and checks the failure of the unique joint explanation on that support. Thus four actual heads achieve **36 bad scalars**, exceeding twice this domain's length. The domain is chosen by the signed quadratics; this example establishes a count on an injective domain and does not give a witness on the prescribed smooth subgroup or an overrun of the named prime's numerical security budget. [Reproducible event check](../../../scripts/probes/probe_quarter_slope_reconstruction.py)
