# Arbitrary-multiplicity section bounds and the second half-rate field

At length $n=2^{30}$ and rate one half, every injective domain in the second named prime field has at most $2n$ MCA-bad labels through **298,250,000 errors**. The first failing count is therefore at least **298,250,001**. The geometric implication is a written proof. Lean checks both actual interpolants, the truncated-slope inequality, the orthogonal variance estimate, and the determinant bound for three polynomial sections. The argument uses both agreements and disagreements, including the sites at which the received line is the whole normalized coordinate fibre. The claimed radius applies to every positive interleaving width. [Interleaving stability](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean) · [Kernel-checked components](../../../ArkLib/Research/ProximityGap/Frontier/HodgeSectionVariance.lean) · [Exact production arithmetic](../../../scripts/probes/probe_hodge_section_variance.py)

## A population inequality without a weight restriction

Work over an algebraically closed field $k$. Let $F(X,Z,Y)$ be irreducible, of value degree $b\ge2$, total $(Z,Y)$ degree at most $m$, and weight at most $W$ for weights $(1,0,d)$. At each of $n$ distinct finite sites $x$, prescribe an affine function $L_x(Z)$. Choose $M$ different scalar labels $z$, each with a polynomial $q_z(X)$ of degree at most $d$ such that $F(X,z,q_z)=0$ identically and $q_z(x)=L_x(z)$ at at least $t>d$ sites. Set

$$B_X=(2b-2)m-b(b-1)+1,\qquad B_Z=(2b-2)W-b(b-1)d+1.$$

In characteristic zero or characteristic greater than $\max(b,B_Z)$ one has

$$ M\le B_X+\left\lfloor\frac{(8mb+2)B_XB_Z+2mn+(n-d)(m+1)}{t-d}\right\rfloor.\tag{1} $$

Here and below $0\le d<t\le n$. Let $S'$ be the normalization of $\mathbb P^1_X\times\mathbb P^1_Z$ in the degree-$b$ field defined by $F$, with fibre classes $\Phi_X,\Phi_Z$, and let $B$ be its reduced branch curve. Its degrees on the two lines are bounded by $B_X,B_Z$, respectively. Indeed the binary value discriminant is homogeneous of coefficient degree $2b-2$ and isobaric of index $b(b-1)$. Each coefficient of $Y^j$ has scalar degree at most $m-j$ and coordinate degree at most $W-jd$. Outside the zero divisor of the discriminant the binary root scheme is finite étale. One extra line in each direction covers infinity. Remove the scalar labels whose entire horizontal line lies in the discriminant. At most $B_X$ labels are removed. Every remaining graph gives a simple degree-one curve $C'_z$ on $S'$. Denote the remaining population by $N$.

We use Mumford's rational intersection product on $S'$. From the horizontal ramification estimate for the minimal resolution, there are nonnegative $c_z$ such that $-(C'_z)^2\le c_z$ and $\sum_z c_z\le4B_XB_Z$. The proof counts ramification where a selected parameter line fails to be transverse to $B$; it applies to every retained section and places no condition on its coordinate fibres. The same intersection theory gives the Hodge index inequality on $\Phi_Z^\perp$ and nonnegative intersection of distinct effective curves. [Horizontal ramification and Hodge index, Lemmas 2 and 4](section-incidence-hodge-index.md#four-lemmas) · [Mumford's intersection product](https://www.numdam.org/articles/10.1007/BF02698717/)

### Truncating the order of the received function

Fix $x$. Write the scheme-theoretic full fibre as $\Phi_x=\sum_i e_iD_i$. Set $f_i=D_i\cdot\Phi_Z$ so that $\sum e_if_i=b$. For $w=Y-L_x(Z)$ in $k(S')$ let $\nu_i=\operatorname{ord}_{D_i}(w)$, allowing negative orders. Write $D=\sum_i\nu_iD_i$. Define

$$a_i=\min(e_i,\max(0,\nu_i)),\qquad A_x=\sum_i a_iD_i,\qquad f_x=A_x\cdot\Phi_Z\le b.$$

We claim $0\le-A_x^2\le m f_x$. In fact, writing $u_i=\nu_i/e_i$ and $v_i=a_i/e_i$, the condition $D_i\cdot\Phi_x=0$ gives

$$-D\cdot A_x=\sum_{i<j}e_ie_j(D_i\cdot D_j)(u_i-u_j)(v_i-v_j).$$

The formula for $-A_x^2$ has $(v_i-v_j)^2$ as the last factor. Truncation to $[0,1]$ is nondecreasing and 1-Lipschitz, proving $-A_x^2\le-D\cdot A_x$. To bound the latter, put $\Psi=F(X,Z,L_x(Z))$. This polynomial is nonzero since $b\ge2$ and $F$ is irreducible. Divide by its exact power of $X-x$ and homogenize in $Z$ to degree $m$. The horizontal zero divisor of $w$ is bounded coefficientwise by the pullback of the resulting curve, near $\Phi_x$. Indeed at the generic point of any such zero at finite $Z$, $Y=L_x+w$ is regular, and Taylor expansion of $F=0$ gives $w\mid\Psi$ in the valuation ring. The removed power of $X-x$ is a unit there. At the generic point over $Z=\infty$ use $Z'=1/Z$, $Y'=Z'Y$ and $w'=Z'w$. The same Taylor argument for $(Z')^m F(X,1/Z',Y'/Z')$ bounds every positive order of $w$ there as $\operatorname{ord}(w')\ge\operatorname{ord}(w)$. Components over other coordinate sites are disjoint from $A_x$. In the principal divisor of $w$, the remaining pole terms only decrease the upper bound for $-D\cdot A_x$. The homogenized curve does not contain $\{x\}\times\mathbb P^1$ and its pullback intersects $A_x$ in $m f_x$, by projection. This proves the claim.

### The agreement indicator on the normalized surface

Put $I_{zx}=1$ at an agreement and $0$ elsewhere. For all but at most $mn+B_XB_Z$ pairs $(z,x)$,

$$ C'_z\cdot A_x=I_{zx}.\tag{2} $$

For the first exceptions, write the homogeneous value form at $x$ as $(Y_1-L_x(Z)Y_0)^jG_x(Z;Y_1,Y_0)$ with the greatest possible $j$. The specialized form is nonzero by primitivity. The nonzero polynomial $G_x(Z;L_x(Z),1)$ has degree at most $m$, by division by the monic affine linear factor. Discard its roots at this site. The projective root scheme is finite near every remaining $(x,z)$, since its binary form there is nonzero. The normalization maps to this scheme. Each prime fibre component maps into the received line or the zero set of $G_x$. At these points the zero set of $G_x$ avoids the received value, so a point over an agreement lies only on components on which $w$ vanishes generically, and the converse holds.

Discard also the singular points of $B$. Over its smooth points the tame cover is regular by the local Kummer description, and off $B$ it is étale. The number of singular points is bounded by the sum of the delta invariants of $B$. For a reduced curve of bidegree $(u,v)$ with $s$ components, that sum is at most $(u-1)(v-1)-1+s\le uv$, since $s\le u+v$; the empty curve has none. Thus at most $B_XB_Z$ additional pairs are discarded: each pair specifies a distinct base point. At a regular point on the cover the local intersections of $C'_z$ with the fibre components are integers. Their $e_i$-weighted sum is one because $C'_z$ maps isomorphically to its horizontal line. Thus the curve meets exactly one component, transversely, and its $e_i$ equals one. Its $a_i$ equals one exactly when $w$ vanishes on that component. This proves (2). On every discarded pair we still have $0\le C'_z\cdot A_x\le1$ because $0\le A_x\le\Phi_x$. [Abhyankar's lemma for a regular divisor](https://stacks.math.columbia.edu/tag/0EYG)

### Variance and the three-section determinant

The classes $T_x=A_x-(f_x/b)\Phi_X$ are mutually orthogonal in $\Phi_Z^\perp$, with $-T_x^2=-A_x^2\le mb$. For fixed $z$, set $v_x=T_x\cdot C'_z$. Apply Hodge index to $\sum_x v_xT_x$ and $C'_z$. It gives $(\sum_xv_x^2)^2\le c_z\sum_x v_x^2(-T_x^2)$, hence $\sum_x v_x^2\le mbc_z$. Each exceptional pair costs at most one upon replacing $C'_z\cdot A_x$ by $I_{zx}$. Therefore

$$\sum_{z,x}(I_{zx}-f_x/b)^2\le4mbB_XB_Z+mn+B_XB_Z.\tag{3}$$

If $N=0$ there is nothing left to count. Put $\theta_x=N^{-1}\sum_z I_{zx}$. The left side of (3) is at least $N\sum_x\theta_x(1-\theta_x)$, by minimizing the sum of squared deviations separately at each site. Draw three retained labels uniformly with replacement. If the first two differ, their points $(z,q_z)$ over $k(X)$ determine an affine line. It intersects $F=0$ in at most $m$ points, by substitution in the irreducible curve. Counting also the possibility of equality of the first two labels, the probability of a collinear triple is at most $(m+1)/N$. A noncollinear triple can agree jointly on at most $d$ sites, since its nonzero three-row determinant with rows $(1,z,q_z(X))$ has degree at most $d$ and vanishes at each such site. Consequently

$$\sum_x\theta_x^3\le d+(n-d)(m+1)/N,\qquad \sum_x\theta_x\ge t.$$

Using $2\theta(1-\theta)\ge\theta-\theta^3$ on $[0,1]$ in (3) gives (1), including the removed labels. This proof also covers $f_x=b$, when the centered divisor at that site is zero.

## Production specialization

Take $n=1073741824$, $d=536870911$, $e=298250000$ and $t=n-e=775491824$. Select one fold polynomial per bad scalar from the actual MCA witnesses. For a multiplicity $r$, maximum value degree $v$ and total scalar/value degree $s$, take all monomials of weight below $rt$. Their number exceeds the mixed jet constraints by

$$\sum_{j=0}^v(s-j+1)(rt-jd)_+-n\sum_{j=0}^{r-1}(r-j)(s+1-j).$$

The excess is **568,412** for $(r,v,s)=(6,8,32521)$ and **1,300,859,506** for $(12,17,98)$. Thus nonzero interpolants of both shapes contain every selected section. Remove purely scalar factors from both. The mixed jet equations survive because they are identities over the scalar polynomial domain. A remaining factor of value degree zero cannot contain a selected point over $k(X)$: a value-independent factor vanishing at a constant scalar has that scalar as a polynomial root, and has already been removed. [Mixed Hasse interpolation](../../../ArkLib/Research/ProximityGap/Frontier/HalfSuccessorJetInterpolation.lean)

Assign each selected point to one irreducible factor of the first interpolant over $k(X)$. Take its primitive integral representative. The sum of the assigned factors' value degrees is at most eight. A factor carrying more than $8\cdot98+17\cdot32521=553641$ labels divides the second interpolant as well, since its value-resultant with that interpolant otherwise has scalar degree at most this number and vanishes at each assigned label. Gauss's lemma lifts this divisibility to $k[X,Z,Y]$. Thus each large factor has $W\le6t-1$ and $m\le98$. Both primes exceed all the characteristic cutoffs in (1). For $b=2,\ldots,8$ its population bounds are, respectively,

$$10563139,\quad58759066,\quad162953260,\quad333029295,\quad570601610,\quad869227183,\quad1214617199.$$

These all exceed 553641 and so also cover the small factors.

Every value-linear factor carries at most $e+1=298250001$ labels. Indeed, suppose its population $L>e+1$. It divides the second interpolant, so has $m\le98$. At sites where substitution of the received line is not an identity, at most 98 of its labels agree. There are therefore at least $t-98n/L$ identity sites. Except at roots of the specialized coefficient of $Y$, every assigned section agrees on an identity site. That coefficient is not the zero polynomial there: if it and the constant term vanished identically, $X-x$ would divide the primitive factor. Thus the 99 sections with fewest misses each miss at most $98n/(L-98)$ identity sites, using integer parts for miss counts. Every three agree jointly on more than $d$ sites and are collinear. All 99 are on a single affine line $q_z=A+zB$, which divides the degree-at-most-98 factor and therefore equals it up to a scalar over $k(X)$. Interpolating between two polynomial sections gives $A,B\in k[X]$, each of degree at most $d$ and defined over the original field. On its joint core those two polynomials fit both rows. Each assigned MCA witness consequently needs at least one fresh agreement. Off the core at most one label agrees per site. If the core has size $c$, this gives $L\max(1,t-c)\le n-c$ and hence $L\le e+1$. [Witness and fresh-site argument](half-rate-successor-multiplicity.md#counting-the-heads)

The integer partitions of degree at most eight give total population at most $2n$, except for eight value-linear factors. The certificate enumerates all partitions. In that last case an overrun would give every factor at least $L_0=2n+1-7(e+1)=59733642$ labels. The same identity-site argument at $L_0$ puts each factor on a polynomial head, since $t-\lfloor98n/L_0\rfloor-3\lfloor98n/(L_0-98)\rfloor>d$. Each core has cardinality at least $c_0=t-\lfloor e/(L_0-1)\rfloor=775491820$.

If three of the polynomial pairs $(A_i,B_i)$ are noncollinear over $k(X)$, their nonzero determinant with rows $(1,A_i,B_i)$ has degree at most $2d$. At a site belonging to $j\ge1$ of their cores it vanishes to order at least $j-1$ by subtracting one matching row from each other matching row. Hence their total core size is at most $n+2d<3c_0$. All eight pairs are therefore collinear. Two distinct cores intersect on at most $d$ sites, by a nonzero polynomial difference. Their union alone leaves at most $n-2c_0+d=59629095$ uncovered sites.

At any covered site the evaluated pairs are collinear and one is the received pair. Every fresh agreement there selects the scalar perpendicular to its nonzero difference from the received pair, giving at most one distinct scalar. On an uncovered site each head gives at most one label. Every bad witness needs a fresh agreement on its head. Thus the total number of labels is at most $n+7\cdot59629095=1491145489<2n$, which settles the last partition. Monotonicity gives safety at all smaller counts. [Numerical certificate](../../../scripts/probes/probe_hodge_section_variance.py)
