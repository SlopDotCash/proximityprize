# An ordinary-polar proof of the second-prime cubic bound

At the last good grid count for the second prime, ordinary first polars suffice to exclude a cubic component. The auxiliary polynomial can use all value degrees allowed by its weight. Subtracting the dimension of the subspace of multiples of the cubic leaves a positive surplus. This removes interpolation with powers of the Jacobian ideal from the proof of the numerical threshold and gives a second route for its Lean verification.

Use the setup and coordinate chart of the [terminal cubic proof](second-prime-terminal-cubic.md). Put $n=2^{30}$, $d=2^{26}-1$, $t=357913943$, and take a primitive irreducible cubic-in-value component $F$ supporting at least $M=1342177249$ distinct selected polynomial sections, each with at least $t$ agreements. Its total scalar-value degree is $m\le34$ and its coordinate-value weight satisfies $3d\le W\le290805098$. The same lower population works throughout the [three-head interval](second-prime-terminal-reduction.md). The scalar-Hessian divisibility alternative has at most one label. Consider the proper-intersection case. [Lean proof of the divisibility alternative](../../../ArkLib/Research/ProximityGap/Frontier/ReverseHessianAffineSection.lean)

## Received multiplicities from two first polars

Let $J=W-d$ and $D=6W-9d-3$. For the two ordinary generic projective first polars, let $g$ denote the coordinate gcd degree of their resultants with $F$. The [ordinary Sylvester rank-loss argument](second-prime-persistent-singularities.md#a-lower-bound-for-the-persistent-intersections) gives $g\ge2J-266$. Indeed $M-164$ simple sections are available, the resultant scalar degree is at most 195, and the defect bound is $\lfloor(10W-16d-6)195/(M-164-195)\rfloor\le266$. Equivalently $g$ is the sum of the branch minima $\nu$ of the first partials, in the projective value chart at each finite coordinate place. Here and below the weighted coordinate chart chooses a regular fiber at coordinate infinity.

Let $H=F_{ZZ}F_Y^2-2F_{ZY}F_YF_Z+F_{YY}F_Z^2$. Its unnormalized homogeneous resultant with $F$ has coordinate degree at most $16W-27d$, by the Sylvester index sum. We need the following lower charges on its local intersections.

* At a branch with finite ordinate use a parametrization $X=X(t),Y=Y(t)$ in power series over a separable coefficient extension of $k(Z)$. Differentiate coefficients with respect to $Z$ holding $t$ fixed. The equation gives $F_Z=-F_X\dot X-F_Y\dot Y$. Both dotted series are regular. Thus $F_Z$ and $F_Y$ both vanish to order at least $\nu=\min(vF_X,vF_Y)$. The three monomials of $H$ give $vH\ge2\nu$. [Lean ideal-square identity](../../../ArkLib/Research/ProximityGap/Frontier/BranchHessianIdeal.lean)
* At a received site $x$, choose $X=x+t^e$ on a branch through the affine received ordinate $L_x$. This choice uses tameness and $x$ is constant. If $s=\min(e,v(Y-L_x))$ and $j=vF_Y$, differentiation holding $X$ fixed preserves $v(Y-L_x)$ as a lower bound and $L_x''=0$. The implicit identity gives $vH\ge3j+s\ge3\nu+s$. At a point of two-variable multiplicity $r$, both first partials have local order at least $r-1$, hence $\nu\ge s(r-1)$. The extra charge beyond $2\nu$ is at least $sr$. Summing $s$ over the branches through that received point gives $r$, so its total extra charge is at least $r^2\ge3r-2$. The inequality also holds for an absent received point with $r=0$.
* At a branch at value infinity write $T=1/Y$, $S=T^3F(1/T)$, and $f=vT>0$. The homogeneous first polars have minimum $\nu=\min(vS_X,v(T^2S_T))$ modulo $S$. Set $h=\min(vS_X,vS_T)$. Coefficientwise differentiation of $S=0$ gives $vS_Z\ge h$ just as at a finite ordinate. The homogeneous Hessian on this chart is $2T S_T S_Z^2+T^2 H(S)$ modulo $S$. Every term has order at least $2h\ge2\nu-4f$. These inequalities need only the reciprocal polynomial identity and regular series. The sum of $f$ across the poles at finite coordinates is at most $W-3d$, the degree bound of the leading value coefficient. This follows by the proper intersection with $T=0$, or by the norm in a local monic chart. [Reciprocal identity and projective intersection](second-prime-normalized-hessian.md#a-projective-resultant-with-its-leading-coefficient-factor-removed)

Writing $R=\sum_x r_x$ and summing the charges in the nonzero raw resultant gives
$$
3R\le2n+(16W-27d)-2g+4(W-3d)
    \le2n+16W-35d+532.
$$
This estimate allows a loss of four times the pole order. It needs neither the sharp $8\nu/3$ estimate at a moving singularity nor division of the universal Hessian determinant by its leading-coefficient factor. The branch parametrization and the local intersection formula are still geometric inputs. [Tame charts and branch orders](second-prime-persistent-singularities.md#local-charges-for-the-two-derivatives) · [Fixed received ordinate in Lean](../../../ArkLib/Research/ProximityGap/Frontier/TameBranchDerivative.lean)

## Interpolation modulo the cubic

Set $\mu=32$, $s=400000000$, $U=\mu t$, and $J_0=\lfloor(U-1)/d\rfloor=170$. Take all monomials $X^iY^j Z^h$ with $i+dj<U$ and $j+h\le s$. With $S(V)=\sum_{j\ge0}(V-jd)_+$, the dimension is at least $(s+1)S(U)-J_0S(U)$. A multiple $FQ$ in this space has $Q$ of weight below $U-W$ and scalar degree at most $s$. This uses additivity of weighted degree and of scalar degree over the polynomial domain. Gauss's lemma lifts divisibility over $k(X)[Z,Y]$ to integral divisibility by the primitive $F$. Thus the dimension of all such multiples is at most $(s+1)S(U-W)$. The function $(U-dx)_+-(U-W-dx)_+$ on $x\ge0$ is nonincreasing. Its integral gives
$$
S(U)-S(U-W)\ge (2UW-W^2)/(2d).
$$

At each site impose the polynomial-multiplier condition on the full translated $(X,Y)$ jet of order $\mu$ as in the [intrinsic interpolation proof](second-prime-intrinsic-cubic.md). Translation by a received affine function of $Z$ sends each source monomial to scalar degree at most $s$. With column degree padded to 34, the total net codimension is at most
$$
(s+1-34)((\mu-1)R+n)+34n\binom{\mu+1}{2}.
$$
The independent multiplier columns make projection onto the auxiliary polynomial injective on the simultaneous solution space. Subtract the displayed net cost and the dimension bound for all multiples of $F$. The resulting lower bound
$$
(s+1)\frac{2UW-W^2}{2d}-J_0S(U)
 -(s+1-34)\left((\mu-1)\frac{2n+16W-35d+532}{3}+n\right)
 -34n\binom{\mu+1}{2}
$$
is concave in $W$. At $3d$ and $290805098$ its floors are respectively **711166579242392977** and **770819534513414215**. Hence there is a jet solution outside the multiple subspace for every allowed weight. Its specialization at each section vanishes at all agreements with multiplicity at least $\mu$ and has degree strictly below $\mu t$. The nonzero scalar resultant with $F$ consequently has at least $M$ distinct roots. Its degree is at most $3s+34J_0=1200005780<M$. This contradiction excludes the cubic. [Exact arithmetic](../../../scripts/probes/probe_second_prime_unrestricted_jets.py) · [Lean slot inequality and production surplus](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeUnrestrictedJetBudget.lean)

## A residual determinant for the ordinary polar bound

Write $A,B\in k[Z][X]$ for the two polar resultants after the coordinate change. Both have coordinate degree $D$ and scalar height at most 195. Take the primitive integral representative $E$ of their gcd over $k(Z)[X]$ and write $A=EF$, $B=EG$. Put $g=\deg_XE$ and $u=D-g$. The residuals have coordinate degree $u$, scalar height at most 195, and are coprime over $k(Z)$. Their nonzero coordinate resultant therefore has scalar degree at most $390u$.

On each selected simple section, let $q=F_Y(X,z,q_z)$ denote the value partial of the original cubic, of coordinate degree $J$. Both specialized ordinary polar resultants are divisible by $q^2$. The linear section factor supplies one copy. For the residual factor of the cubic, evaluation of its Bézout identity with the polar at the same section supplies the second copy. Gauss's lemma ensures $E_z\ne0$ for every $z$. After removing $E_z$, the specialized residuals thus have a common divisor of degree at least $2J-g$ when this is positive. If both residuals vanish, the entire specialized Sylvester matrix vanishes. In either case the residual resultant vanishes at $z$ to order at least $2J-g$. A direct proof of this last assertion reduces the specialized Sylvester matrix to rank normal form over the scalar field. Each column in its null block supplies one factor of $Z-z$ in the determinant. A common monic degree-$h$ factor cuts at least $h$ dimensions from the range since the Sylvester image is zero modulo that factor.

Summing over the $M_1\ge1342177085$ simple labels yields
$$
M_1(2J-g)\le390(D-g).
$$
For $g<2J$ this strengthens the defect bound from 266 to **201**, using $D=6W-9d-3$ and $W\le290805098$. The previous numerical surplus therefore still applies. Lean proves the inequality for the actual pair of bivariate polars from their stated degree bounds and the square divisors at the simple sections. [Integral factor and coprime residuals](../../../ArkLib/Research/ProximityGap/Frontier/IntegralCommonPolar.lean) · [Section divisibility and rank loss](../../../ArkLib/Research/ProximityGap/Frontier/OrdinaryPolarRankLoss.lean) · [Generic gcd bound](../../../ArkLib/Research/ProximityGap/Frontier/OrdinaryPolarGcdBudget.lean)

For a related computational treatment of Puiseux expansions and resultant valuations over perfect coefficient fields, see Poteaux and Weimann. Their perfect-field assumption differs from the scalar function field used here. The formal cubic splitting argument uses only separably closed constants and invertibility of two and three. [Poteaux and Weimann](https://arxiv.org/abs/1708.09067) · [Separably closed cubic splitting](../../../ArkLib/Research/ProximityGap/Frontier/TameCubicPowerSeries.lean)

## One homogeneous Hessian estimate at finite values and poles

Write the binary cubic as $P(X,Z;B,A)=A^3 F(X,Z,B/A)$ and take a projective branch $[B:A]$ after $X=x_0+t^6$. Its power series coefficients carry the scalar derivation $D$ fixing $t$. Put $U=P_X$ and $V=A P_B$. On the branch, differentiating $P=0$ and using Euler's identity $BP_B+AP_A=3P=0$ gives
$$
A^2P_Z=-A^2 U\,DX+(B\,DA-A\,DB)V,\qquad A^2P_B=A V.
$$
The homogeneous lift of the raw scalar Hessian to degree seven is
$$
H=P_{ZZ}P_B^2-2P_{ZB}P_B P_Z+P_{BB}P_Z^2 .
$$
Consequently $A^4H$ belongs to $(U,V)^2$. Writing $v$ for the power series order and $\nu=\min(v(U),v(V))$ gives $v(H)\ge 2\nu-4v(A)$ on every sheet. Choose the chart with at least one unit coordinate on each sheet. The total pole cost is bounded directly by the resultant formula with the constant test polynomial $1$ taken at nominal degree one. Its homogeneous value is $A$, and its resultant is the leading coefficient of the cubic. Summed over finite base points, this gives $\sum v(A)\le 6\deg_X(\operatorname{lc}_Y F)$. This supplies the finite and pole baseline in the ordinary-polar proof with a single calculation. At received affine sites the stronger order follows by differentiating an actual power series root twice. [Received-site derivative](../../../ArkLib/Research/ProximityGap/Frontier/ReceivedPowerSeriesHessian.lean) · [Projective order formula](../../../ArkLib/Research/ProximityGap/Frontier/ProjectiveCubicLocalOrder.lean) [Kernel-checked projective Hessian identity](../../../ArkLib/Research/ProximityGap/Frontier/ProjectiveBranchHessian.lean)
