# Root products of a three-fiber pencil

Let $L_S=\prod_{s\in S}(X-s)$. Suppose $A,B,D$ are disjoint subsets of a multiplicative grid, all of size $m$, and
$$
 L_A-cL_B=(1-c)L_D,\qquad c\ne0,1.
$$
Thus $A,B,D$ are the complete simple fibers of $L_A/L_B$ at $0,\infty,c$. Write $\alpha,\beta,\gamma$ for their respective products. Evaluating at zero gives $\alpha-c\beta=(1-c)\gamma$. The three products are either all equal or pairwise distinct. In the latter case
$$
 c=(\alpha-\gamma)/(\beta-\gamma).
$$
For each $x\in D$, multiply the numerator of the ratio by $X-x\beta/\gamma$ and its denominator by $X-x\alpha/\gamma$. The corrected ratio equals **one** at $x$, and its numerator and denominator have equal degrees and equal root products. The extra sites differ from $x$ and from each other. Its signed weight has squared norm at most $2m+6$, since adding one positive and one negative unit to a vector in $\{-1,0,1\}$ adds at most six to the squared norm. [Lean product and center identities](../../../ArkLib/Research/ProximityGap/Frontier/SplitPencilRootProducts.lean)

## Reflection distance and the first production endpoint

For an odd-degree pencil on a dyadic multiplicative grid in odd characteristic, fix any grid element $r$. The map $x\mapsto r/x$ has two distinct fixed points in the algebraic closure. Let $k$ count those in $A\cup B\cup D$. Count a site as lost when its reflection leaves its original fiber. Then
$$
 \mathrm{lost}\ \ge\ m+2-k+2\,1_{\alpha=\beta=\gamma}.
$$
Indeed the polynomial
$$
 Q(X)=X^m\big[L_A(r/X)L_B(X)-L_B(r/X)L_A(X)\big]
$$
has degree at most $2m$. If it were zero, the reflection would preserve each of the three complete simple fibers. Each invariant odd-size fiber needs a fixed point, while the reflection has just two. Every preserved site and both fixed points are roots. When all three products coincide, the coefficient at degree $2m$ vanishes by equality of the two constant coefficients. At zero the reflected polynomials both have value $r^m$, so zero is another root of $Q$. The Lean bound applies after extending coefficients to the algebraic closure and taking the union of preserved sites and fixed points there. [Lean mirror-site bound](../../../ArkLib/Research/ProximityGap/Frontier/SplitPencilRootProducts.lean)

At the first-prime production endpoint the two protected degree-$m=268435455$ pencils each obey this bound. For every odd-exponent $r$, no grid element squares to $r$, so each pencil loses at least 268,435,457 sites, or 268,435,459 if its products coincide. This counts its three marked fibers, including the private sites. [Endpoint pencil and fiber table](half-four-fiber-parity.md#six-protected-divisor-signatures)

There are additional restrictions when several pencils have coincident products. Write $P_i=\prod U_i$ for the products of the private site classes in that table.

* In the one-triple shape at least one of the two pencils has three different products. Coincidence for both would give $P_1d=P_0=P_1c$ for two different marked sites $c,d$.
* In the five-double shape coincidence for both implies $P_0b=P_1d$ and $P_0a=P_1c$, hence $bc=ad$.
* In the six-double shape consider all four pencils obtained by omitting one head. If all four have coincident products, let $s_{ij}$ be the six double sites with missed heads $i,j$. For each omitted head $\ell$ there is a common $K_\ell=P_i s_{i\ell}$ for $i\ne\ell$. Symmetry gives $P_iK_i=T$ independent of $i$. Hence $s_{ij}=T/(P_iP_j)$ and every perfect matching of the six sites has the same product $C_0=T^2/\prod_iP_i$. The full dyadic grid has product $-1$. For puncture $z$ and all-agree site $v$ this gives $zv=-1/(TC_0)^2$. Since $-1$ is a grid square at this length, $z$ and $v$ have the same exponent parity.

## A complete antipodal pair at length 256

Consider either of the two named prime fields and its order-256 grid. Assume $m\le63$ and $\alpha,\beta,\gamma$ are pairwise distinct. If $D$ contains a pair $x,-x$, either all three products have the same exponent parity, or **$\gamma$ is the unique parity outlier and $\alpha\beta=\gamma^2$**. Accordingly, if two different fibers each contain an antipodal pair, all three products have the same parity. When the parities are mixed and none of the three products is the multiplicative midpoint of the other two, all three fibers contain at most one point of every antipodal pair.

Here is the calculation. Take a primitive $z$ of order 256, put $u=z^2$ and $y=x^2$. Fold the signed indicator $1_A-1_B$ onto the order-128 grid by adding the weights at antipodes. The resulting $s$ has mass zero, $|s_j|\le2$, $\sum|s_j|\le2m$ and $\sum s_j^2\le4m\le252$. The quotient $S(y)=\prod_j(y-u^j)^{s_j}$ equals $c^2$ by multiplying the two evaluations. Its root-product ratio is $(\alpha/\beta)^2$. Formally substituting $z^{-1}$ for $z$ in the product, including its center, multiplies its value by $(\beta/\alpha)^2$. Making the same substitution in the chord defining $c$ multiplies $c$ by $\beta/\alpha$. Both statements follow by factoring each inverted difference individually, so they apply in the original prime field.

Translate the quotient center to one and index the other 127 sites by $j=1,\ldots,127$. Put $\beta_N(j)=(1-z_N^j)(1-z_N^{-j})$ for $z_{256}=z$, $z_{128}=u$. For odd $r<64$ let $M_{rj}$ count occurrences of $j=\pm2^k r\bmod128$, $0\le k\le6$, with both signs counted. The usual factorization $1-t^2=(1-t)(1+t)$ gives the primitive-unit exponents $e=Ms$. The norm of the single-center equality gives
$$
 \prod_{r}\beta_{128}(r)^{e_r}
 =\big[\beta_{256}(a)/\beta_{256}(b)\big]^2,
 \qquad z^a=\alpha/\gamma,\quad z^b=\beta/\gamma .
$$
Translation preserves the balanced product and does not change the exponents $a,b$. Absolute indices $1,\ldots,128$ suffice on the right since each $\beta_N$ is invariant under sign. Exchanging $a,b$ negates both sides in logarithms. Remove the both-even choices and equal absolute indices. The remaining $\binom{128}2-\binom{64}2=6112$ targets per prime cover every mixed-parity choice except $a=-b\bmod256$. In that last case $\alpha\beta=\gamma^2$ and $c=-\alpha/\gamma$.

The exact search uses the primitive unit logs in both named fields. Balancing the 127 source columns gives covariance $C=127MM^\top-(M\mathbf1)(M\mathbf1)^\top$. Every source of the stated squared norm satisfies $127e^\top C^{-1}e\le252$ by orthogonal projection onto the zero-mass subspace. In each congruence class solve for one representative by Bézout, reduce its coordinates modulo the homogeneous kernel basis, and enumerate the translated ellipsoid. Its Gram–Schmidt enclosure also works for a fractional translate $r_i\in[-1/2,1/2]$. Add the rounded row offset $2^{15}r_i+\sum_{j>i}a_{ji}r_j$ before enumeration and allow 33 extra units of rounding error per row. Every final point is tested against the exact rational Gram form. [Integer enclosure proof](mu128-balanced-weight-two.md) · [Full verifier](../../../scripts/probes/probe_mu256_pencil_chord.py)

| Field | Distinct targets | Total ellipsoid points | Lower bounds on maximum source weight at surviving points |
|---|---:|---:|---|
| First | 6,112 | 2 | $3,3$ |
| Second | 6,112 | 5 | $5/2,7/2,13/4,13/4,11/4$ |

The signed orientation for each target uses the smaller of its two log residues. In the first field the surviving pairs of absolute indices are $(23,71),(57,105)$. In the second they are $(5,49),(63,23),(79,7),(121,49),(79,123)$. Each displayed lower bound comes from an integer vector $(v,t)$ with $v\cdot e>2\sum_j|(vM)_j+t|$. This would be impossible if $Ms=e,\sum s_j=0,|s_j|\le2$. The enumeration gives the same counts starting from reversed bases. [Seven separation certificates](../../../scripts/probes/mu256_pencil_chord_certificates.json)

Furthermore **each eligible antipodal pair gives its prescribed single-center identity over the complex numbers**. For equal product parity, $\alpha/\gamma,\beta/\gamma\in\mu_{128}$. Add $+2,-2$ to the folded weights at $y\beta/\gamma,y\alpha/\gamma$ respectively. The corrected ratio has value one, mass zero, product ratio one and energy at most $252+24=276$. Its exponents therefore obey the homogeneous norm congruence. For the geometric case, the norm of the prescribed $c^2$ already equals one, so use the uncorrected weights with energy at most 252. The verifier checks that the homogeneous kernel has just the zero exponent in the ellipsoid for $MM^\top$ of energy 384 in both fields. Once the primitive-unit exponents vanish, the remaining ratio is a root of unity of order dividing 256. Its finite reduction is injective on these roots, so the asserted identity holds for the corresponding complex representatives. This gives the folded equality $S(y)=c^2$ even with a single tested pair. A pencil whose three products coincide does not prescribe $c$ by its products and lies outside this calculation.

Run `uv run --no-project --with python-flint python scripts/probes/probe_mu256_pencil_chord.py`, and append `--reverse-basis` for the second traversal.
