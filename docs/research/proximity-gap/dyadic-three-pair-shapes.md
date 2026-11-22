# Three transpositions on dyadic roots

Let $H$ consist of the complex $2^m$-th roots of unity. A non-dihedral involution exchanging three disjoint pairs in $H$ has one of the following two forms for its matched sites.

* One pair is $(u,-u)$. The remaining two are $(a,b)$ and $(u^2/a,u^2/b)$.
* Three sites $u,v,w$ have partners $-vw/u,-uw/v,-uv/w$, respectively.

The same configurations describe three prescribed disjoint transpositions in a split prime field when $p^2>12^{\varphi(2^m)}$. That implication uses the three-row pair determinant transfer and the fact that identities between dyadic powers transfer back unchanged. The classification below uses an exact integer calculation over **all** dyadic orders. The Lean seven-site theorem establishes the four-pair exclusion independently. [Integer certificate](../../../scripts/probes/probe_dyadic_three_pair_shapes.py) · [Seven-site theorem](../../../ArkLib/Research/ProximityGap/Frontier/DyadicSevenProjectivities.lean)

## The integer certificate

Number the six endpoints in pair order. A trace-zero matrix exchanges the endpoints of a pair $(x,y)$ only if $cxy-a(x+y)=b$. The determinant of the three rows $(1,x+y,xy)$ must vanish. Its expansion has twelve signed monomials. Rotate all six sites to put the first at 1. In the additive group of dyadic rational numbers modulo 1, five unknowns then specify the other sites. Write $h=1/2$ for the exponent of $-1$.

At order $2^m$ the minimal polynomial is $X^{2^{m-1}}+1$ for $m>0$. A sum of dyadic roots vanishes exactly when each term can be paired with its negative. Order one supplies no six distinct sites. The twelve signed terms have $11\cdot9\cdot7\cdot5\cdot3=10,395$ possible matchings. Each matching imposes six integer linear equations in the five unknowns. An equation has right-hand side $h$ when its two monomial signs agree and zero otherwise.

The certificate diagonalizes each matrix using unimodular row and column operations. It checks the two change-of-basis determinants and their matrix product against the original equations. For a nonzero diagonal coefficient $a=2^s b$ with $b$ odd, an equation $a t=c/2$ modulo 1 permits exactly $2^s$ dyadic values of $t$. They are $(c\bmod2+2j)/2^{s+1}$ for $0\le j<2^s$, since odd multiplication permutes this set. Unconstrained coordinates stay free. Substituting back gives the six exponents as affine functions of those free coordinates. The certificate checks an identity on such a family by comparing the constant modulo its denominator and every integer coefficient exactly.

There are 15,491 components with repeated sites, 67 with three antipodal pairs, 34 with a common pair product, 282 of the first displayed form, and 56 of the second. The categories are checked in that order. Components from different matchings can overlap. A common pair product forces reciprocal scaling, while three antipodal pairs force negation, by uniqueness of a projectivity on three sites. This proves exhaustiveness. In the second form put $S_1=u+v+w$, $S_2=uv+vw+wu$ and $S_3=uvw$. The trace-zero matrix with $a=S_3,b=-S_1S_3,c=S_2$ exchanges all three pairs. Its nondegeneracy test is $a^2+bc=-uvw(u+v)(u+w)(v+w)$. These coefficient identities hold over any field.

## A uniform weighted penalty

Use the weighting of the two-error slice with a nonantipodal anchor pair $(1,s)$ and $f(x)=(x-1)/(x-s)$. The reflection target has cost at most three and is met by at most one tested site for each nonzero scale $\mu$. Every other target of positive cost has exactly two alternative pairs by seven-site rigidity. It costs one. [Weight convention](dyadic128-two-error-slices.md)

In the antipodal form write $v=t^2$ for the square of one antipodal endpoint. Its target is $T=(v-1)/(v-s^2)$. The condition $T f(x)=\mu$ makes $x$ a projective function of $v$ with numerator $(s\mu-1)v+1-s^3\mu$ and denominator $(\mu-1)v+1-s^2\mu$. This map is nonsingular since $s^2\ne1$ and $\mu\ne0$. A scaling would require $s^3=1$ and a reciprocal scaling would require $s=1$. A nontrivial dyadic root has neither property. At most six values of $x$ occur.

In the other form, orient the anchor so that the first endpoint is one of $u,v,w$. Either orientation is allowed, with $s$ inverted and $\mu$ inverted when the two anchors are swapped and renormalized. The other two heads are $t$ and $-s/t$. They are distinct. One other pair is $(t,s/t^2)$. With $Z=t-s/t$, its target is
$$
T=\frac{Z}{s(Z+1-s)},\qquad
x=\frac{(s^2\mu-1)Z+s^2\mu(1-s)}{(s\mu-1)Z+s\mu(1-s)}=M(Z).
$$
The fractional-linear map $M$ is nonsingular. Its two constant coefficients are nonzero. A realized positive target has $Z\ne0$.

For clarity, the parity argument works for any rational function $R$ of degree $d$ on a dyadic grid. Call a matched site $t$ exceptional when $R(-t)=R(t)$ or $R(-t)=-R(t)$. There are at most $8d$ **nonexceptional** matched input sites. Otherwise one of the four source and target parity classes contains $2d+1$ of them. Rotate source and target independently to make that class even in both coordinates. The cyclotomic automorphism taking the primitive root to its negative fixes these $2d+1$ matches. The function and its conjugate agree there and therefore agree identically by cross multiplication. For the present application all coefficients lie in the cyclotomic field, since any occupied scale is itself a product of three ratios. An even input now has even output. Any odd input would satisfy $R(-t)=\pm R(t)$. Every nonexceptional match therefore lies on the half-sized grid in both coordinates. Repeat. Rotations preserve both exceptional tests, so the same oversized set would survive down to a one-point grid.

Apply that argument at degree two to $R(t)=M(t-s/t)$. Both $t$ and $-s/t$ give the same $x$ and have identical exceptional status. Thus at most eight outputs can come from nonexceptional sites. For $Z\ne0$ injectivity of $M$ precludes $M(-Z)=M(Z)$. Writing $M=(AZ+B)/(CZ+D)$, the equation $M(-Z)=-M(Z)$ gives $ACZ^2=BD$. Since $BD\ne0$, at most two outputs come from exceptional sites. Each anchor orientation therefore costs at most ten. Adding the three contributions gives the uniform **29-unit** bound for every dyadic length in characteristic zero.

The same 29-unit bound follows over a split prime field under $2^{7\varphi(n)}<p^2$. Fix a tested scale with at least one positive record. Transport its value to the complex grid using one realizing product of three ratios. Three-factor transfer makes all other records at this scale agree there, and two-factor transfer retains each alternative pair. Distinct tested sites stay distinct and the penalty is monotone in the number of alternatives. This exponential field-size hypothesis leaves the named production fields open. At order 128 the sharper finite histogram supplies twelve. [Ratio transfer in Lean](../../../ArkLib/Research/ProximityGap/Frontier/RatioProductNorm.lean)

At dyadic lengths at least 256 the triple-transfer hypothesis already gives $p/2^{128}>2^n$, above the elementary capacity-window budget. The 29-unit result still bounds the list at other tolerances. At length 64 the same height hypothesis allows a nonempty 128-bit budget interval. The individual bounds of six and ten have Lean proofs, as do the general $8d$ and nonsymmetric $12d$ estimates. [Weighted geometry](../../../ArkLib/Research/ProximityGap/Frontier/DyadicWeightedRowGeometry.lean) · [General rational graph bound](../../../ArkLib/Research/ProximityGap/Frontier/DyadicRationalParity.lean)
