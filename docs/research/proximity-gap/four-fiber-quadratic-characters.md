# Four protected fibers and a binary character test

At five errors on the sixteen nonzero elements of `ZMod 17`, a pair of received words makes **every one of the seventeen scalars MCA-bad** for dimension eight. The same four polynomials give **eighteen** bad scalars over every proper extension of this base field. The example also checks a necessary binary test involving all four private error sets of a complete four-head overlap graph. For either named production prime the convolution appearing in this test has precisely six kernel dimensions before the diagonal corrections.

## The explicit sixteen-site words

Write $L_A=\prod_{a\in A}(X-a)$. On the fifteen sites other than 1, use a word $v$ taking values $2,10,4,3,1$ at $2,3,4,5,14$, respectively, and zero elsewhere. Each of the following scalar head polynomials agrees with $v$ at precisely ten sites.

| Head | Polynomial | Private error sites |
|---|---|---|
| 0 | $0$ | $5,14$ |
| 1 | $L_{\{8,10,11,12,13,16\}}$ | $7,15$ |
| 2 | $11L_{\{7,8,9,10,15,16\}}$ | $11,12$ |
| 3 | $5L_{\{6,7,8,11,12,15\}}$ | $10,16$ |

The remaining sites with errors are the six pair overlaps. The pairs $02,03,12,13,01,23$ occur at $2,3,6,9,4,13$ in that order. All four agree at 8. At the hole 1 the four head values are $0,8,4,11$.

At ordinary sites $x$ set the two received values to $(v(x),(x-1)v(x))$ and set the values at 1 to $(0,8)$. For a head $D$ the codeword pair is $(D,(X-1)D)$ of degrees below eight. Its ten common sites determine each component uniquely. An eleventh site matching the scalar combination and disagreeing on the pair therefore certifies the literal bad event on that eleven-site set.

Each of the fourteen ordinary sites outside $\{1,8\}$ gives the fresh scalar $-1/(x-1)$. Their complement in $\mathbf F_{17}$ is $\{0,1,12\}$. At 1 the four labels are $D(1)/8=0,1,9,12$, which supply all three. This gives $\varepsilon_{\rm MCA}=1$ at radius $5/16$. The pinned Lean kernel checks both base-field declarations with the three standard axioms, and independent `con-leche --verified` accepted their 25,516 transitive declarations. At $4/16$ the pinned code already has exact worst-case probability $15/17$. [Four-error theorem](../../../ArkLib/Research/ProximityGap/Frontier/SmoothQuinticSeventeen.lean) · [Five-error witness](../../../ArkLib/Research/ProximityGap/Frontier/SmoothSeventeenFiveErrors.lean)

In any proper extension choose $b\notin\mathbf F_{17}$ and use $(b,1)$ at 1. The fourteen ordinary labels stay in the prime subfield and the four distinct hole labels $D(1)-b$ all lie outside it. The ten-site uniqueness argument also works over the extension. This supplies eighteen distinct literal bad labels on the prescribed order-sixteen subgroup.

## Four fibers with six distinct overlaps

Suppose the four private sets $U_0,U_1,U_2,U_3$ are disjoint and have size $h-2$ in a subgroup $H$ of order $n=4h$. Write $a,b,c,d,e,f$ for six other distinct sites, the overlaps $02,03,12,13,01,23$ respectively. The configurations considered here have one uncovered site and one site where all four heads agree. Let $O=\bigcup U_i$, so the eight other sites are specified independently of their partition.

Two shared-edge triangles force pencils of the form
$$
 F=\alpha\frac{L_{U_0}(X-b)}{L_{U_1}(X-d)},\qquad
 G=\gamma\frac{L_{U_0}(X-a)}{L_{U_1}(X-c)}
$$
with $F=1$ on $U_2\cup\{f\}$ and $G=1$ on $U_3\cup\{f\}$. All these fibers have degree $h-1$ and are simple. In particular $F-1$ and $G-1$ have the indicated monic vanisher numerators up to nonzero constants. Write $R=F/G$. Its constant multiplier in
$$
 R=\kappa\frac{(X-b)(X-c)}{(X-a)(X-d)}
$$
is fixed by $R(f)=1$. For heads $D_i$ the normalized functions are $(D_2-D_1)/(D_2-D_0)$ and $(D_3-D_1)/(D_3-D_0)$. At $e$ the second and third indexed heads agree, so $R(e)=1$ as well. For the test below it suffices that $R$ and $1-R$ are units at every point of $O$.

Take the squarefree representative $D$ of the square class of $F(F-1)(F-R)$, keeping its constant square class, over an odd prime field. Because $F-R=R(G-1)$, direct cancellation gives the following finite supports modulo even multiplicity.

| Square class | Odd finite valuations |
|---|---|
| $D$ | $O\cup\{a,d\}$ |
| $D F$ | $U_2\cup U_3\cup\{a,b\}$ |
| $D(F-1)$ | $U_0\cup U_3\cup\{a,f\}$ |

In particular the twist polynomial is determined by the marked sites up to its constant square class. Let $x_s,y_s\in\mathbf F_2$ be the support indicators of $DF,D(F-1)$ at all $s\in H$. The pairs on $U_0,U_1,U_2,U_3$ are respectively $(0,1),(0,0),(1,0),(1,1)$. All eight exceptional pairs are known from the table.

Write $[v]$ for the quadratic character in additive notation ($0$ for a nonzero square). At $s\in O$ put $\delta_s=[D'(s)]$, $\rho_s=[R(s)]$, $\sigma_s=[1-R(s)]$, and $L_{s,u}=[s-u]$ for $s\ne u$, with zero diagonal. There are two field-constant bits $b_0,b_1$ such that every regular site satisfies
$$
 b_0+\sum_u L_{s,u}x_u=\delta_s x_s+\rho_s y_s,\qquad
 b_1+\sum_u L_{s,u}y_u=\sigma_s x_s+(\delta_s+[-1])y_s .
$$

To see this, remove the local uniformizer power in each of $DF,D(F-1),D(F-R)$ and take its residue character. The three characters add to zero since the product is a square. At a simple pole of $F$ their residues coincide, making all three zero in additive character notation. At a zero of $F$, the last two units have residues $-D'(s)$ and $-D'(s)R(s)$. At a site with $F=1$, the first and third have residues $D'(s)$ and $D'(s)(1-R(s))$. At a site with $F=R$ the first and second are $D'(s)R(s)$ and $D'(s)(R(s)-1)$. These are exactly the four right-hand sides. On the left, the squarefree representative is its leading constant times the product of simple marked factors, giving the displayed sums.

For each marking and each choice of the constant character of $D$, this is an affine linear system over $\mathbf F_2$. The four possible ordinary colors must each occur precisely $h-2$ times. On $\mu_{16}\subset\mathbf F_{17}$ fix $(a,b,c,d,e,f)=(2,3,6,9,4,13)$ and hole 1. There are 2,520 balanced partitions per marking. An all-agree site of 5 leaves **zero** partitions; an all-agree site of 8 leaves **one**, precisely the genuine example above; an all-agree site of 16 leaves **two** and both fail the original pencil equations. [Exact exhaustive finite check](../../../scripts/probes/probe_four_fiber_quadratic_characters.py)

## Exact rank of the common convolution at both production primes

Take $H=\langle g\rangle$, $n=2^{30}$. Set $K_0=0$ and $K_j=[1-g^j]$ for $j\ne0$. Then for $i\ne j$ one has $L_{g^i,g^j}=[g^i]+K_{j-i}$. At the first prime $[g]=0$. At the second prime $[g]=1$, so the extra row-constant and diagonal terms are required. In either case the pure circulant with kernel $K$ has rank **1,073,741,818**.

Indeed its rank is $n-v_{X+1}(\sum K_jX^j)$ since $X^n-1=(X+1)^n$ over $\mathbf F_2$ (index reversal preserves rank). For $0<r<8$, the product of $1-g^j$ over $j\equiv r\pmod 8$ is $1-g^{rn/8}$. For $r=0$ omit the zero exponent, giving product $n/8$ by differentiating $X^{n/8}-1$. These eight characters give the reduction of the kernel modulo $X^8-1=(X+1)^8$. At both primes its Hasse coefficients of orders zero through seven are $(0,0,0,0,0,0,1,1)$. Thus the nullity is precisely six. The coupled matrices also contain the marking-dependent diagonal terms shown above. Their production ranks and balanced solutions remain open. [Exact modular arithmetic](../../../scripts/probes/probe_four_fiber_quadratic_characters.py)

## The stronger fourth-power test

For $p\equiv1\pmod4$ use the additive quartic character $[\ ]_4$ valued in $\mathbb Z/4$. The valuations of $F(F-1)(F-R)$ at the four colors are $1,-3,1,1$, all congruent modulo four. Up to a field constant, its fourth-power class is represented by
$$
 D_4=L_O(X-b)^2(X-f)^2(X-d)(X-a)^3.
$$
Write $\delta_s$ for the quartic log of its unit at $s\in O$, including an unknown constant. Write $\eta=[-1]_4$, $\rho_s=[R(s)]_4$, $\sigma_s=[1-R(s)]_4$. For each ordinary site strip the local uniformizer powers from $F$ and $F-1$ and take the two leading quartic logs. Their necessary values are

| Color | Leading log of $F$ | Leading log of $F-1$ |
|---|---|---|
| $U_0$ | $\delta_s-2\eta-\rho_s$ | $\eta$ |
| $U_1$ | $-\delta_s$ | $-\delta_s$ |
| $U_2$ | $0$ | $\delta_s-\sigma_s$ |
| $U_3$ | $\rho_s$ | $\eta+\sigma_s$ |

For $U_1$ the three equal leading logs of $F,F-1,F-R$ sum to $\delta_s$, and the inverse of three modulo four is minus one. At the other three colors two of the three residues are actual evaluations at $0,1,R(s)$, respectively, so the product determines the third log. On the left the first two logs are obtained from $\alpha L_{U_0}(X-b)/(L_{U_1}(X-d))$ and $\beta L_{U_2}(X-f)/(L_{U_1}(X-d))$, omitting a root at $s$ itself. For each of the four possible twist constants, both sides are affine-linear over $\mathbb Z/4$ in four ordinary indicator vectors. At every site these indicators take exactly one 1, and all four supports have the prescribed size. The two additional constants $[\alpha]_4,[\beta]_4$ are common to every site.

The fourth-power test rejects **both** spurious partitions at all-agree site 16 in the quadratic control, and accepts the genuine survivor at 8. Four is the largest order supported by this equal-exponent mechanism. Indeed a product with exponents $a,b,c$ on $F,F-1,F-R$ has valuation vector $(a,-a-b-c,b,c)$ on the four colors. Equality forces $a=b=c$ and $4a=0$ in the chosen character group. [Quartic control](../../../scripts/probes/probe_four_fiber_quadratic_characters.py)

The pure quartic convolution at either named prime has Smith form over $\mathbb Z/4$ consisting of $n-6$ units and six zeros. To see this, let $T$ denote the quartic convolution and $\bar T$ its binary reduction. Every binary kernel element is a multiple of $(X+1)^{n-6}$, so it is 8-periodic, because $(X+1)^{n-8}=1+X^8+\cdots+X^{n-8}$. Lift its period to an 8-periodic vector $v$ over $\mathbb Z/4$. Then $Tv$ is even and 8-periodic, hence $Tv/2$ modulo two is a multiple of $(X+1)^{n-8}$. In particular $Tv/2$ lies in the image of $\bar T$, the ideal $((X+1)^6)$. Correcting $v$ by twice a preimage lifts the binary kernel element to a quartic kernel element. No Smith factor equal to two permits such a lift on its binary coordinate, proving the claim. This also gives exactly $4^6$ quartic kernel vectors before the marking-dependent terms are included.

## The other two overlap patterns

The four-fiber character equations cover all three possibilities of the punctured-list classification. The symbols $F,G,R,O,U_i$ have the same meanings. [Punctured-list criterion](first-prime-punctured-four-list.md)

**Five double sites.** Label the missing edge $23$ and define $a,b,c,d,e$ as before. The remaining exceptional site is the hole $z$. The private sizes in order are $h-2,h-2,h-1,h-1$. Delete $f$ from both unit fibers in the two pencils. The scale of $R$ is determined by $R(e)=1$, since heads 2 and 3 agree at $e$. The fourth-power representative becomes $L_O(X-b)^2(X-d)(X-a)^3$. The exceptional binary supports for $DF$ and $D(F-1)$ are $\{a,b\}$ and $\{a\}$. If a second root of $R-1$ occurs at an ordinary site, that site must lie in $U_0$ or $U_1$. Otherwise one of the full disjoint unit fibers would meet the other. Assigning any value to its unused $[1-R]_4$ entry preserves the equations for these two colors.

**One triple site.** Relabel the heads so that $0,2,3$ meet at $t$ and the remaining pairs $01,12,13$ meet separately at $e,c,d$. The private sizes are $h-1,h-2,h-1,h-1$. Now
$$
 F=\alpha\frac{L_{U_0}}{L_{U_1}(X-d)},\qquad
 G=\gamma\frac{L_{U_0}}{L_{U_1}(X-c)},\qquad
 R=\kappa\frac{X-c}{X-d},\qquad R(e)=1.
$$
The unit fibers are $U_2,U_3$. The fourth-power representative is $L_O(X-d)$. Both binary support vectors vanish on all five exceptional sites.

The following two markings in the same prescribed field distinguish the remaining cases. The exhaustive counts use all ordinary balanced partitions, and the last column checks the full pencil identities including $R(e)=1$.

| Shape and marking in $\mathbf F_{17}$ | Partitions | Binary survivors for each twist | Quartic survivors | Exact |
|---|---:|---:|---:|---:|
| Five doubles $(a,b,c,d,e,z)=(5,13,11,3,7,1)$ | 25,200 | 0, 1 | 1 | 1 |
| Triple $(c,d,e,t,z)=(16,5,15,9,1)$ | 92,400 | 1, 1 | 2 | 2 |

For five doubles take $D_0=0$ and
$$
 (D_1,D_2,D_3)=
 (L_{\{6,8,9,12,14,16\}},12L_{\{2,3,4,9,12,14\}},14L_{\{2,4,6,8,11,16\}}).
$$
The punctured center is zero except for values $3,5,7,12,5$ at $5,7,10,13,15$. For one triple take
$$
 (D_1,D_2,D_3)=
 (L_{\{2,3,7,10,11,14\}},2L_{\{3,5,7,8,10,12\}},5L_{\{2,8,11,12,14,16\}}).
$$
Here the center is zero except for values $4,16,10,1,14$ at $4,6,9,13,15$. In each example the four heads have ten agreements apiece and every ordinary coordinate has at least one mismatch. Their hole values are $0,7,3,10$ and $0,15,7,13$, respectively. Thus **all three combinatorial patterns occur** at length sixteen, and these last two give **nineteen distinct MCA-bad scalars** over every proper extension of $\mathbf F_{17}$. Take the received pair $(b,1)$ at the hole with $b$ outside the prime subfield. The fifteen ordinary labels are in the subfield and the four translated hole values all lie outside it. [Reproducible complete checks](../../../scripts/probes/probe_four_fiber_quadratic_characters.py)

The triple example also gives a Lean theorem with the field homomorphism and arbitrary element outside its image as parameters. For every such extension, it produces a concrete set of nineteen labels satisfying the literal bad event on the embedded sixteen sites. The pinned kernel uses only the three standard axioms. Independent `con-leche --verified` accepted all 22,979 transitive declarations. [Universal extension theorem](../../../ArkLib/Research/ProximityGap/Frontier/SmoothSeventeenExtension.lean) · [Geometric height consequence](four-fiber-elliptic-height.md)
