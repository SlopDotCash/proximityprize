# A rate-half MCA threshold at production length

Let $n=2^{30}=4h$, $h=268435456$, and $k=2h$. On any $n$ distinct field elements, at most **268,435,458** finite scalars can be MCA-bad at $h-1$ Hamming errors for any received pair. At $h$ errors, a pair of received rows has at least **536,870,914** bad scalars. Consequently the first bad error count at security $2^{-128}$ is exactly **268,435,456** on any such field whose budget $B=\lfloor |F|/2^{128}\rfloor$ satisfies
$$
268435458\le B\le536870913.
$$
Its last good integer radius is $h-1$ and its supremal good relative radius is $1/4$. The endpoint $1/4$ fails.

For an explicit prime-field instance one unit above the lower endpoint, take
$$
p=91343853369979269099964682909737195747164553217
  =17179869379\cdot2^{122}+1,
\quad g=39947002152884693406992285236833299620967665422 .
$$
At the lower endpoint itself take
$$
p'=91343853062927602073649116268957764822404956161
   =68719477285\cdot2^{120}+1,\quad
g'=15880532512442061028676049873222051690399817336.
$$
Here $\lfloor p'/2^{128}\rfloor=268435458$. The multiplicative orders of $g,g'$ in their respective fields both equal $n$. Thus this instance uses the smooth evaluation domain and security level in the challenge. The two previously designated production primes have larger budgets. Their known good radius $1/4$ follows from earlier unique-decoding estimates. The exact threshold here pertains to the displayed budget interval.

## The syndrome pencil

Write $e=h-1$, $d=n-k-1=2h-1$, and $S_j=H^0(\mathbb P^1,\mathcal O(j))$ for homogeneous binary forms of degree $j$ in the coordinate variable. Work over an algebraic closure of the finite field for the geometric argument. The distinct evaluation points remain fixed. If $V(X)=\prod_{x\in H}(X-x)$, send a received word $v$ to the functional
$$
\lambda_v(P)=\sum_{x\in H}\frac{v(x)}{V'(x)}P(x,1),\qquad P\in S_d .
$$
Its kernel on received words is the Reed–Solomon code of dimension $k$. Indeed interpolation gives $\sum_x f(x)/V'(x)=0$ for $\deg f<n-1$, so each codeword lies in the kernel. The $d+1$ by $n$ parity-check matrix has full row rank by the Vandermonde determinant. A word with errors supported on a finite set $B\subseteq H$ has syndrome in the span of the evaluations at $B$.

Given the two words, their syndromes give a homogeneous pencil $\lambda_{[t_0:t_1]}=t_0\lambda_0+t_1\lambda_1$, viewed globally as $S_d\otimes\mathcal O\to\mathcal O(1)$ on the parameter line. The challenge's affine scalars are $[1:\gamma]$. If the whole pencil is zero, both rows are codewords and there are no bad scalars. A pencil of projective image a single point may have one zero member; the proof below allows it.

Suppose $M\ge e+2$ distinct scalars are bad. At each such scalar there exists a codeword within $e$ errors. The associated functional is annihilated by the binary vanisher of its error sites, multiplied if necessary to degree $e$. Thus at that parameter the map
$$
S_e\longrightarrow S_{d-e}^*,\qquad f\longmapsto(P\longmapsto\lambda(fP))
$$
has nonzero kernel. Every maximal minor has parameter degree $e+1$ and vanishes identically because it has at least $e+2$ distinct zeros. Over the rational function field of the parameter line there is therefore an apolar form of degree at most $e$.

Take a nonzero apolar form $f$ of smallest degree $r\le e$. Here apolar means that $\lambda(f S_{d-r})=0$. We have $r\ge1$ because the generic syndrome is nonzero. The smallest form is unique up to nonzero scaling: for two nonproportional degree-$r$ forms divide out their greatest common divisor of degree $c<r$. Two coprime binary forms of degree $r-c$ generate all binary forms in degrees at least $2(r-c)-1$, by the binary resultant or the two-generator Koszul sequence. Since $d-c\ge2(r-c)-1$, the greatest common divisor is already apolar, which contradicts minimality.

Clear coefficient denominators of $f$ and eliminate all common factors in the homogeneous parameter coefficients. We obtain a form of bidegree $(l,r)$ without a parameter basepoint. Its zero scheme $D$ in $\mathbb P^1_t\times\mathbb P^1_x$ is an effective Cartier divisor. Its projection $\pi$ to the parameter line is finite flat of degree $r$: every fiber is a degree-$r$ nonzero form on the coordinate line, and the degree is constant. Fibers and components are allowed to be nonreduced. Write $\mathcal O_D(a,b)$ for restriction from the product, in parameter and coordinate order.

## A nonvanishing functional on the generic locator

Twist the ideal sequence of $D$ by $\mathcal O(0,d)$ and push it down by the parameter projection. Since $d-r\ge0$, it gives
$$
0\longrightarrow S_{d-r}\otimes\mathcal O(-l)
 \xrightarrow{\ f\ } S_d\otimes\mathcal O
 \longrightarrow\pi_*\mathcal O_D(0,d)\longrightarrow0.
$$
The pencil kills the first term generically, hence everywhere by the polynomial identity. It factors through a functional $\pi_*\mathcal O_D(0,d)\to\mathcal O(1)$, including fibers at which the rank drops. Finite-flat duality and relative adjunction identify this map with a section
$$
W\in H^0(D,\mathcal O_D(l+1,r-2-d)).
$$
Indeed the relative dualizing sheaf is $\mathcal O_D(l,r-2)$, obtained by adding the divisor to the relative canonical sheaf $\mathcal O(0,-2)$. The perfect pairing of a finite flat algebra with its dual commutes with base change. It identifies multiplication of the section by a coordinate form with the dual functional after multiplication by that same form on the fiber algebra. These descriptions also follow on an affine chart from the coefficient-of-$X^{r-1}$ pairing on a monic polynomial quotient.

The section $W$ generates its line bundle at every generic point of $D$. To see this over the rational function field, use the Artinian algebra of the degree-$r$ divisor and trivialize the line bundles there. If $W$ fails to generate in a local factor, it belongs to its maximal ideal, so some nonzero ideal annihilates the resulting functional as a module element. The functional then descends to the quotient by this ideal, a proper subdivisor of $D$ of length less than $r$. Every divisor of length $r'<r$ on the projective coordinate line is defined by a binary form of degree $r'$. That form now annihilates the original syndrome, contradicting the choice of $r$. This algebra argument works with repeated factors. Nondegeneracy of the resulting linear pairing also persists after any extension of the generic field.

A Cartier divisor in this smooth surface is Cohen–Macaulay with no embedded associated points. Multiplying by $W$ therefore injects $\mathcal O_D$ into its line bundle. Its cokernel has finite nonnegative length. The Euler-characteristic difference, computed from the ideal sequence on the product, is
$$
\deg_D\mathcal O_D(l+1,r-2-d)
   =r(l+1)+l(r-2-d)
   =r-(d-2r+2)l\ge0 .
\tag{1}
$$
In particular $l\le\lfloor e/3\rfloor$, since $r\le e$ and $d-2r+2\ge3$.

## Vanishing at bad parameters

Let $K(X,Z)=\prod_{x\in H}(X-xZ)$ be the coordinate-domain vanisher of degree $n$. At a bad parameter $t$, the error syndrome is a sum of evaluations on a reduced set $B_t$ of size at most $e$. It is also represented by $W_t$ on $D_t$. The union of these two finite schemes has length at most $e+r\le d+1$. Restriction of $S_d$ onto the union is surjective by the ideal sequence of that divisor on $\mathbb P^1$. Consequently the two functionals, extended by restriction from the union, coincide there. A function vanishing on $B_t$ annihilates the functional on the union, and hence annihilates $W_t$ on $D_t$. In particular $K W_t=0$ as a section, including on the nilpotents of $D_t$. One can trivialize all the line bundles on this finite scheme before making this argument. If the syndrome itself vanishes at $t$, the surjectivity simply gives $W_t=0$.

Let $S$ be the product of the $M$ distinct linear parameter factors. Flatness makes each of these parameter fibers a Cartier divisor on $D$, and the fibers are pairwise disjoint. The preceding vanishing therefore allows division by $S$ on $D$. In particular
$$
U=\frac{W^3 K}{S}
\in H^0\big(D,\mathcal O_D(3(l+1)-M,\ n+3(r-2-d))\big).
\tag{2}
$$

If $K$ restricts nontrivially to $D$, then $U$ is nonzero: $W$ is a non-zero-divisor, and multiplication back by $S$ gives $W^3K$. If $K$ vanishes identically on $D$, its ideal sequence extends $K$ to a section of $\mathcal O(-l,n-r)$, hence $l=0$ and $f$ divides the squarefree domain vanisher. The whole pencil is then supported on one fixed reduced subset $B$ of at most $r\le e$ domain sites. Both received rows are a codeword plus errors supported on $B$, since their individual syndromes are supported there and the parity-check kernel is the code. On $H\setminus B$ they agree with these two codewords. Discard sites in $B$ with both discrepancies zero. Each remaining site can cancel at at most one finite scalar. At all other scalars the mixed candidate has full agreement exactly off these active sites, where the two original rows have a joint explanation. The candidate is unique since the code's distance $2h+1$ exceeds $2e$. This fixed-support case thus gives at most $r$ bad scalars, including for a proportional syndrome pencil.

For a divisor of bidegree $(l,r)$ the ideal sequence gives
$$
H^0(D,\mathcal O_D(a,b))=0\qquad\text{if } a<0\text{ and }b<r .
\tag{3}
$$
The ambient $H^0(\mathcal O(a,b))$ is zero because $a<0$, and $H^1(\mathcal O(a-l,b-r))$ vanishes by Künneth since both entries are negative. For the section (2), $b-r=n+2r-3d-6\le-5$. Thus (3) gives
$$
M\le3l+3\le3\lfloor e/3\rfloor+3=h+2 .
$$
This proves the unrestricted bound. Moreover if $M\ge e+2$, then $r=e$, $l=e/3$ and equality holds in (1). Otherwise $3l+3\le e+1$ since $h\equiv1\pmod3$. The degree equality makes $W$ invertible everywhere. Thus every such bad fiber is a reduced length-$e$ divisor supported completely on the evaluation domain. No intermediate geometric point was assumed rational. [Elementary polynomial proof](rate-half-apolar-polynomial-proof.md)

### The extremal incidence pattern

If $M=e+3=h+2$, then in (2) the parameter degree is zero and the coordinate degree is $r-5$. The ideal sequence of $D$ shows that $U$ is the restriction of an ordinary homogeneous polynomial $Q$ in the coordinate variable alone: the kernel term is $\mathcal O(-l,-5)$ and its $H^1$ vanishes. Thus $W^3K=S Q$ on $D$. Each irreducible component has bidegree $(u,3u)$ with $u>0$, by the component degree argument below. Hence projection to the coordinate line is finite and surjective. Because $W$ is invertible, pullback of the zero divisor of $Q$ is bounded by that of $K$. It follows that $Q$ has $r-5$ distinct roots, all in the evaluation domain. Indeed pullback to the normalization of any such component preserves the order comparison after multiplication by the positive ramification index. Cancel $Q$ to get $W^3(K/Q)=S$ on $D$.

There are exactly $3M=n-(r-5)$ surviving coordinates. Their fibers on $D$ coincide, as a divisor, with the union of all $M$ selected parameter fibers. Those parameter fibers are reduced, so every incident point is smooth on $D$ and each surviving coordinate also has a reduced fiber. Thus each of the $3M$ coordinates occurs at exactly $l$ distinct selected parameters, and each selected parameter occurs on $3l=e$ distinct surviving coordinates. All other coordinates occur at none of the selected parameters.

## A bad received pair at the next integer

Choose disjoint subsets $E_1,E_2\subset H$, each of size $h+1$. Let $D_0$ be the vanisher of their common complement, of degree $2h-2$. Consider the two polynomial pairs
$$
P_1=(0,0),\qquad P_2=(XD_0,-D_0).
$$
Both have row degrees less than $k$. They coincide on $H\setminus(E_1\cup E_2)$ and differ on every point of $E_1\cup E_2$. Put the receiver equal to $P_2$ on $E_1$ and to $P_1$ elsewhere. The receiver agrees jointly with $P_i$ precisely on $C_i=H\setminus E_i$, of size $3h-1$. For each $x\in E_i$ take the finite scalar $\gamma=x$. The two mixed polynomial values at $x$ agree because their difference is $(x-\gamma)D_0(x)$. Hence the folded polynomial corresponding to $P_i$ agrees on $C_i\cup\{x\}$, of size $3h=n-h$. A joint polynomial explanation on this same witness would agree with $P_i$ throughout $C_i$, forcing equality of each row polynomial by $3h-1\ge k$ distinct evaluations. Its second row disagrees at $x$ because $D_0(x)\ne0$. The $2h+2$ chosen scalars are distinct because $E_1,E_2$ are disjoint and the evaluation points are distinct.

At error count $h-1$ the universal numerator bound is $h+2$; at $h$ the supplied numerator is $2h+2$. The MCA event is monotone in radius and is constant between successive Hamming grid points. This proves the exact field-budget interval and the claimed endpoint.

## Prior bound and verification

The integral BCHKS bound in Chojecki, Theorem 5.2, gives the predecessor numerator at most $\lfloor4h(h+2)/(3(h-1))\rfloor=357913945$. It exceeds the two explicit new budgets $268435458$ and $268435459$. For the first repository production prime the budget is already $n$, and unique-decoding estimates had established goodness through $h$ errors. Formula (2) improves its worst-case numerator at the predecessor; it does not move that prime's known threshold bracket. [Chojecki, ePrint 2026/1463](https://eprint.iacr.org/2026/1463)

The finite-field certificate uses Proth's test: the displayed odd cofactor is below $2^{122}$ and $3^{(p-1)/2}=-1\bmod p$. Taking $g=3^{(p-1)/2^{30}}$ gives $g^{2^{29}}=-1$ and $g^{2^{30}}=1$. Its exact rounded budget is $p\mathbin{\mathrm{div}}2^{128}=268435459$. The new lower-budget prime has the analogous Proth witness 3, with $g'=3^{(p'-1)/2^{30}}$. Lean certifies primality, the exact generator orders, both budgets and the MCA lower bound at $h$ by the repository bisimplex theorem. The unconditional upper proof and the extra geometric restrictions are written proofs. [Lean field and bad-side certificates](../../../ArkLib/Research/ProximityGap/Frontier/RateHalfApolarBudget.lean)

## Components of an exceptional locator on the dyadic subgroup

Suppose $M\ge h+1$ and $H=\mu_n$ in either designated production field or in the explicit budget-$h+3$ field. As proved above, $r=e=3l$, $W$ is invertible on $D$, and every selected bad fiber is reduced and contained in $H$. In particular $D$ itself is reduced: any repeated horizontal component meets every fiber with multiplicity at least two, and there are no vertical components over the parameter line. For every geometrically irreducible component $C\subset D$ of bidegree $(u,v)$, restriction of the invertible section trivializes $\mathcal O_C(l+1,-3(l+1))$. Its degree is $(l+1)(v-3u)$, hence $v=3u$. Here $v>0$ by finiteness over the parameter line, so $u>0$ as well.

In fact $u$ is **at least 16 and cannot equal 17**. The argument works over the algebraic closure and applies to each geometric component separately, including those permuted by Frobenius.

Choose an irreducible affine equation $F(T,X)$ of bidegree $(u,3u)$ for $C$. Eliminate $T$ from $F(T,X)$ and $F(T,Y)$ by their resultant. The resultant is nonzero: an independent generic pair $(X,Y)$ cannot come from a common parameter because the fiber product $C\times_{\mathbb P^1_T} C$ has dimension one. Its bidegree in $X,Y$ is at most $(3u^2,3u^2)$. Each root in $T$ of $F(T,X)$ contributes a factor $Y-X$ when evaluating $F(T,Y)$, with multiplicities included over $\overline{F(X)}$. Therefore $(X-Y)^u$ divides the resultant. Removing it leaves a nonzero polynomial of bidegree bounded in both variables by $B=3u^2-u$, containing all ordered off-diagonal coordinate pairs with a common point above the parameter. Extra components only enlarge the ensuing upper bound. The projective resultant has the same degree estimate and accounts for the parameter at infinity.

A translated-subtorus component contributing an off-diagonal pair on $H^2$ must have the form $Y=cX$ or $Y=c/X$ with $c\in H$. To see the equality of projection degrees, choose a component of the parameter fiber product dominating this resultant component. Both projections to $C$ have equal degrees because composition with $C\to\mathbb P^1_T$ gives the same nonconstant parameter. Composition with the coordinate projection of $C$ then shows that the two coordinate maps also have equal degrees. A primitive monomial parametrization of a torus translate now has two exponents of equal absolute value, necessarily one. No vertical or horizontal resultant component occurs since the fibers of $C$ above a fixed coordinate are finite and each parameter in turn has finitely many coordinates. At the generic point of $Y=cX$ or $c/X$, $F(T,X)$ and its transformed equation share a $T$-root. They are irreducible over $\overline F(X)$ by primitivity and irreducibility of $F$, hence proportional. The transformation of the coordinate thus preserves $C$ and fixes $T$.

All transformations of these two types that preserve $C$ and send $H$ to itself form a subgroup of the dihedral group of order $2n$. Their action on the function field of $C$ is faithful. Their order divides the degree $3u$ of this field over $\overline F(T)$ by the fixed-field theorem. Thus this order is at most $q_u=2^{v_2(u)}$. Each bad fiber contains $3u$ distinct $H$-points of $C$. Of the other coordinates in this fiber, any fixed coordinate has at most $q_u-1$ reached by these symmetries. The $M$ fibers therefore give at least $M\cdot3u(3u-q_u)$ ordered incidences outside the toric components. Any pair is counted on at most $u$ fibers because a fixed first coordinate has at most $u$ parameters. Hence the resultant's non-toric components must contain at least $3M(3u-q_u)$ distinct subgroup pairs.

For each absolutely irreducible non-toric component of bidegree $(a,b)$, its Euler characteristic satisfies $\chi\le2ab$ as in the [cubic collision proof](rate-half-predecessor-rich-lines.md). Corvaja–Zannier gives at most $(108a^2b^2n^2)^{1/3}$ subgroup points whenever $p>12n^2 B^2$. This characteristic condition holds for all $u\le17$ on the three primes here. Summing over components preserves the bound with $a,b$ replaced by $B$: $(ab)^{2/3}\le (a^{4/3}+b^{4/3})/2$, while the sums of both component degrees are at most $B$. Thus
$$
\big(3M(3u-q_u)\big)^3\le108 B^4 n^2.
$$
At $M=h+1$, exact integer substitution violates this inequality for every $1\le u\le15$ and for $u=17$. At $u=16$ the comparison permits a component. For $u=1$ the bound recovers $M\le2097152$; the stronger exclusion of graph components requires no descent assumption on their degree-three rational maps.
