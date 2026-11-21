# The sharp rate-half predecessor on arbitrary evaluation domains

Let $n=4h$, $k=2h$, $e=h-1=3l$, $L=l+1$, and $l\ge2$. The largest possible number of finite MCA-bad scalars at $e$ errors, allowing the field and the $n$ distinct evaluation points to vary, is **$e+3=h+2$**. The lower construction below uses a union of multiplicative cosets as part of its evaluation domain. It applies at the production length $n=2^{30}$ and uses finite base-field codewords. The upper argument sharpens the [apolar predecessor bound](rate-half-apolar-predecessor.md).

## Explicit rows and scalar witnesses

Take a finite field $F$ with $3L\mid |F^\times|$, at least three cosets of $\mu_{3L}$, and $|F|\ge n$. Choose three disjoint cosets $c_i\mu_{3L}$ and extend their union to an $n$-element evaluation set $D$. The initial union has $9L\le n=12l+4$ elements. The cube images $c_i^3\mu_L$ are disjoint and together have $3L=e+3$ elements. For each one of these finite scalars $t$ set
$$
 f_t(X)=\frac{X^{3L}-t^L}{X^3-t}=\sum_{j=0}^l t^j X^{3(l-j)}.
$$
Its roots are the $e$ elements of the corresponding coordinate coset with cubes in $t(\mu_L\setminus\{1\})$. They are distinct because the characteristic does not divide $3L$. Write $B_t$ for this root set and $V=\prod_{x\in D}(X-x)$. Let $[A/B]_+$ denote the polynomial quotient. Use the two received rows given by evaluating
$$
 U_0=[V/X^e]_+,\qquad U_1=-[V/X^{e+3}]_+ .
$$
For $Q_t=V/f_t$ the identity $V(X^3-t)=Q_t(X^{e+3}-t^L)$ gives
$$
 U_0+tU_1=Q_t+P_t,\qquad P_t=-t^L[Q_t/X^{e+3}]_+ .
$$
The degree of $P_t$ is at most $n-2e-3=k-1$. It agrees with the mixture on $S_t=D\setminus B_t$, of size $n-e$. The second row has polynomial degree $n-e-3\ge k$ and $n-e-3<|S_t|$. Its difference with any polynomial of degree less than $k$ has that same degree and cannot vanish on $S_t$. Thus no joint explanation exists on this very witness. This proves the MCA event individually at every listed $t$. The corresponding parity-check pencil on test polynomials of degree at most $2e+1$ is $P\mapsto[X^{e-1}]P-t[X^{e+2}]P$, by the Lagrange interpolation formula. [Lean MCA event at radius $e/n$](../../../ArkLib/Research/ProximityGap/Frontier/CubicApolarEvent.lean) · [Mixed-word identity and no-joint theorem](../../../ArkLib/Research/ProximityGap/Frontier/CubicApolarWitness.lean)

At $n=64$ take $F=\mathbb F_{73}$, $g=5$, the three cosets $g^i\mu_{18}$ for $i=0,1,2$, and the ten least remaining residues as padding. Enumerating all 73 scalars gives exactly 18 bad values, whereas $e+1=16$. The verifier computes the syndromes of the actual received rows, checks that every degree-15 catalecticant kernel is one dimensional, and evaluates all 18 candidate codewords on every site. A word of at most 15 errors has its support locator in this kernel after multiplication to degree 15. Fewer errors give at least two independent such polynomials. Hence a finite parameter can be bad only when its unique locator has 15 distinct roots in the domain. [Complete small-field verifier](../../../scripts/probes/probe_cubic_apolar_witness.py)

## Universal upper bound and equality

Use the notation of the existing apolar proof, with parameter first and coordinate second on the product of two projective lines. In a moving pencil with $M\ge e+2$ bad values its generic minimal locator has bidegree $(l,e)$, and the section $W$ everywhere trivializes $\mathcal O_D(l+1,-e-3)$ on the locator divisor $D$. The original degree bound gives $M\le e+4$. These deductions follow from $d=2e+1$, $r-(d-2r+2)l'\ge0$, $r\le e$ and $M\le3l'+4$. The fixed-support case has at most $e$ bad scalars.

There is a direct upper bound using a third power. As in the ideal and fiber argument, $W^3K/S$ is a nonzero section of $\mathcal O_D(a,b)$ with $a=3(l'+1)-M$ and $b=n+3(r-2-d)=3r-2e-5<r$. If $a<0$, the product has no ambient sections, and the ideal term $\mathcal O(a-l',b-r)$ has no first cohomology since both degrees are negative. This forces $H^0(D,\mathcal O_D(a,b))=0$, a contradiction. Thus $M\le3(l'+1)\le e+3$. In the extremal case $a=0,b=e-5$, so this section is precisely a coordinate polynomial.

The bound also follows from the complementary projection in the already restricted case $M=e+4$. No fiber of the projection $q:D\to\mathbb P^1_x$ can contain a full parameter line, since restricting the trivialized bundle to that line would make $\mathcal O(l+1)$ trivial. Consequently $q$ is finite flat of degree $l$ by the fixed fiber degree. Relative adjunction for this projection gives $\omega_q=\mathcal O_D(l-2,e)$. Finite-flat duality and the trivialization by $W$ yield
$$
 (q_*\mathcal O_D(l,0))^\vee=q_*\mathcal O_D(-2,e)
   \simeq q_*\mathcal O_D(l-1,-3)=\mathcal O_x(-3)^{\oplus l}.
$$
For the last equality use the divisor ideal sequence on the product. Its source is $\mathcal O(-1,-e-3)$, whose zeroth and first direct images to the coordinate line vanish. Thus $q_*\mathcal O_D(l,0)=\mathcal O_x(3)^{\oplus l}$, and $H^0(D,\mathcal O_D(l,-8))=0$. At $M=e+4$ the original nonzero section $W^4K/S$ would belong to this zero space. Here $K$ is the coordinate vanisher and $S$ the parameter vanisher. This excludes $e+4$ and proves the upper bound $e+3$. The argument allows nonreduced components.

At equality $M=e+3$, the section $(W^4K/S)/W$ has bidegree $(0,e-5)$. Every section of that degree comes from a coordinate polynomial $B(x)$, by the divisor ideal sequence and vanishing of $H^0,H^1$ of $\mathcal O(-l,-5)$ on the product. Since $W$ is a unit, $q^*(\mathrm{div}(K)-\mathrm{div}(B))=\pi^*\mathrm{div}(S)$ is effective. Faithfully flat descent gives $B\mid K$. The pullback of the squarefree divisor of $K/B$ is exactly the disjoint union of the $M$ reduced bad fibers. There are exactly $3M$ active coordinates, and each belongs to exactly $l$ distinct bad fibers. The other $e-5$ coordinates belong to none.

## Exact non-subgroup threshold at production length

Take $h=2^{28}$ and the prime
$$
 p=91343852673653315610116111617434743158930931713
  =4722366500471629021257\cdot 2^{84}+1 .
$$
It is a Proth prime with witness 5: the odd cofactor is less than $2^{84}$ and $5^{(p-1)/2}=-1\pmod p$. Both $n$ and $3L=h+2=268435458$ divide $p-1$. Use $\mu_{3L},2\mu_{3L},4\mu_{3L}$ as the core and fill with the least remaining residues; their distinctness follows from $2^{3L},2^{6L}\ne1\pmod p$. The exact budget is $\lfloor p/2^{128}\rfloor=h+1$. The $h+2$ witnesses above exceed it at $e=h-1$.

At $e'=h-2$, if $M\ge e'+2$ in a moving pencil, the apolar inequalities instead give $l'\le\lfloor e'/5\rfloor$ since $d-2r+2\ge5$. The fourth power in the previous argument still has negative coordinate degree and gives $M\le3l'+4$. For these parameters this is less than $e'+2$, a contradiction. The fixed-support case has $M\le e'$. Thus $M\le e'+1=h-1$ for every pair at $e'$ on any domain. The real-radius bad event is monotone and constant on Hamming steps. On the explicit domain the first bad integer error count is $268435455$, the last good count is $268435454$, and the exact operational supremum at 128-bit security is $268435455/1073741824$. The same deduction holds for any field/domain of the stated construction whose budget is in $[h-1,h+1]$. The field supports a smooth subgroup of order $n$; the specified evaluation set is a different subset. [Arithmetic and codeword certificates](../../../ArkLib/Research/ProximityGap/Frontier/CubicApolarWitness.lean)

The pinned Lean kernel checks the cardinality of each power fiber, all three disjoint coordinate cosets, their cube images, and the MCA event for one common received pair. At production length the chosen core has 805306374 sites and admits 268435450 padding sites. The domain contains 1 and a primitive cube root, whose $2^{30}$-th powers differ. Combining the lower construction with the uniform upper bound proves that the maximum bad-scalar count is exactly 268435458 and the worst-case MCA probability on this domain is exactly $268435458/p$. The 128-bit good radii at every positive interleaving width form the strict interval $\delta<268435455/1073741824$. For every $l\ge2$, primes $p\equiv1\pmod{3l+3}$ of arbitrarily large size admit a length-$4(3l+1)$ domain attaining the unrestricted maximum $3l+3$ at $3l$ errors. [Power-fiber construction](../../../ArkLib/Research/ProximityGap/Frontier/CubicApolarAttainment.lean) · [Exact extremum and threshold](../../../ArkLib/Research/ProximityGap/Frontier/CubicApolarExtremum.lean)

## Cubic fibers on the two designated subgroups

For either of the two designated production fields, one reduced locator of size $e$ in $H=\mu_{2^{30}}$ cannot be a union of full unramified fibers of any degree-three rational function $G$. Work over the algebraic closure. Write $G=P/Q$ in homogeneous coprime degree-three forms. The off-diagonal residual of $G(x)=G(y)$ after removing the diagonal has bidegree $(2,2)$ and has no vertical or horizontal component. Since the degree is three and the characteristic exceeds three, the generic fiber is separable and the residual is generically reduced in either variable.

If the residual is irreducible, its normalization has genus at most one and both coordinate functions have degree two. They are multiplicatively independent modulo constants: an irreducible torus curve satisfying a nonconstant monomial relation has a primitive binomial equation, whose two positive bidegrees are coprime. They cannot both be two. On the normalization $x^n,y^n$ have degree $2n$ and nonzero differentials, since $p\nmid2n$. Their zeros and poles occupy at most eight places, so $\chi\le8$. Every distinct ordered collision pair in $H$ supplies a place where both values are one. Corvaja–Zannier’s Theorem 2 bounds this count by
$$
 \max\big((1728n^2)^{1/3},48n^2/p\big)\le12582912 .
$$
The proposed $e$ sites in complete triples give $2e=536870910$ ordered pairs. [Corvaja–Zannier, Theorem 2](https://doi.org/10.4171/jems/409)

In the reducible case the two components each have bidegree $(1,1)$ and give deck Möbius transformations of $G$. The degree-three function-field extension is cyclic since it then has three automorphisms. A nonidentity deck map $R$ has order three and carries all $e$ sites into $H$. Three rational source-target pairs descend $R$ to the base field. A monomial Möbius map is either $cx$, which at order three has no overlap with a dyadic $H$, or $c/x$, of order at most two. Otherwise independent inversions of source and target preserve the intersection count and put $R$ in the form $\lambda(x-a)/(x-b)$ with $\lambda,a\ne0$ and $a\ne b$. Indeed, its invertible matrix has at least three nonzero entries. Choose a numerator row with two nonzero coefficients and a nonzero leading entry in the other row. The proved subgroup intersection bound is $66060289<e$. This includes projective changes of coordinates on the pure cube construction. A general apolar pencil on the smooth domain need not have fibers of this cubic form. [Subgroup intersection theorem](../../../ArkLib/Research/ProximityGap/Frontier/MobiusStepanov.lean)

## Minimum degree of every component on a production subgroup

Still take $n=2^{30}$ and either designated prime. If a predecessor pencil has $M\ge e+2$ bad scalars on $H=\mu_n$, each irreducible component of its geometric locator has bidegree $(a,3a)$ with **$a\ge466034$**. There are at most 191 components in total. This requirement applies to general apolar locators. The following proof uses only the stated apolar reduction, tame curve arguments, and Corvaja–Zannier's Theorem 2.

Restrict the trivialized line bundle $\mathcal O_D(l+1,-3(l+1))$ to the normalization $C$ of any component. If the bidegree is $(a,r)$ then its degree is $(l+1)(r-3a)$, giving $r=3a$. The projection to $t$ has degree $r$ and the coordinate function has degree $a$. Every bad fiber of the full locator is reduced and contained in $H$, so it gives $r$ distinct such sites on this component. Suppose $a\le466033$. All covers below are separable and tame: the cover over $t$ has degree $r<p$, and its Galois closure has group contained in $S_r$, of order prime to $p$.

Take the normalizations $W_i$ of the irreducible off-diagonal components of $C\times_{\mathbb P^1_t}C$. Their generic fibers correspond to the orbits of the monodromy group on ordered unequal pairs of the $r$ sheets. Each $W_i$ projects to $C$ in both ways with the same degree, its degree over $t$ divided by $r$. The image of $W_i$ in $\mathbb P^1_x\times\mathbb P^1_y$ therefore has equal bidegrees in $x$ and $y$. If these two functions are multiplicatively dependent, their torus image is a primitive-binomial curve. Equal positive bidegrees force a graph $y=cx$ or $y=c/x$. For a graph meeting $H\times H$, necessarily $c\in H$. Such a graph comes from a deck transformation of $C$ over $t$: the generic equation for $t$ at $x$ is irreducible over the coordinate function field, and substituting $y=cx$ or $c/x$ gives the same degree-$a$ equation up to scaling since they share the generic parameter. Its graph inside the fiber product is a copy of $C$. These transformations, including the identity, form a subgroup of the dyadic dihedral group $x\mapsto c x^{\pm1}$, of order $d$ a power of two dividing $r$ because it acts freely on a generic fiber. Thus $d\le a$.

For each accepted parameter the dependent components account for at most $r(d-1)$ ordered unequal pairs of sites. There are at least $r(r-d)M$ observations on the independent components. They are distinct places on the normalized fiber products, since all these fibers are reduced and the cover of the smooth parameter line is étale there. On the other hand, the sum of the degrees of $x$ on all the off-diagonal components is $a(r-1)$. Removing the $d-1$ nonidentity active deck graphs leaves total degree at most $D_0=a(r-d)$ on the independent components. On each of them the degree of $y$ equals that of $x$. In particular $\deg x<p$, and $x^n,y^n$ have nonzero differentials.

Here is a bound for the total Euler characteristics used in the gcd theorem. The bidegree gives $g(C)\le(a-1)(r-1)$, so the total ramification of $C\to\mathbb P^1_t$ is at most $2a(r-1)$. A tame inertia permutation $\sigma$ on the $r$ sheets has index equal to $r$ minus its number of cycles. It is a product of that many transpositions. A transposition on the ordered unequal pairs has index $2r-3$; subadditivity of permutation index therefore bounds the induced ramification by $2(r-1)$ times that on the original sheets. Summing Riemann–Hurwitz over the $W_i$, then adding at most $4a(r-1)$ zero and pole places of $x,y$, gives
$$
 \sum_i\chi_i\le-2r(r-1)+4a(r-1)^2+4a(r-1)\le36a^3.
$$
Each $\chi_i$ is nonnegative since a nonconstant coordinate has at least one zero and one pole. Apply Corvaja–Zannier on each independent $W_i$ to $x^n,y^n$, bounding the maximum of its two terms by their sum. Hölder's inequality, $\sum_i \deg x\le D_0$ on these components, and the Euler bound show that the observations number at most
$$
 (54n^2D_0^2\,36a^3)^{1/3}+12n^2D_0^2/p .
$$
For $a\le466033$, $2304a\le n$ and $r-d\ge2a$, so $128\cdot36a^3\le nD_0$. Cubing shows the first term is at most $3nD_0/4=r(r-d)n/4$. The second term is strictly below one at either prime. The actual count $r(r-d)M$ is larger because $M\ge n/4+1$. This contradiction proves the component bound. Their parameter degrees sum to $l=89478485$, giving the asserted number 191. [Arithmetic certificate](../../../ArkLib/Research/ProximityGap/Frontier/CubicApolarWitness.lean) · [Corvaja–Zannier, Theorem 2](https://doi.org/10.4171/jems/409)

There is also a genus lower bound at every component degree. For $a\le l=89478485$, $r<p$, $D_0<p$ and $4n^2D_0<p$. Thus the characteristic correction above is less than $3D_0=r(r-d)$ even at the largest degree. If $128\sum_i\chi_i\le nD_0$, the first term of the gcd bound is at most $3nD_0/4$; together the two terms would again contradict $M\ge n/4+1$. Keeping the actual normalization genus $g=g(C)$ in Riemann–Hurwitz gives
$$
 nD_0<128\sum_i\chi_i\ \le\ 128(r-1)(4a+4g+2r-4)
 <384a(10a+4g).
$$
Since $D_0\ge2a^2$, this forces **$6g>8388593a$**. Every component, including one carrying the entire bidegree, must have high geometric genus. Summing over all components gives total normalization genus at least **125099765486935**. [Cutoff and genus arithmetic](../../../ArkLib/Research/ProximityGap/Frontier/CubicApolarWitness.lean)

## A constraint on variation in the coordinate coefficients

Keep the original multiplicative coordinate $X$ on $H=\mu_n$. Let $e=n/4-1$ be odd and suppose the exceptional locator has more than $e+1$ bad parameters. Every bad fiber has the form
$$
f_\tau(X)=\sum_{j=0}^e a_j(\tau)X^j
$$
with $e$ distinct roots in $H$. Its first and last coefficients are nonzero. At each fixed site $x\in H$, the parameter polynomial $f(T,x)$ is nonzero of degree at most $l=e/3$. Indeed, a coordinate constant component would violate the bidegree identity $(a,3a)$ proved above.

Fix $0\le u\le v\le e$. Take any subfamily on which all leading ratios $a_j/a_e$ for $j>v$ and all trailing ratios $a_j/a_0$ for $j<u$ are constant. The two normalizations may vary independently in the parameter. This subfamily has at most $l$ members whenever $v-u$ is at most the bound in the table.

| Field | Lower bound for $\log_2 p$ | Sufficient upper bound for $v-u$ |
|---|---:|---:|
| Boundary prime $91343853062927602073649116268957764822404956161$ | 156 | 165191046 |
| First designated prime | 158 | 166497938 |
| Second designated prime | 159 | 167139054 |

For two root sets $E_1,E_2$ in this subfamily, Newton's identities applied to the monic locator and the monic reciprocal locator give the same power sums at all exponents $1\le b<e-v$ and $1\le -b<u$, respectively. Their power sums also agree at zero since both sets have size $e$. The combined interval contains at least $z=\lfloor(e-(v-u)-1)/2\rfloor$ odd exponents, distinct modulo $n$. Fix a generator $g$ of $H$ and put $c_j=1_{E_1}(g^j)-1_{E_2}(g^j)$, $C(Y)=\sum_j c_jY^j$. For each such exponent $b$, $C(g^b)=0$ in $\mathbb F_p$.

For a primitive complex root $\zeta$ of order $n$, multiplication by $C$ in $\mathbb Z[Y]/(Y^{n/2}+1)$ has determinant $N=\operatorname{Norm}_{\mathbb Q(\zeta)/\mathbb Q}(C(\zeta))$. The reduction of the multiplication matrix modulo $p$ diagonalizes at all the primitive roots. At least $z$ diagonal entries vanish, so $p^z\mid N$ by Smith normal form. On the complex side, orthogonality over the odd exponents gives
$$
\frac{2}{n}\sum_{b\;\mathrm{odd}\bmod n}|C(\zeta^b)|^2
=\sum_{j<n/2}(c_j-c_{j+n/2})^2
\le 2\sum_j c_j^2\le4e.
$$
Arithmetic–geometric mean gives $|N|\le(4e)^{n/4}$. Since $4e<2^{30}$ and $p>2^s$ for the corresponding table entry $s$, the inequality $sz\ge30(n/4)$ forces $N=0$. Consequently $Y^{n/2}+1$ divides $C(Y)$ in $\mathbb Z[Y]$, so $c_j=c_{j+n/2}$ for every $j<n/2$. Thus the two root sets have identical signed occupancies on every antipodal pair. Because each fiber has odd size, some pair has signed occupancy $1$ or $-1$; the same site of that pair then lies in every fiber in the subfamily. At most $l$ bad parameters can contain one site. [Lean common-site implication and numeric bounds](../../../ArkLib/Research/ProximityGap/Frontier/ApolarAntipodalFiber.lean)

In particular the full exceptional locator cannot have the separated form $A(X)-R(T)X^j$ (after clearing parameter denominators), for any $0\le j\le e$, even when the resulting curve has high genus. More generally a separated rational map $A(X)/B(X)$ is excluded if its two-dimensional pencil contains a nonzero polynomial supported in a band of the indicated width. Choose that polynomial as the denominator by a projective change of the value coordinate. On finite fibers the other coefficients then vary only in that band. The omitted parameter value of this change has at most $l$ preimages, and removing them leaves more than $l$ bad parameters. This covers maps in the original multiplicative coordinate and its inversion or multiplicative rescaling.
