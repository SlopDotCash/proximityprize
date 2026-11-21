# The exact bad-scalar count at the unique-decoding endpoint

Let $h\ge3$, $n=4h$ and $k=2h$. At $e=h$ errors the maximum number of bad finite folding scalars, over all finite fields, injective length-$n$ domains and received pairs, is $3(h+1)$. Here a bad scalar has a set of $n-e$ agreements with a Reed–Solomon codeword on which no pair of codewords jointly explains the received rows.

## Upper bound

In the [cubic apolar bound](../../../ArkLib/Research/ProximityGap/Frontier/SharpApolarMCA.lean) take $d=n-k-1=2h-1$. The unique-range constraint is $2e=d+1$, and the coordinate condition is $4h<3(d+2-e)+e=4h+3$. The maximum in that theorem becomes $\max(h+1,3(\lfloor h/1\rfloor+1))=3(h+1)$. The argument applies to every injective evaluation domain. At $h=2^{28}$ it gives $805306371$.

## Attaining the bound

The construction works for any $n=k+2e$ with $k,e\ge1$. Choose a finite field containing the $(e+1)$-st roots of unity, with characteristic coprime to $e+1$. Choose $m$ disjoint multiplicative cosets of this group and an $n$-element domain $D$ containing them. Write $V=\prod_{x\in D}(X-x)$ and $[R]_+$ for the polynomial quotient of $R$ by $X^{e+1}$. The two received rows are the evaluations of $U_0=[VX]_+$ and $U_1=-[V]_+$.

For a site $t$ in any chosen coset $A$, let $E=A\setminus\{t\}$ and $Q=\prod_{x\in D\setminus E}(X-x)$. The product of $X-x$ over $A$ is $X^{e+1}-t^{e+1}$. It follows that
$$
 V(X-t)=Q(X^{e+1}-t^{e+1}),\qquad
 U_0+tU_1=Q-t^{e+1}[Q]_+ .
$$
The last term $P=-t^{e+1}[Q]_+$ has degree at most $n-2e-1=k-1$. The mixture therefore agrees with $P$ on all $n-e$ sites of $D\setminus E$. The second row has degree $n-e-1=k+e-1$, at least $k$ and strictly less than this witness size. Its difference with any codeword polynomial has degree $n-e-1$, which precludes joint explanation on the same set. Every one of the $m(e+1)$ distinct sites is thus a bad scalar for a single received pair.

Taking $e=h$, $k=2h$ and $m=3$ gives the claimed maximum. The padding has $h-3$ sites. An appropriate finite field always exists: choose an odd prime $q$ coprime to $h+1$, and an extension degree divisible by the multiplicative order of $q$ modulo $h+1$, large enough that the field contains $4h$ sites and three cosets. The construction only requires a union of three cosets inside the domain. The maximum on the particular multiplicative subgroup $\mu_{4h}$ can be smaller.

At production length one explicit field is $p=267268857013743962100724606304616304664727519233=(2^{28}+1)\cdot47939\cdot2^{114}+1$. Its budget is $785432578$. The distinct cosets with representatives $1,2,4$ meet the hypotheses. Hence the predecessor cap $268435458$ is within budget, while the endpoint attains $805306371$ on the constructed domain. The exact first bad Hamming count on this domain is $268435456$. The prime also admits smooth domains of length $2^{30}$; the argument does not identify this constructed domain with one of them.

## Why a different polynomial cannot transplant this example to the smooth subgroup

The same division argument works with any monic polynomial $A$ of degree $h+1$ in place of $X^{h+1}$: divide by $A(X)$ and replace $t^{h+1}$ by $A(t)$. On the smooth subgroup $H=\mu_{4h}$ this extension still cannot supply even two complete fibers when $h$ is a power of two with $h\ge2$ and $p>(4(h+1))^2$. Both designated prime fields meet this inequality.

To see this, suppose two distinct values have full fibers $S,T\subset H$, each of odd size $d=h+1$. Their monic vanishing polynomials differ only in the constant term, so Newton's identities give equal power sums for exponents $1$ through $h$. Fix a generator $g$ of $H$ and set $c_j=1_S(g^j)-1_T(g^j)$ and $C(Y)=\sum_{j=0}^{4h-1}c_j Y^j$. Then $C(g^b)=0$ for all $h/2$ odd exponents between $1$ and $h$.

For a complex primitive $4h$-th root $\zeta$ set $N=\operatorname{Norm}(C(\zeta))$ in the cyclotomic field. Modulo $p$ multiplication by $C$ on $\mathbb Z[Y]/(Y^{2h}+1)$ has at least $h/2$ independent null vectors, since it diagonalizes at the primitive roots $g^b$. Its integer determinant is therefore divisible by $p^{h/2}$. Orthogonality on odd exponents gives mean squared absolute value $\sum_{j<2h}(c_j-c_{j+2h})^2\le4d$ since $S,T$ are disjoint and the sum of $c_j^2$ is $2d$. Arithmetic–geometric mean now gives $|N|\le(4d)^h<p^{h/2}$, so $N=0$. Thus $Y^{2h}+1$ divides $C$ over the integers, and $c_{j+2h}=c_j$ for every $j<2h$. The positive coefficients occur in pairs, contradicting odd $|S|$. In particular, the exact arbitrary-domain example leaves a substantive subgroup-specific question.

The exhaustive small checks recover all 12 bad scalars for $n=12$ over $\mathbb F_{13}$ and all 15 for $n=16$ over $\mathbb F_{31}$, including the case with a padding site. The verifier enumerates all witness sets and tests actual polynomial agreements and nonjointness. [Exhaustive verifier and prime certificate](../../../scripts/probes/probe_power_fiber_endpoint.py)

## Rational functions give a broader construction

Let $n=k+2e$ with $k,e\ge1$. Let $P$ be monic of degree $e+1$, coprime both to a polynomial $B$ and to the domain vanisher $V$. Let $W$ be the degree-at-most-$e$ residue of $V/B$ modulo $P$. Use rows $xW(x)/P(x)$ and $-W(x)/P(x)$ on the evaluation sites. Suppose $P-cB$ is the monic vanisher of a set $A$ of $e+1$ distinct roots, with $c\ne0$. For **each** $t\in A$ for which $E=A\setminus\{t\}$ lies in the domain, let $Q$ be the vanisher of $D\setminus E$. Then $V(X-t)=Q(P-cB)$. Reducing modulo $P$ and cancelling $B$ shows
$$
 H_t=\frac{(X-t)W+cQ}{P}
$$
is a polynomial. Its degree is at most $(k+e)-(e+1)=k-1$. It agrees with the folded rows at every root of $Q$.

If a codeword polynomial $R$ explained the second row on those same $k+e$ sites, then $RP+W=aQ$ for a constant $a$, by root counting and the degree bound. Modulo $P$ this would imply $Q(c+a(X-t))=0$. But $Q$ is a unit modulo $P$ and the degree-at-most-one polynomial $c+a(X-t)$ is nonzero at $t$. This contradicts $\deg P=e+1\ge2$. All these parameters are therefore bad, including a parameter outside the domain when its other $e$ fiber sites lie inside. [Lean proof of the construction](../../../ArkLib/Research/ProximityGap/Frontier/RationalFiberEndpoint.lean)

In particular, three disjoint $(h+1)$-subsets of a given smooth domain whose monic vanishing polynomials lie on a single affine line suffice to attain the worst-case $3(h+1)$. Write the pencil as $P_0-cB$, with $\deg B\le h$. Disjoint sets force $P_0$ coprime to $B$. If the field has more than $n$ elements, choose $P$ in this pencil avoiding every site, excluding at most one parameter per site. This supplies the stated coprimality and makes all three selected $c$ nonzero. The existence of this configuration on the designated subgroups remains open.

## Three complete quintic fibers on the sixteenth roots of unity

Let a field contain an element of order 16. Its subgroup of order 16 contains three disjoint five-point fibers of one rational function of degree five **if and only if its characteristic is 3, 17 or 31**. For a fixed omitted site there are respectively two, one and one unordered triples of such fibers. This classifies this construction in every field at length 16. Other constructions and larger lengths are separate questions.

Here is the exact finite calculation. Scale the missing site to 1 and represent the other sites by exponents 1 through 15 of a primitive root. Enumerate the 126,126 unordered partitions of those exponents into sets of size five. The odd powers of a primitive root act on this enumeration with 15,981 orbits. For each representative form the three monic vanishing polynomials in the variable (X), with coefficients in (mathbb Z[Y]/(Y^8+1)). Their coefficient vectors are collinear exactly when every two-by-two minor of the two differences vanishes. This is equivalent to the rational-fiber condition. Indeed, the fiber polynomials lie in a pencil, and conversely two disjoint sets give coprime forms generating that pencil.

If all minors vanish at a primitive root in characteristic (p), then (p) divides the integral cyclotomic norm of every minor. Every orbit has a nonzero minor over the integers, excluding characteristic zero. For odd primes, the greatest common divisors of the odd parts of the norms are (1,17,49,289,961,6561); the associated partition counts are (125592,512,12,4,4,2). Each norm is evaluated using (N(f)=f_{\rm even}^2-Yf_{\rm odd}^2) down the quadratic tower. For the four surviving primes, take the polynomial gcd of all minors and (Y^8+1) modulo (p). Its degree counts the primitive roots at which that partition works, since (Y^8+1) is separable. Odd powers permute all eight primitive roots, so the orbit-weighted incidence count divided by eight gives the count for a fixed generator. This final step eliminates characteristic 7.

At (p=17), take the whole multiplicative subgroup. For
$$
  P=X^5+4X^4+14X^3+11X^2+5X+11,\qquad W=12X^4+12X^3+3X^2+10X+15,
$$
the rows (xW(x)/P(x)) and (-W(x)/P(x)) have precisely the 15 bad scalars (2,3,\ldots,16) at four errors. Enumerating every 12-site witness and interpolating from its first eight sites gives that set directly. The universal upper bound is 15, so this prescribed smooth-domain code has exact worst-case probability (15/17). [Reproducible classification and event check](../../../scripts/probes/probe_mu16_quintic_fibers.py)
