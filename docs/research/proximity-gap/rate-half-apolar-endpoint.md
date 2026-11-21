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
