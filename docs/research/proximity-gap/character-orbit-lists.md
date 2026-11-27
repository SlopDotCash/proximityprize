# Full rotation orbits in production monomial centers

At length $n=2^{30}$, on **both named primes and all four rates**, the single center $y(x)=x^{k+4}$ has at least $\binom{130019327}{4}>10^{31}$ distinct Reed–Solomon messages at exactly $k+4$ agreements. **Every constructed message has rotation orbit of length $n$.** Repeating the scalar words gives the same witnesses at every positive interleaving width. The previously known unrestricted witnesses fail at smaller error counts. [Production brackets](full-prize-review.md) · [Exact verifier](../../../scripts/probes/probe_character_orbit_lists.py)

There is also an exact result throughout a degree range. On the first prime set $G=98{,}539{,}598$, and on the second set $G=97{,}919{,}852$. For every $k+G\le d<n$, the list around $x^d$ at **$d$ agreements** consists of exactly $n/d$ constants when $d\mid n$ and is empty otherwise. The numerical production cutoff for unrestricted centers remains open. The independent result for general received polynomials of degree at most the required agreement count gives exact maxima $3,3,3,1$ at the first unresolved radii. [Bounded-degree centers](low-degree-center-list-rigidity.md)

## Two finite-field templates

Write $M=65{,}536$ and choose $z$ of order $n$ using the specified generator, 3 or 37. Put $u=z^{n/M}$. The attached integer lists specify $A\subset\mu_M$ and $B\subset\mu_n$, each of cardinality 2,049. For the corresponding root $r=u$ or $z$, a nonnegative entry $a$ means $r^a$ and a negative entry $-a$ means $-r^a$. Direct modular exponentiation checks
\[
 \sum_{a\in A}a=0,\qquad \sum_{b\in B}b^3=0.
\]
The sites of $A$ occupy distinct cosets of $\mu_8$ inside $\mu_M$. The sites of $B$ occupy distinct cosets of $\mu_M$ inside $\mu_n$. The search assembled signed four-element choices in disjoint blocks by matching low binary digits of partial sums. Verifying a template requires only modular exponentiation, addition and comparisons of exponent residues. [Explicit named-field data](../../../scripts/probes/character_orbit_zero_sums.json)

If $ab$ and $a'b'$ are in the same $\mu_8$ coset, then $b/b'\in\mu_M$, so $b=b'$ and then $a=a'$. The products $ab$ therefore occupy $2{,}049^2=4{,}198{,}401$ distinct eighth-root cosets. Let $v$ have order eight. In each of these cosets select the four sites $ab,abv,abv^2,abv^3$, giving a set $S$ of 16,793,604 points. Its $j$th power sum factors as
\[
 \sum_{s\in S}s^j=
 \left(\sum_{a\in A}a^j\right)
 \left(\sum_{b\in B}b^j\right)
 \left(\sum_{r=0}^{3}v^{rj}\right).
\]
The first factor vanishes for $j=1$, the second for $j=3$, and the last for $j=2,4$.

Add any $(k+4-|S|)/8$ of the 130,019,327 unused eighth-root cosets. The resulting set $T$ has size $d=k+4$ and its first four power sums vanish. Newton's identities apply in the named characteristics, so the top four coefficients below the leading term of $L_T(X)=\prod_{x\in T}(X-x)$ are zero. Hence $f_T(X)=X^d-L_T(X)$ has degree less than $k$ and agrees with $y$ exactly on $T$. At every rate, at least four padding cosets are selected and at least four remain unused. The number of distinct supports is therefore at least $\binom{130019327}{4}$.

The rotations preserving the center act by $f(X)\mapsto c^{-d}f(cX)$ for $c\in\mu_n$. If a rotation fixes the message, it preserves its exact agreement set. The stabilizer of $T$ omits $-1$, since each of its distinguished eighth-root cosets contains precisely four consecutive sites and the half turn sends them to the other four. Every nontrivial subgroup of a cyclic 2-group contains $-1$. This proves the full orbit claim. Scaling the evaluation variable transfers it to a multiplicative coset.

The first template also yields a witness with larger agreement gain and shorter rotation orbits. Select $A\cup iA$ for $i$ of order four, which has first and second power sums zero. Pad with whole fourth-root cosets to a set of size $b+2$ in a quotient of order $m$ and base dimension $b$. At rates $1/2,1/4,1/8$ use $m=65{,}536$, and at rate $1/16$ use $m=131{,}072$ containing the same template. In each case the padding alone gives more than $2^{31}$ messages. Composing the message and center with $X^{n/m}$ gives $k+32{,}768$ agreements at the three higher rates and $k+16{,}384$ at sixteenth rate. These messages have rotation orbit of length $m$.

## When the degree bound can be attained

Let $N=2^a$, let $p\equiv1\pmod N$ be prime with $p>2^b$, and let $K\mid N$ be a power of two. Suppose $K<d<N$ and
\[
                 2b(d-K)>N(a-1).
\]
If $f$ of degree less than $K$ agrees with $X^d$ on $d$ sites of $\mu_N$, then $f$ is constant.

Indeed, $X^d-f$ is the monic locator of its $d$ roots $T$. Its top $d-K$ coefficients below the leading term vanish. Newton's identities give $\sum_{x\in T}x^j=0$ for $1\le j\le d-K$. For a primitive $z\in\mu_N$ put $h=N/2$ and
\[
 E(Z)=\sum_{j<h}(1_T(z^j)-1_T(z^{j+h}))Z^j.
\]
Suppose $E\ne0$. Multiplication by $E$ on $\mathbb Z[Z]/(Z^h+1)$ has nonzero integer determinant $D$, since $Z^h+1$ is irreducible over $\mathbb Q$. Its rows are signed shifts of the coefficient vector, of squared norm $w\le h$, where $w$ counts singly occupied antipodal pairs. Hadamard's inequality gives $|D|\le w^{N/4}$. Over $\mathbb F_p$ the matrix diagonalizes by evaluations at the odd powers of $z$. At least $r=\lceil(d-K)/2\rceil$ of its eigenvalues are zero. A rank deficit of $r$ forces $p^r\mid D$ by Smith normal form. But
\[
 p^r>2^{b(d-K)/2}>2^{N(a-1)/4}\ge w^{N/4},
\]
which contradicts nonzero $D$. This is the negacyclic determinant estimate for an individual indicator, whose signed differences have magnitude at most one. [Lean determinant bound](../../../ArkLib/Research/ProximityGap/Frontier/DyadicFoldedNorm.lean) · [Related descent for pairs of locators](low-degree-center-list-rigidity.md)

Thus $T=-T$. If $K>1$, its size $d$ is even and its locator is a polynomial in $X^2$. Writing $f(X)=f_1(X^2)$ descends the saturated witness to $(N/2,K/2,d/2)$. The displayed strict inequality persists because $a$ decreases by one and all three sizes halve. Iteration reaches dimension one, where the candidate must be constant. A nonzero constant has either zero or $\gcd(N,d)$ agreements, and the nonempty fibers of $X\mapsto X^d$ partition the grid. This proves the stated exact count. For a diagonal interleaved monomial center, any two message coordinates coincide on $d\ge K$ sites and hence coincide identically.

At the first unresolved half-rate radius, $t=759{,}250{,}124$ agreements are required. Every $\mu_{n/2}$-covariant scalar center has the form $X^j(A+BX^{n/2})$ with $0\le j<n/2$. Subtracting the codeword $AX^j$ leaves a monomial center or the zero center. Degree reversal $f(X)\mapsto X^{k-1}f(X^{-1})$ sends exponent $d\ge k$ to $n+k-1-d$ and preserves list size. A monomial with degree below $t$ has at most one candidate, and the formula above gives zero for degree exactly $t$. Consequently a failing half-rate center with this symmetry would require, up to these equivalences, a degree in **$[759{,}250{,}125,805{,}306{,}367]$**. Its residual polynomial would have more degree than the required number of agreement roots. This case is open.

Run `python3 scripts/probes/probe_character_orbit_lists.py` to check the templates, the capacity of every padding family, and the two numerical windows. The verifier also checks every site and every rotation of concrete two- and four-gain witnesses over $\mathbb F_{257}$ and exhausts the saturated monomial lists at order sixteen in both named fields.
