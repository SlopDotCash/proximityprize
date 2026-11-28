# Exact four-frequency optimum for quarter-rate three-head MCA

On the first named subgroup of order $n=2^{30}$, consider **any** coprime polynomials $P,Q$ of degree at most $n/4-2$ whose combined support contains at most four distinct monomial degrees. Their coefficients are arbitrary. The maximum of the three-head root score, allowing any three distinct targets, is exactly **$9n/16=603,979,776$**. The cubic on the normalized order-16 quotient attains it. Thus the earliest three-head MCA failure in this entire family is **480,946,859 errors**. The same root-score optimum holds in characteristic zero and in any characteristic $p>2^{153}$ admitting the grid. [Three-head score and witness](quarter-three-head-root-score.md)

There is also an exclusion for five frequencies on every normalized quotient of size at least $2^{23}$, over any field containing that subgroup. In particular an unrestricted first-prime quarter MCA failure at the first undecided count, **447,392,428**, requires at least **six distinct monomial degrees** among the reduced split-pencil numerator and denominator. This uses the necessary exact degree $2^{28}-2$, whose power-of-two divisor is only two. [Unrestricted divisibility criterion](quarter-successor-split-pencil.md)

## A mixed-parity member of the pencil

Remove a common monomial and let $g$ be the gcd of all support exponent differences. Divide exponents by $g$, put $k=\gcd(g,n)$ and $N=n/k$. A constant map cannot improve the score. For a nonconstant map of original degree $m$ the normalized degree is $m_0=m/g<N/4$, and every matched normalized site has $k$ preimages. It suffices to bound $2r-3m_0$ on $\mu_N$ by $9N/16$, where $r$ denotes the union size of the normalized fibers.

Both exponent parities occur in the normalized pencil. At most one target member can be supported on even exponents alone: two independent such members would span an entirely even pencil. The same applies to odd exponents. Hence among three distinct targets some member has both parities in its support. If the score beat $9N/16$, each of the three members would have more than $9N/32-m_0/2>5N/32$ roots, since the other two have at most $m_0$ each. We will exclude this many roots for the mixed member. At $N\le16$ the degree bound alone suffices, and $N=32$ follows from the existing [order-32 count for unrestricted pencils](quarter-three-heads-32-fibers.md#counting-incidences-across-the-32-quotient-fibers).

## Translation counts for trinomials and four terms

For a set of $s$ roots let $T_h$ denote the number whose translates by $h$ are also roots. Then $s(s-1)=\sum_{h\ne1}T_h$. A mixed binomial has at most one grid root because its exponent gap is odd. A mixed trinomial has $s(s-1)\le N-1$. In fact, choose as the eliminated term the complement of two terms of opposite parity. For $h\ne1$, subtract the appropriately scaled polynomial from its translate by $h$. At a shared root the resulting binomial vanishes. It cannot vanish identically, since its two remaining exponents have odd difference. If only one coefficient survives there are no shared roots. Write $B(N)=\lfloor(1+\sqrt{4N-3})/2\rfloor$.

For a polynomial with a single term of one parity and up to three of the opposite parity, its root count is at most
$$
 U(N)=\min\left(N,\left\lfloor\frac{1+\sqrt{1+4(N-1)B(N)}}2\right\rfloor\right).
$$
At any nonidentity shift, the phases $h^a$ of the two parities are disjoint because $h$ has even order. If all majority phases agree, eliminate them to leave a single monomial. Otherwise eliminate one majority phase. At least one majority term and the minority term remain, so the resulting mixed polynomial has at most three terms. This bounds every $T_h$ by $B(N)$.

Now suppose a four-term polynomial has two terms of each parity. Let $t$ be the gcd of $N$ and the two within-parity exponent gaps. The degree cap gives $t\le N/8$. Outside $\mu_t$ at least one parity splits into two phases. Eliminating one of these phases gives a mixed trinomial. At a nonidentity shift inside $\mu_t$ both parity-binomial parts must vanish individually at a shared root. Their simultaneous roots are empty or a single coset of $\mu_t$. Consequently
$$
       s(s-1)\le (N-t)B(N)+(t-1)t.
$$
There is a second bound $s\le t+N/t-1$: on any coset of $\mu_t$ the two parity parts become single monomials up to scalar multipliers. At most one coset makes both parts zero. On every other coset the odd gap between their exponents gives at most one zero. If $t=N/8$, both within-parity gaps equal $t$ as ordinary integers since the span is below $2t$. If the two binomial parts share a zero they share a factor $X^t-c$ and the remaining mixed binomial has at most one root. Otherwise there are no common roots at any of the $t-1$ exceptional shifts.

## Small orders and characteristic transfer

On $\mu_{128}$ a mixed trinomial in characteristic zero has at most two zeros. After an odd reparameterization and dividing by a monomial its equation has the form $Y^a=cY+b$ with $b,c$ nonzero. The two complex circles $|Y|=1$ and $|cY+b|=1$ meet at most twice. For $p>2^{153}$ the same holds: three distinct matches give dependent rows $(1,Y,Y^a)$ in the residue field. If the determinant were nonzero in the cyclotomic field, each of its 64 conjugates would have absolute value at most $3^{3/2}$ by Hadamard. Its norm is at most $3^{96}<2^{153}$. Hence the three rows are dependent over the complex numbers as well. Distinct inputs and outputs give a nonconstant affine map there; a scaling forces equal exponent differences, which also forces the finite-field map to be a scaling. Rank tests here hold over arbitrary coefficient extensions. On larger subgroups restriction to cosets, and on smaller ones extension of the same power to the 128th roots, permit replacing $B(N)$ by $\min(B(N),2\max(1,N/128))$. For a field lacking the larger grid one may extend the field to contain it.

With this sharper $B$, the verifier checks the preceding integer bounds against $5N/32$ for every dyadic $128\le N\le2^{30}$. At $N=64$ normalize the smallest exponent to zero; it suffices to examine the four-term supports $\{0,a,b,c\}$ with $0<a<b<c<16$. Eleven or more zeros contain three cyclically consecutive zeros of span at most $\lfloor 2\cdot64/11\rfloor=11$. Rotate the first to one. Every tested three-row evaluation matrix has rank three. The verifier evaluates its unique kernel polynomial, whenever all four coefficients are nonzero; the maximum in these tested cases is nine. Thus eleven zeros are impossible. For these order-64 matrices every minor of size at most four has absolute norm at most $16^{32}=2^{128}$. Ranks, zero coordinates in the one-dimensional kernels, and vanishing on every further site all transfer between the tested first prime, characteristic zero and the stated characteristic range. The proof of the four-frequency optimum follows. [All rank and finite arithmetic checks](../../../scripts/probes/probe_quarter_sparse_pencils.py)

## Five frequencies at the production scale

The following calculation uses the unrestricted $B(N)$ from the translation count; no characteristic lifting is used. A mixed member with five terms has parity counts $4+1$ or $3+2$. In the first case every nonidentity shift can eliminate the entire majority if it has one phase, or one phase from the majority otherwise. One gets zero shared sites in the first case and at most $U(N)$ in the second. Thus $s(s-1)\le(N-1)U(N)$.

For $3+2$ let $t$ be the grid gcd of the two minority exponents' difference, so $2\le t\le N/8$. At a shift outside $\mu_t$ eliminate one minority term; the other survives with the three majority terms. Inside $\mu_t$ use the degree bound $N/4-1$. Alternatively, on the $N/t$ separate cosets of $\mu_t$ the minority contribution becomes one monomial, except for at most one coset where it vanishes. Summing gives
$$
 s(s-1)\le(N-t)U(N)+(t-1)(N/4-1),\qquad s\le t+(N/t-1)U(t).
$$
These bounds also cover rational pencils with fewer than five terms in a chosen member: the three-plus-one bound handles that parity pattern directly, and for two-plus-two the four-term shift and coset estimates with the unrestricted $B$ suffice at these large sizes. The integer test checks all powers of two $t$ and all $2^{23}\le N\le2^{30}$. In particular at $N=2^{30}$ the mixed member has at most **142,946,455** roots, below $5N/32=167,772,160$. This rules out an improved three-head score on all these normalized quotients and proves the six-frequency necessity at the quarter successor.
