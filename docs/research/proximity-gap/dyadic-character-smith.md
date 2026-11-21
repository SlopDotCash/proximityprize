# Lifting the six binary character-kernel dimensions

Let $n=2^e$, $e\ge4$, and let $C$ be an integral circulant of size $n$. Suppose its symbol
reduced modulo two vanishes to order exactly six at $X=1$. For every $1\le r\le e-2$, its Smith
form over $\mathbb Z/2^r$ has $n-6$ unit entries and six zero entries. In particular its kernel
has $2^{6r}$ elements. The bound on $r$ is sharp for this class of circulants.

## Proof

Write $T=X-1$. Over the binary cyclic algebra $B=\mathbb F_2[X]/(T^n)$, multiplication
by the symbol has image $(T^6)$ and kernel $(T^{n-6})$. If $L$ is a power of two dividing
$n$, a coefficient vector has period dividing $L$ precisely when it lies in $(T^{n-L})$.
Indeed, cyclic shift by $L$ is multiplication by $X^L$, and $X^L-1=T^L$.

Fix any binary kernel vector. It is 8-periodic. Suppose it already has an integral representative
$v$ of period dividing $L=2^{j+2}$ with $Cv\equiv0\pmod{2^j}$, where $1\le j<e-2$.
The binary error $w=(Cv/2^j)\bmod 2$ also has period dividing $L$, since $C$ commutes with
the shift. It lies in $(T^{n-L})$. Here $8\le L\le n/2$, so $n-L\ge6$. Dividing by the
symbol's unit factor and removing $T^6$ gives a solution of $\bar C y=w$ in
$(T^{n-L-6})\subseteq(T^{n-2L})$. Lift the repeating block of $y$ to zeroes and ones. Then
$v-2^j y$ is $2L$-periodic and its image is zero modulo $2^{j+1}$. This constructs a
lift of every binary kernel vector through modulus $2^{e-2}$.

The binary rank fixes the number of odd Smith entries at $n-6$. A remaining nonzero Smith
entry of 2-adic valuation strictly between zero and $r$ would force its coordinate to be
even on every kernel vector modulo $2^r$. This contradicts the surjectivity just proved
after changing coordinates by the integral Smith basis. This proves the claim.

For sharpness take the integral symbol $T^6$. Its cokernel modulo $2^{e-1}$ is
the quotient of $(\mathbb Z/2^{e-1})[T]/(T^6)$ by the relation $(1+T)^n-1$.
This extra relation is nonzero, since the coefficient $\binom n4$ has 2-adic valuation
$e-2$. The cokernel therefore has fewer than $(2^{e-1})^6$ elements, precluding six zero
Smith entries at this precision.

## The two production fields

For either certified prime, take the length $2^{30}$ character sequence with coefficient
zero at index zero and the additive quadratic-character bit of $1-g^j$ at the other indices.
The eight residue classes modulo eight have respective parity sums $0,1,0,1,0,1,0,1$.
Thus its symbol is $X T^6\bmod T^8$, with exact order six. The modular result above applies
to **every** integral lift of these bits, including compatible higher-order character logs.
In particular the kernel modulo $2^{28}$ has **$2^{168}$** elements. Index reversal preserves
these Smith factors. The full four-fiber equations contain additional marking-dependent terms,
and their solvability is still open. [Four-fiber equations](four-fiber-quadratic-characters.md)

Lean proves the actual eight sums using the two subgroup generators certified in the repository.
The zero block is the derivative product $n/8$. Each nonzero block is the product of the
factors of $1-(g^r)^{n/8}$. A square-and-multiply calculation checks the eight resulting
field elements. Lean also proves the rank formula by rank-nullity on a quotient of polynomial
algebras. The higher-power induction and optimality proof are given above. Independent modular
elimination checks both conclusions at lengths 16, 32, 64 and 128.
[Character sums](../../../ArkLib/Research/ProximityGap/Frontier/NamedCharacterBlocks.lean) ·
[Binary rank](../../../ArkLib/Research/ProximityGap/Frontier/DyadicCharacterCirculant.lean) ·
[Elimination checks](../../../scripts/probes/probe_dyadic_character_smith.py)

The characteristic-two sequence viewpoint also occurs in the literature on zeros of SLCE
polynomials. The argument here uses products over eight subgroup cosets for the two specified
prime fields. [Zhang and Yang, arXiv:1702.05867](https://arxiv.org/abs/1702.05867)

## Exact Smith factors at the full character precision

Put $v=v_2(p-1)$ and use the additive discrete log of the $2$-primary character, with compatible
reductions at every lower precision. If $c$ is the nonresidue in the table, define the log of
$x\ne0$ by $x^{(p-1)/2^v}=(c^{(p-1)/2^v})^{\log x}$. The diagonal has coefficient zero.
Changing $c$ multiplies the matrix by a unit. Each row of the table omits the $n-6$ unit factors.
The final column lists the valuations of the other six factors over $\mathbb Z/2^v$, with
valuation $v$ denoting zero.

| Field | $v$ | $c$ | Number of coset products | Six valuations |
|---|---:|---:|---:|---|
| First named prime | 36 | 3 | 2,048 | 28, 28, 30, 30, 32, 35 |
| Second named prime | 30 | 29 | 32 | 29, 29, 30, 30, 30, 30 |

In particular only the second raw kernel lifts all six binary directions to modulus $2^{29}$.
At their full precisions the two kernel sizes are $2^{183}$ and $2^{178}$, respectively.
These are exact finite calculations for the two specified matrices. [Reproducible certificate](../../../scripts/probes/probe_named_character_smith.py)

### Compressing the billion-dimensional quotient

Choose an integral lift $K(X)$ of the character coefficients, and put
$F_k(T)=(1+T)^{2^k}-1$. In the local power-series ring at $(2,T)$ the factor $K(1+T)$ is a unit
times a monic sextic $P(T)$ with $P\bmod 2=T^6$. The following elementary lifting argument
works at every finite precision. Start with $P=T^6$ and the unit $U=(K\bmod2)/T^6$.
If $K-PU=2^j E\bmod 2^{j+1}$, first choose the unique $\Delta$ of degree less than six with
$\Delta U=E\bmod(2,T^6)$. After subtracting $\Delta U$ the error is divisible by $T^6$ modulo two.
This determines a correction to $U$, and $P+2^j\Delta$ is the next monic factor. The constant
term of $U$ remains odd. This also gives uniqueness of the monic factor at each precision.

Work in the free rank-six ring $A=\mathbb Z_2[T]/P$. The original cyclic cokernel modulo
$2^v$ is $A/(2^v,F_{30})$. Indeed taking the two quotients by $F_{30}$ and by $K$ commutes.
Passing to power series preserves both quotient calculations at finite precision, since modulo
two their respective defining equations are powers of $T$ up to a unit and therefore $T$ is
nilpotent in each finite-precision quotient.

In $A$ we have $T^6\in2A$, hence $F_3\in2A$. From $F_{k+1}=2F_k+F_k^2$ it follows that
$G_k=F_k/2^{k-2}$ is integral for $k\ge3$, and
$$
G_{k+1}=G_k+2^{k-3}G_k^2.
$$
Write $s=v-28$ and $a=s+1$. To compute $G_{30}\bmod 2^s$ it suffices to know $P\bmod 2^a$.
First reduce $F_3$ by $P$ modulo $2^a$ and divide its six even coefficients by two. Then use
the displayed recurrence modulo $2^s$.

For $L=2^{a+2}$, reduction of $K$ modulo $X^L-1$ preserves $P\bmod 2^a$. In fact in $A$,
$X^L-1=F_{a+2}\in2^a A$, so the polynomial of the $L$ block sums has zero remainder on
division by $P$ at this precision. Modulo two its vanishing order at $T=0$ is still six
because $L>6$. Uniqueness of the monic factor identifies its factor with $P$ modulo $2^a$.
The block sums of character logs are the logs of $n/L$ and $1-(g^{n/L})^j$ for $0<j<L$,
by the same subgroup product identities as in the binary proof.

The monic sextics at precisions $2^9$ and $2^3$, in order of ascending coefficients below
the leading term, are $(400,176,452,440,54,290)$ and $(0,0,6,4,6,0)$. The checker lifts
them by monic polynomial remainders, computes $G_{30}$ and reduces its six-by-six multiplication
matrix. Adding 28 to the resulting valuations gives the table because $F_{30}=2^{28}G_{30}$.
The checker compares this compressed calculation with dense Smith elimination on 36 smaller
circulants, including arbitrary even lifts of order-six binary kernels.

## Effect of deleting marked output rows

There is also an exact binary rank formula for the raw convolution if its values are inspected
only outside a set $M$ of indices. Let $E$ and $O$ be the numbers of **distinct** even and odd
classes modulo eight met by $M$. The projected image has codimension
$$
6-\min(E,3)-\min(O,3)
$$
in the remaining output space. In particular, once the markings meet at least three classes
of each parity, every prescription on the remaining rows has a preimage under the raw
convolution. This surjectivity holds at every finite 2-adic precision for any integral lift,
because a maximal minor of the projected matrix is odd. This calculation leaves all input
coordinates free. Restrictions on the inputs in the four-fiber system still apply.

Indeed the six compatibility equations for a full binary output $b$ are the Hasse coefficients
of orders $0,\ldots,5$ of $b(1+T)$. The column at $j$ depends only on $j\bmod8$, since
$(1+T)^8=1\bmod T^6$. The binary relations between the eight distinct columns are precisely
the polynomials of degree less than eight divisible by $T^6$. They are generated by
$1+X^2+X^4+X^6$ and its odd translate. Thus the available columns on $M$ span a space of
dimension $\min(E,3)+\min(O,3)$. Allowing arbitrary missing outputs quotients the six full
compatibility equations by exactly this space.
