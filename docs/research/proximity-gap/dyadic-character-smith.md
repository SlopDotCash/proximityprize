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
