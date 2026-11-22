# Field-uniform list bounds from the 128th roots of unity

The two-error sample argument at length 128 and dimension 64 needs a uniform bound of 12 on an integer sum of penalties. It tests multiplicities of products of two ratios and sums their charges after multiplying by a third ratio. All relevant equalities of triple products transfer from any prime field of order greater than $2^{224}$ containing the 128th roots of unity to characteristic zero. Six rows over an auxiliary field then suffice for all these prime fields. [Two-error counting argument](dyadic128-two-error-slices.md)

## Lifting equalities of products

Let $z$ have order $n>2$ in the prime field, with $p$ coprime to $n$. Rotate the distinguished sites to $1,z^d$, and put $f_i=(z^i-1)/(z^i-z^d)$ for the other exponents. For lists $A,B$ of $s$ such exponents, form the integer polynomial
\[
 C(X)=\prod_{i\in A}(X^i-1)\prod_{j\in B}(X^j-X^d)
       -\prod_{i\in A}(X^i-X^d)\prod_{j\in B}(X^j-1).
\]
If the products of the ratios are equal at $z$, they are equal at $z^{-1}$ as well. Inverting every site multiplies each ratio by the same $z^d$. The two roots are distinct, so the reductions of $C$ and $\Phi_n$ share a quadratic factor. The integer resultant is divisible by $p^2$. This multiplicity follows by putting the Sylvester matrix in a basis exposing its corank modulo $p$. [Integer resultant divisibility](../../../ArkLib/Research/ProximityGap/Frontier/ModularResultantMultiplicity.lean)

For each primitive complex $n$th root, every binomial factor has modulus at most two. Multiplying the bound over all primitive roots gives
\[
 |\operatorname{Res}(\Phi_n,C)|\le 2^{(2s+1)\varphi(n)}.
\]
If this is less than $p^2$, the resultant is zero, so $\Phi_n$ divides $C$ over the integers. The equality consequently holds at every primitive $n$th root in every characteristic coprime to $n$. No equality for a test scalar chosen independently of the sites is needed. Whenever a scalar makes a positive contribution, a triple of sites represents it. Each alternative at each contributing site gives a triple with the same product. All these triples transfer to the single target represented by the chosen triple. [Cyclotomic norm and ratio products](../../../ArkLib/Research/ProximityGap/Frontier/RatioProductNorm.lean)

## Six separations and a finite interval of prime fields

Take $n=128$ and $s=3$. Then $2^{(2s+1)\varphi(n)}=2^{448}$. The auxiliary field of order 167772161 has a primitive 128th root. Given two distinct nonantipodal sites, write their difference of exponents as $2^j t$ with $t$ odd. An odd multiplier congruent to $t^{-1}$ modulo $128/2^j$ sends the separation to $2^j$. Selecting the corresponding primitive root in the transfer sends the remaining 126 sites bijectively to the remaining auxiliary sites. Thus the six separations $1,2,4,8,16,32$ cover every row.

The exact auxiliary-field replay gives worst penalties $9,12,12,12,12,12$. For fixed separation it constructs the multiplicity of each product of two distinct remaining ratios. For each product with multiplicity two it adds one to the table at every product times a remaining ratio. Multiplicities at least three add three. The maximum table entry is the asserted bound for all choices of the scale. The replay also checks the field and primitive-root arithmetic. [Exact small-field calculation](../../../scripts/probes/probe_cyclotomic_list_transfer.py)

For each prime $p\equiv1\pmod{128}$ whose integer budget $B=\lfloor p/2^{128}\rfloor$ satisfies
\[
361269899996423739323753777598085\le B\le184239584937908329739504521356773474,
\]
the lower endpoint ensures $p>2^{224}$ and the upper endpoint gives $128B<\binom{128}{65}$. Also $\binom{B+1}{2}\le p$, which permits scalar projection at every positive interleaving width. The two-error upper bound at 62 errors and the prescribed-product attack at 63 errors therefore give an exact first failure at 63. Multiplying or translating the evaluation sites preserves the scalar code under the corresponding substitution in its message polynomials. In particular the conclusion applies to every 128-site multiplicative coset in these fields. The Lean kernel checks all six rows in blocks of 512 integer operations per index range. Each concrete row bounds the number of tags for any scale, and the transfer then applies to every pair in the supplied field. The fully quantified four-rate thresholds hold at every positive interleaving width. [Finite certificate](../../../ArkLib/Research/ProximityGap/Frontier/AuxiliaryRatioSlotChecks.lean) · [Unconditional four-rate theorem](../../../ArkLib/Research/ProximityGap/Frontier/Smooth128PrimeBand.lean)
