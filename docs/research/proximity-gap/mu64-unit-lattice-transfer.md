# All vanisher-ratio comparisons lift at order 64 in both named fields

Let $p$ be either named prime and $H=\mu_{64}$ in its prime field. For any disjoint subsets $P,Q\subset H$ and any two sites outside them, the corresponding monic vanisher ratio $L_P/L_Q$ has equal values at the sites if and only if it does so for complex roots with the same exponents. The result is uniform over the supports, their sizes, and the choice of primitive root.

Two consequences on both named order-64 domains are as follows.

- At rate one quarter, the saturated rank-two quartet with four singletons and sixty double sites is impossible at 32 errors, independent of how its sites are assigned. The six necessary ratio tests transfer, so the characteristic-zero parity argument gives at most ten changed double labels under the half-turn. The polynomial argument recovering all labels, and its contradiction for odd row degree fifteen, work in these prime fields. [Parity and label recovery](quarter-dyadic-parity.md)
- At rate one half, **the exact maximum list size at seventeen errors is three**. Four scalar words would produce a three-split pencil of degree fifteen or four constant neighbour-set ratios from a 4-cycle. The pencil ratios lift and their complex parity conditions would require $3(15-2)\le32$. The four cycle ratios likewise lift and give the existing parity contradiction. Three words are attained by the geometric-sum center with $M=4,h=16$. The maximum is the same at every positive interleaving width. For any four vector words choose one nonzero coordinate-difference vector from each of the six pairs; the union of their annihilating hyperplanes omits a linear functional since $p>6$. That functional takes the candidates to four distinct scalar words within the same error radius, while padding the scalar witness with zeros gives three words at every width. The same reasoning and the order-32 transfer give maximum three at length 32 and nine errors. [Overlap classification and parity obstructions](dyadic-radius-successor-list-three.md) · [Geometric-sum witness](PROGRESS.md#2026-11-21--exact-list-of-the-geometric-sum-center) · [Order-32 transfer](quarter-mu32-unit-sieve.md)

## Bounding the exponents

Choose an order-64 root $z$, and let $u_r=1-z^r$ for odd $1\le r<32$. Every nonzero difference of subgroup points is a power of $z$ times a monomial in these sixteen units. Factor $1-z^{2^a d'}$ as the product of the $2^a$ factors $1-z^{d'+64j/2^a}$ for odd $d'$, reducing odd exponents modulo sign. For a fixed $r$, its contribution from difference $t$ counts the solutions to $t=\pm 2^a r$ modulo 64, $0\le a<6$. When the plus and minus residues agree at $a=5$, both count.

With $w=1_P-1_Q$, comparing ratios at exponent sites $x,y$ yields a root of unity times $\prod_r u_r^{e_r}$, where
\[
 e_r=\sum_{a=0}^5\bigl(w(x+2^a r)+w(x-2^a r)-w(y+2^a r)-w(y-2^a r)\bigr).
\]
It follows that $|e_r|\le24$. The same formula gives $4k$ for a subgroup of order $2^k$. [Formal exponent bound](../../../ArkLib/Research/ProximityGap/Frontier/DyadicUnitExponentBound.lean)

## Exact bounded independence in the named fields

We prove $\prod_r u_r^{64 e_r}=1$ with $|e_r|\le24$ only for the zero vector. The certificate uses projections of the multiplicative groups to orders
\[
 M_1=2^{36}7^3\cdot26407\cdot279991\cdot4533259,
 \qquad M_2=2^{30}\cdot3\cdot5^2\cdot7\cdot71\cdot202172094073993.
\]
The seeds are $g=3,37$ respectively, with $z=g^{(p-1)/64}$. For each unit the certificate supplies a projected logarithm $a_r$ and checks $u_r^{(p-1)/M}=g^{a_r(p-1)/M}$ by direct exponentiation. The order of $g^{(p-1)/M}$ is certified from the displayed factorization. Hence any bounded relation vector lies in
\[
 \Lambda=\{e\in\mathbb Z^{16}:\sum_r a_r e_r=0\pmod{M/64}\}.
\]
The verifier tests every row of the supplied integer basis against this congruence. It computes its squared determinant by exact rational Gram–Schmidt, comparing with the square of the kernel index $(M/64)/\gcd(M/64,a_1,\ldots,a_{31})$, with the indices running over odd residues. Thus the supplied rows span the entire kernel. Basis reduction and the method used to obtain the logarithms lie outside the trust requirement. [Certificate data](../../../scripts/probes/mu64_unit_lattice_certificates.json)

Finally enumerate every lattice point of squared Euclidean norm at most $16\cdot24^2=9216$. In orthogonal row coordinates, after fixing the later coefficients, the next integer coefficient $t$ must satisfy $(t-c)^2 b\le R$, with $c,b,R$ rational and $b>0$. The verifier computes both closed integer endpoints with an integer square root and recurses with the exact remaining radius. It tests each point in the coordinate box in the full prime field.

| Field | Points in the closed sphere | Points in the box | Products equal to one |
|---|---:|---:|---:|
| First named prime | 1025 | 1 | 1 |
| Second named prime | 97043 | 19 | 1 |

The one identity is the zero vector in both rows. Reversing the basis order changes the orthogonal coordinates and yields the same counts. Both modes use only the Python standard library. [Exact verifier](../../../scripts/probes/probe_mu64_unit_lattice.py)

If a ratio comparison holds in the finite field, raising to the 64th power kills the phase and the bounded check forces every $e_r$ to be zero. The original quantity is then a power of $z$ in both characteristics, so its equality to one transfers exactly. The reverse direction follows by specializing the exact factored cyclotomic equality. A different primitive root permutes the units up to signs and 64th roots of unity and gives the same bounded independence. This result concerns order 64. The corresponding transfer at the production length remains open.
