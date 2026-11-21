# A norm obstruction for dyadic prime-field subgroups

Let $n=2^j\ge4$, $d=\varphi(n)=n/2$, $K=\mathbb Q(\zeta_n)$, and write a bar for complex conjugation. For every nonzero algebraic integer $A\in K$, at least one of the following holds.

1. $A/\bar A$ is a root of unity. Its principal ideal is invariant under conjugation and its absolute field norm is a square or twice a square.
2. Its absolute field norm $D$ satisfies $7^d\le 2^d D^8$.

In particular an odd prime norm must be at least $(7/2)^{n/16}$. This covers polynomials in the primitive root with arbitrarily many coefficients and with exponents depending on $n$. The proof applies the unramified Frobenius estimate of Amoroso and Dvornicich to the quotient by conjugation. [Amoroso and Dvornicich](https://doi.org/10.1006/jnth.1999.2451)

## Proof

The automorphism $s(\zeta_n)=\zeta_n^7$ commutes with conjugation. Every algebraic integer of $K$ lies in $\mathbb Z[\zeta_n]$. Reducing its integral polynomial expression modulo the ideal $7\mathcal O_K$ gives $s(A)\equiv A^7$, by the characteristic-seven Frobenius. The same holds for $\bar A$. Consequently
$$
 C=A^7\,s(\bar A)-\bar A^7\,s(A)\in7\mathcal O_K.
$$
If $C=0$, writing $x=A/\bar A$ gives $s(x)=x^7$. Iteration through the finite order $h$ of $s$ yields $x^{7^h-1}=1$.

If $C\ne0$, the nonzero integer norm of $C/7$ has magnitude at least one, so $7^d\le |N(C)|$. At every complex embedding $t$, abelianity makes $t(\bar A)=\overline{t(A)}$, whence
$$
 |t(C)|\le 2|t(A)|^7|(ts)(A)|.
$$
The embeddings $ts$ permute the embeddings $t$. Multiplication gives $|N(C)|\le2^dD^8$.

All roots of unity of $K$ are powers of $\zeta_n$. Suppose $x=\zeta_n^a$. If $a=2b$, then $A/\zeta_n^b$ lies in the real subfield and has square norm to $\mathbb Q$. If $a$ is odd, put $B=1+\zeta_n^a$. Then $B/\bar B=\zeta_n^a$, so $A/B$ is real. Also $N(B)=\Phi_n(-1)=2$. Hence $D=2r^2$ for some rational $r$. Since $D$ is integral, writing $r$ in lowest terms forces its denominator to be one. In either case the quotient $A/\bar A$ is a unit and conjugation fixes the principal ideal.

## Consequences for split primes

Let $p\equiv1\pmod n$, $g\in\mathbb F_p^\times$ have order $n$, and $P=(p,\zeta_n-g)$ denote the corresponding prime of $K$. Conjugation sends $P$ to the distinct prime associated to $g^{-1}$.

- If $F\in\mathbb Z[X]$, $F(g)=0$ and $F(g^{-1})\ne0\pmod p$, then $A=F(\zeta_n)$ is nonzero and its principal ideal is not fixed by conjugation. Thus $7^{n/2}\le2^{n/2}|N(F(\zeta_n))|^8$. For $p\le n^B$ with fixed $B$, the norm cofactor is exponentially large in $n$.
- For every principal ideal $P^h$, the same proof gives $7^{n/2}\le 2^{n/2}p^{8h}$. In particular the ideal class of $P$ has order at least $n\log(7/2)/(16\log p)$.
- More generally a nonzero principal ideal of norm strictly below the threshold has identical multiplicities at primes exchanged by conjugation. A split rational prime dividing that norm must divide it to at least the second power.

In a putative family of examples obtained from an odd prime norm $p$, the trivial bound $|\eta|\le n$ therefore gives
$$
 \limsup_{n\to\infty} \frac{|\eta|}{\sqrt{n\log_2(p/n)}}\le
 \sqrt{16/\log_2(7/2)}<2.98.
$$
This excludes an unbounded logarithmic coefficient from that construction. An arbitrary prime divisor of a large composite norm can still give a much smaller field, and the proof supplies no period bound at that prime.

The published height estimate of Ishak, Mossinghoff, Pinner and Wiles gives a stronger numerical ceiling. Every conjugate of $x=A/\bar A$ has modulus one. Its logarithmic Weil height equals the logarithm of the norm of its denominator ideal divided by $d$, so $h(x)\le (\log D)/d$. Take the smallest dyadic conductor $m$ in which a root-of-unity multiple of $x$ occurs, allowing twists by roots in $K$. Such twists preserve height and all archimedean moduli. A nontorsion quotient cannot reduce to a rational number, so $m\ge4$. For $m=4$, neither $(1+i)x'$ nor $(1-i)x'$ is rational for the minimizing twist $x'$, since both have modulus $\sqrt{2}$. For $m\ge8$ the condition $8\mid m$ applies. Theorem 1(ii) of the cited paper now gives $h(x)\ge0.210291$ in both cases. This yields $D\ge\exp(0.210291d)$ and a limiting prime-norm ratio at most $\sqrt{2\log 2/0.210291}<2.568$. [Primary paper, Theorem 1(ii)](https://www.math.ksu.edu/~pinner/RevisedAmoroso.pdf)

The pinned Lean kernel also verifies the split-relation inequality for every conductor coprime to seven. The theorem takes an actual primitive root in any field of characteristic prime to the conductor, two opposite evaluations of the input integer polynomial, and returns the exponential inequality for its integer cyclotomic resultant. Its proof includes coefficientwise divisibility, archimedean norm multiplication, finite-order descent, and transfer through the cyclotomic polynomial. [Lean proof](../../../ArkLib/Research/ProximityGap/Frontier/DyadicFrobeniusNorm.lean)

## Three-term supports

For a sum $A=u+v+w$ of three $n$-th roots, the alternatives are especially restrictive. An opposite pair gives norm one. In the absence of opposite pairs, any representation as a positive multiset of three roots is unique among such reduced representations. Indeed $1,\zeta_n,\ldots,\zeta_n^{d-1}$ form a rational basis and the coefficient of each basis vector records the signed difference of the two corresponding multiplicities.

If $A/\bar A=\zeta_n^a$, uniqueness forces the exponent multiset to be stable under $e\mapsto a-e\pmod n$. The involution either has a fixed element and swaps the other two, giving a geometric progression of roots, or fixes all three. The fixed exponents, when they exist, are exactly an opposite pair, so the latter case forces all three roots equal. For a progression $t,tz,tz^2$ with $z\ne1$, the identity $1+z+z^2=(1-z^3)/(1-z)$ gives norm one because the automorphism $\zeta_n\mapsto\zeta_n^3$ exchanges the numerator and denominator up to direction. Equal roots give norm $3^d$. This proves the explicit inequality for every other ternary sum as well. It implies that every unit of this form comes from an opposite pair or a nonconstant geometric progression.

The probe computes the exact integer norm of all $1+\zeta_n+\zeta_n^c$ through $n=8192$ by quadratic descent. Rotation and an odd Galois conjugation produce this form for every ternary support whose exponent differences have gcd one with $n$. For all smaller conductors, the tower norm raises the reduced norm to the extension degree. The minimum nonexceptional normalized log norm at $8192$ is about $0.281200$, realized at $c=5$. [Exact probe](../../../scripts/probes/probe_dyadic_ternary_norm.py)
