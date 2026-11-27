# A differential equation cannot contain the large family of short polynomial sections

Work over an algebraically closed field \(k\) of characteristic \(p>3078\), with \(K=k(X)\). The ordinary derivative on \(K\) sends \(X\) to one. Let \(s=30,\ v=8,\ u=1538,\ M=1072766345\). Suppose a nonzero \(G\in k[X,Z,V]\) of degrees at most \(s,v\) in \(Z,V\) contains the jets \((U_i,U_i')\) of \(M\) distinct polynomials \(U_i\in k[X]\) of degree at most \(u\), as identities in \(K\).

Remove factors depending only on \(X\). One irreducible factor \(g\) contains at least \(\lceil M/38\rceil\) of these points, since the sum of the total \((Z,V)\)-degrees of all factors, counted with multiplicity, is at most 38. Take \(g\) primitive over \(k[X]\); it is irreducible in \(K[Z,V]\) by Gauss's lemma. Write \(b=\deg_{Z,V}g\le38\). Its degree in \(V\) is positive, since a nonzero polynomial in \(K[Z]\) of degree at most \(b\) cannot vanish at that many distinct \(U_i\). Thus \(T=g_V\) is nonzero and relatively prime to \(g\), because \(\deg_V g\le8<p\).

## Differentiating on the irreducible component

On the localized coordinate ring \(K[Z,V,T^{-1}]/(g)\), with \(B=-g_X-Vg_Z\), take the derivation
\[
 \partial=\partial_X+V\partial_Z+(B/T)\partial_V.
\]
It preserves the relation \(g=0\) since \(\partial g=0\). In particular \(\partial Z=V\). For all \(j\ge1\) put
\[
 \partial^jZ=P_j/T^{\,2(j-1)},\qquad P_1=V .
\]
If \(P=P_j\) and \(a=2(j-1)\), a polynomial numerator for \(P_{j+1}\) is
\[
 T^2(P_X+VP_Z)+TBP_V
       -aP\big[T(T_X+VT_Z)+BT_V\big].
\]
Only the \((Z,V)\)-degree matters for the following count. We have \(\deg T\le b-1,\ \deg B\le b\), so each step adds at most \(2b\) to the degree. Therefore \(\deg_{Z,V}P_{u+1}\le1+2bu\).

At a polynomial jet on \(g\) with \(T(X,U_i,U_i')\ne0\) in \(K\), substitution commutes with the derivation. Indeed, differentiating \(g(X,U_i,U_i')=0\) gives \(U_i''=B/T\) at that jet. Hence \(P_{u+1}(X,U_i,U_i')=0\), because the ordinary derivative of order \(u+1\) kills \(U_i\). The simultaneous points of \(g=T=0\) number at most \(b(b-1)\) by the projective Bézout bound over an algebraic closure of \(K\). If \(g\) does not divide \(P_{u+1}\), the points on the remaining intersection number at most \(b(1+2bu)\). The bound applies over \(K\) even if \(g\) splits after scalar extension: coprime plane polynomials over a field have zero-dimensional affine intersection, and acquire no common component after extending the field. Homogenization to the individual total degrees creates no common factor at infinity.

The sum of these two bounds is at most \(38^2(1+2\cdot1538)=4443188\), below \(\lceil1072766345/38\rceil=28230694\). Consequently \(g\mid P_{1539}\), and \(\partial^{1539} Z=0\) on this irreducible component. [Exact arithmetic and differential controls](../../../scripts/probes/probe_quarter_list_jet_derivation.py)

## The required quadratic branch cannot be a solution

Let \(H\) generate a separable quadratic extension of \(K\), let \(H'=dH/dX\), and let \(D=[k(X,H):k(H)]\). The primitive irreducible equation of \(H\) in \(k[X,Z]\) has degree \(D\) in \(X\), by viewing it as the minimal equation of \(X\) over \(k(Z)\). Suppose \(\deg_X G\le e\), \(15e<D\), and \(g(X,H,H')=0\). Each irreducible factor has \(X\)-degree at most \(e\). The resultant \(\operatorname{Res}_V(g,T)\) is nonzero, since \(g\) is primitive and irreducible over \(K[Z]\) with positive \(V\)-degree and \(T=g_V\ne0\). Its \(X\)-degree is at most \((2\deg_Vg-1)e\le15e\) by the Sylvester determinant. Its value at \(Z=H\) cannot vanish by the minimal-equation degree. A Bézout identity for the resultant implies \(T(X,H,H')\ne0\). Substitution at this jet commutes with the derivation for the same reason as for the polynomial sections. The component would therefore force \(d^{1539}H/dX^{1539}=0\).

In the quarter-rate instance, at a simple root \(b_0\) of \(N\) the function \(H=(2B_0-A S_0+2\sqrt N)/A^2\) has a local expansion
\[
 H=c(X-b_0)+(X-b_0)^{1/2}d(X-b_0)
\]
with \(c,d\in k[[X-b_0]]\) and \(d(0)\ne0\). Indeed \(N(b_0)=0\) makes \(A(b_0)\ne0\) by \(\gcd(A,B_0)=1\) and \(N\equiv B_0^2\bmod A\); the residual unit after removing \(X-b_0\) has a square root in the power series ring. The simple roots exist because \(N\) has at least \(n-3080\) distinct roots and degree at most \(n-4\). At order \(q=1539\), the odd term has leading coefficient \(d(0)\prod_{j=0}^{q-1}(1/2-j)\) at exponent \(1/2-q\). This is nonzero for \(p>2q\); every other odd term has strictly larger exponent and the integer powers cannot cancel it. This contradicts the required vanishing. [Quarter-rate pencil and its physical roots](complementary-list-pencil.md)

The argument establishes that the component carrying sufficiently many polynomial sections cannot also contain the jet of \(H\) under the stated height bound. For its application one must force that same component to contain \(H\) by the intersection-multiplicity estimate. [Interpolation and application](quarter-list-moving-jets.md)
