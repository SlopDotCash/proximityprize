# Three transpositions for a non-dihedral involution on dyadic roots

Let $H$ be the complex roots of unity of order dividing $N=2^m$. A projective involution exchanging at least four disjoint pairs of elements of $H$ is either $x\mapsto -x$ or $x\mapsto t/x$ for $t\in H$. The same assertion holds on prime-field copies of $H$ when $12^{\varphi(N)}<p^2$. The latter size condition holds at length 128 for every prime in the prize size range. The pair-product transfer is kernel checked. The full all-orders complex argument below is a written proof undergoing formalization.

Fu proved a sharp upper bound of fourteen points for a nontrivial projective equivalence between arbitrary sets of complex roots of unity. Here the roots have power-of-two order, the projectivity is an involution, and each specified orbit has size two. [Fu](https://arxiv.org/abs/1905.01510) · [Hubbard’s elementary method for general projectivities](https://arxiv.org/abs/2410.17412)

## The parity split

An involution exchanges $x,y$ on the conic $Axy+B(x+y)+C=0$. If $B=0$ it is a reciprocal map. Otherwise normalize $B=1$. Exclude the negation map. Distinct transpositions have distinct products, since equal products imply equal sums. At most one transposition is antipodal, as $-Ax^2+C=0$ for such a pair. The case $A=C=0$ is precisely negation. With two transpositions the coefficients $A,C$ belong to $K=\mathbf Q(\zeta_N)$ by subtraction. Nondegeneracy gives $AC\ne1$.

For $N\ge8$, apply the automorphism $\sigma(\zeta)= -\zeta$. Call sites even or odd according to the parity of their exponents. Write $A=A_0+A_1$ and $C=C_0+C_1$ for the invariant and anti-invariant parts. Two even-even pairs force $A_1=C_1=0$ by subtracting the two equations on their distinct products. Every odd-odd pair must then be antipodal. There can be no cross pair: for even $x$ and odd $y$ its two equations would give $x+C=0$ and $Ax+1=0$. Two odd-odd pairs give the same conclusions with parities interchanged by rotating the grid.

For a cross pair with $x$ even, $y$ odd and $T=xy$, one has
\[
 x=-A_1T-C_0,\qquad y=-A_0T-C_1.
\]
At most two disjoint cross pairs exist. Indeed, $T=(A_1T+C_0)(A_0T+C_1)$ is quadratic. If it holds identically, $A_1A_0=0$ and one endpoint is fixed. Thus in a configuration of four pairs containing a cross pair there must be precisely two cross pairs, one even-even pair and one odd-odd pair.

## Ruling out the four mixed pairs

Write the cross pairs $(x_i,y_i)$, $i=1,2$, and put $U=x_1x_2$, $V=y_1y_2$, $D=x_1y_1-x_2y_2$. The cross equations give
\[
 A_0=-(y_1-y_2)/D,\quad A_1=-(x_1-x_2)/D,\quad C_0=A_0U,\quad C_1=A_1V.
\]
Thus an even-even pair has product $-V$ and sum $A_0(V-U)$. An odd-odd pair has product $-U$ and sum $A_1(U-V)$. If $U=V$, both pairs are antipodal, which was excluded.

Use the additive valuation above 2 normalized by $v(1-\zeta)=1$. For $k$ nonzero modulo $N$, $v(1-\zeta^k)=2^{v_2(k)}$. This follows because $1-\zeta^k$ differs from $1-\zeta^{2^{v_2(k)}}$ by a unit, and the latter has absolute field norm $2^{2^{v_2(k)}}$. Let $u,v'$ be the exponents of $U,V$, and let $L$ be the exponent of $x_1y_1/(x_2y_2)$. The even integers $v'-u$ and $L$ differ modulo four by two, because their difference is twice the difference of an odd and an even exponent. Consequently $\Delta=v(V-U)-v(D)$ is nonzero.

The valuations of the two same-parity sums are respectively $v(y_1-y_2)+\Delta$ and $v(x_1-x_2)+\Delta$. Exactly one of the even-even sum and $y_1-y_2$ has valuation two. Indeed, writing one even-even endpoint as $\zeta^a$, the sum's valuation is that of $1-\zeta^{v'-2a}$ by the product $-V$, whereas the difference exponent for $y_1-y_2$ is congruent to $2-v'$ modulo four. The valuation is well defined because 2 is totally ramified and has residue degree one in this cyclotomic field. The same statement holds for the odd-odd sum and $x_1-x_2$, with the roles of zero and two modulo four interchanged.

If $\Delta>0$, both differences have valuation two, giving $v'\equiv0$ and $u\equiv2\pmod4$. This forces $v(V-U)=2<v(D)$, a contradiction. If $\Delta<0$, both same-parity sums have valuation two, giving $v'\equiv2$ and $u\equiv0\pmod4$. Again $v(V-U)=2$, and now $v(y_1-y_2)=v(x_1-x_2)=v(D)$. This is impossible: the exponent $L$ is the sum of the two difference exponents, and the sum of two integers having the same finite 2-adic order has strictly greater order. The four mixed pairs cannot occur.

## One antipodal pair in the opposite parity

If all sites have the same parity, rotate and work at order $N/2$. Otherwise, absent cross pairs, one class has at least three pairs and the other has exactly one antipodal pair. Rotate to make the first class even. The exceptional pair is $a,-a$ with $a$ odd, so on the smaller grid $H'=\mu_{N/2}$ the remaining involution has equation
\[
 Bxy+x+y+Bc=0,\qquad c=a^2.
\]
Here $c$ is an odd power of the primitive root of $H'$, and $B\ne0$. We show that at most two pairs in $H'$ satisfy this equation. The assertion is immediate for $|H'|\le4$.

Split coefficients again, now in the field of the smaller grid. The coefficients belong to that field whenever two distinct pairs exist. Its parity automorphism negates $c$. Two even-even or two odd-odd pairs are impossible, since they would force $B$ and $Bc$ to have the same parity. Three cross pairs were already excluded.

If there are two cross pairs, the displayed formulas for $C_0,C_1$ applied to $C=Bc$ give $B_1c=B_0U$. In particular $|x_1-x_2|=|y_1-y_2|$. Two unordered chords of equal length on the unit circle differ by a rotation. The orientation giving $x_1y_1=x_2y_2$ is excluded, so $y_i=\lambda x_i$ for an odd power $\lambda$ of the primitive root. For an additional even-even pair $a',b'$ the sum formula gives
\[
 (a'+b')(x_1+x_2)=(1-\lambda^2)x_1x_2.
\]
The left side has valuation at least four, while $1-\lambda^2$ has valuation two. The denominator $x_1+x_2$ used to derive the identity cannot vanish because $D=\lambda(x_1^2-x_2^2)\ne0$. An additional odd-odd pair reduces to the same case by a rotation interchanging the classes. This scales $c$ by a square and preserves its odd exponent.

Finally suppose there is one pair $a',b'$ even, one odd pair and a cross pair $(x,y)$. Write $T_E,T_O$ for the two same-parity products. The coefficient equations give $B_1T_E+B_0c=B_0T_O+B_1c=0$. Hence $|B_0|=|B_1|\ne0$, and the same-parity sums, $B_0(T_O-T_E)$ and $B_1(T_E-T_O)$, have the same length. Equal absolute values of the sums imply equal chord lengths, since $|a-b|^2=4-|a+b|^2$ on the unit circle. The two pairs consequently differ by a rotation $\lambda$, an odd power. Substituting both pairs into the conic gives $c=\lambda a'b'$. Both sums are nonzero by $T_E\ne T_O$. Substitution of the cross pair now gives
\[
 (x+y)(1+\lambda)a'b'=(a'+b')(xy+\lambda a'b').
\]
Its invariant part forces $x=-\lambda y$. Consequently $(\lambda^2-1)xa'b'=(a'+b')(-x^2+\lambda^2a'b')$, again impossible since the left side has valuation two and the right side at least four. This finishes the descent. At order at most four there are too few sites for four transpositions.

## Transfer to prime fields

Rotate one distinguished pair to $1,z^d$. A second pair determines a unique nonidentity involution exchanging the two pairs, since the product of its two cross ratios fixes the parameter of the involution exchanging the distinguished endpoints. Each further pair gives an equality of two pair products. Dividing the cleared difference by $1-z^d$ leaves the determinant of the three rows $(1,x+y,xy)$. Its cyclic expansion is a sum of three products, each bounded in absolute value by four at every complex conjugate. A collision also holds at the reciprocal primitive root. The integer cyclotomic norm therefore vanishes whenever $p^2>12^{\varphi(N)}$. All the specified pairs then give one and the same complex involution. If that involution is reciprocal, equality of the products of the paired sites is an equality of exponents modulo $N$, and persists in the prime field. Negation transfers in the same way. [Lean pair transfer](../../../ArkLib/Research/ProximityGap/Frontier/CyclotomicPairDeterminant.lean)


## A sharp three-pair example

For every primitive root $z$ of even order at least eight, the three pairs $(1,z)$, $(z^2,-z^2)$, and $(z^3,z^4)$ are disjoint. The trace-zero map $(ax+b)/(cx-a)$ exchanges all three, with
$$
a=z(z^2-z+1),\qquad b=-z^4,\qquad c=1.
$$
Substitution gives $cxy-a(x+y)=b$ for each pair. The determinant test is $a^2+bc=z^2(z-1)^2(z^2+1)\ne0$. The diagonal entry is nonzero because $a=0$ would imply $z^6=1$. Scaling the sites conjugates the map and preserves its non-dihedral form. Thus the maximum number of disjoint transpositions of a non-dihedral involution on every smooth 128-site domain in a sponsor-size prime field is exactly three. The upper bound uses the six complete pair tables. On a nonantipodal row only the reflection target can have three or more alternative pairs. For a trace-zero map based at $u,v$, that target equality reads $(cu-a)/(cv-a)=u/v$ and hence forces $a=0$. If all four pairs are antipodal, comparing two of them gives $c=b=0$. [Sharpness on every even root orbit](../../../ArkLib/Research/ProximityGap/Frontier/ThreeInvolutionPairs.lean) · [Order-128 upper bound over all sponsor-size primes](../../../ArkLib/Research/ProximityGap/Frontier/Smooth128Involutions.lean)
