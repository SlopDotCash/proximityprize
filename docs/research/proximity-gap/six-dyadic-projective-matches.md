# Six matches for a projectivity on dyadic roots

Let $H=\mu_N(\mathbf C)$, $N=2^m$. If a Möbius transformation carries seven distinct points of $H$ into $H$, it has the form $x\mapsto tx$ or $x\mapsto t/x$ with $t\in H$. Six matches occur for every $N\ge8$. No assumption that the transformation is an involution is needed. The same bound holds on arbitrary multiplicative cosets in any prime field with $p>2^N$ containing $H$. For the special case of involutions, the weaker condition $p^2>12^{\varphi(N)}$ suffices.

Lean verifies the parity descent, its exceptional five-site conic, the finite-prime transfer and the sharp six-site construction. The prime-field result covers independent nonzero scalings of the source and target grid. [All dyadic orders](../../../ArkLib/Research/ProximityGap/Frontier/DyadicSevenProjectivities.lean) · [Two prescribed prime-field cosets](../../../ArkLib/Research/ProximityGap/Frontier/DyadicProjectiveCosets.lean) For context, Fu gives a sharp bound of fourteen points allowing arbitrary complex roots of unity. [Fu](https://arxiv.org/abs/1905.01510) · [Cross-ratio transfer](../../../ArkLib/Research/ProximityGap/Frontier/CyclotomicProjectiveTransfer.lean) · [Chord norms](../../../ArkLib/Research/ProximityGap/Frontier/DyadicChordNorm.lean)

## A cross ratio excludes four occupied parity classes

When $N\ge8$, fix a primitive root $z$. Write E and O for points of even and odd exponent. In the cyclotomic field use the valuation $v(1-z)=1$ above two. For $x=z^i\ne y=z^j$, its value on the chord $x-y$ equals $2^{v_2(i-j)}$. This follows by writing the difference as a root of unity times $1-z^{i-j}$, taking its absolute rational norm $2^{\gcd(i-j,N)}$, and using total ramification of 2.

Categorize each match by its source and target parity. Four matches cannot represent EE, EO, OE, OO respectively. The cross ratio formed from the product of the first two and last two source chords divided by the two chords linking the first to the third and the second to the fourth has positive valuation. Indeed both numerator factors join sites of the same parity and both denominator factors join sites of opposite parity. The same cross ratio of the four images has negative valuation. A projectivity preserves these two cross ratios exactly.

## The conic left after one antipodal pair

The following lemma permits loops, that is, matched sites fixed by an involution. On $H$, fix $c$ of odd exponent and a nonzero $B\in\mathbf Q(z)$. The nonsingular conic
\[
 Bxy+x+y+Bc=0
\]
has at most four distinct source sites $x\in H$ with a partner $y\in H$. For $N\le4$ this is immediate. The pairing is symmetric, and distinct unordered pairs (including loops) have distinct products: the equation recovers their sum from their product.

For $N\ge8$ split $B=B_0+B_1$ into invariant and anti-invariant parts under $\sigma(z)=-z$. The parity of $c$ gives $(Bc)_0=B_1 c$ and $(Bc)_1=B_0 c$. Two EE pairs with distinct products force $B_1=B_0c=0$. Two OO pairs force $B_0=B_1c=0$. Hence each same-parity type contains at most one unordered pair. A cross pair occupies both EO and OE among ordered matches. The cross-ratio argument prevents both same-parity types from occurring with it.

For a cross pair oriented with even $x$ and odd $y$, writing $T=xy$ gives
\[
 x=-B_1T-B_1c,\qquad y=-B_0T-B_0c.
\]
In particular $B_0B_1\ne0$ and $T=B_0B_1(T+c)^2$, so there are at most two such pairs. Suppose there are two, denoted $(x_i,y_i)$, and let $D=x_1y_1-x_2y_2$, $U=x_1x_2$, $V=y_1y_2$. Their distinct products give $D\ne0$, and the two displayed linear equations give
\[
 B_1=-(x_1-x_2)/D,\qquad B_0=-(y_1-y_2)/D.
\]
Taking the product of the two roots of the quadratic gives $UV=c^2$. Also $x_1/y_1=x_2/y_2=B_1/B_0$, a root of unity. Thus $x_1/x_2=y_1/y_2$, and
\[
 v(D)=v(1-(x_1/x_2)^2)>v(1-x_1/x_2)=v(y_1-y_2).
\]
The strict inequality follows from the chord formula; the square is not one because $D\ne0$. Since $U,V$ have even exponents and $UV=c^2$ with $c$ odd, their exponents differ by two modulo four. This gives $v(V-U)=2$.

An additional EE pair would have product $-V$ and sum $B_0(V-U)$. Indeed $U=B_1c/B_0$ and $V=B_0c/B_1$, from $x_i/y_i=B_1/B_0$ and the identity $(T_1+c)(T_2+c)=c/(B_0B_1)$ for the roots of the displayed quadratic. Its sum would have valuation $v(y_1-y_2)+2-v(D)<2$. A sum of two even sites has valuation at least two, including a double site. An OO pair gives the same contradiction with sum $B_1(U-V)$. With two cross pairs there are therefore no further sites. With at most one cross pair the previous parity counts already bound the total by four. This proves the lemma.

## Descent for an arbitrary projectivity

Assume there are at least seven matches, and take the full set of matches. At most three parity classes are occupied, so some class has at least three matches. Independent rotations of source and target move them into EE, preserving the conclusion. Write the projectivity as $M$. Three distinct source and target sites determine $M$, so it is defined over $\mathbf Q(z^2)$ and commutes with $\sigma$. An even input cannot have an odd output. If an odd input $x$ had an even output, then $M(-x)=M(x)$, contradicting injectivity. All matches are now EE or OO.

If all are EE, apply induction to the smaller grid. Otherwise choose an OO match $u\mapsto v$. Another is $-u\mapsto-v$. If $M=(ax+b)/(cx+d)$, the relation $M(-x)=-M(x)$ gives $acx^2=bd$. Unless $M$ is already a scaling or reciprocal scaling, this equation has at most two solutions, so $u,-u$ are all the odd source matches.

Multiply the output by $-u/v$, an even power, to get a map that interchanges $u$ and $-u$. It retains at least five even source matches with even targets. Substitution of $\pm u$ into its matrix representation forces opposite diagonal entries and constant numerator term equal to minus the denominator slope times $u^2$. Unless the map is already dihedral, normalizing its graph equation gives $Bxy+x+y+Bu^2=0$. Its coefficients belong to the smaller field by the three even matches. On $\mu_{N/2}$, $u^2$ has odd exponent. The lemma permits at most four sites, a contradiction. The induction starts at $N\le4$, where seven matches are impossible.

For sharpness, on every even primitive orbit of length at least eight the transpositions $\{1,z\}$, $\{z^2,-z^2\}$, $\{z^3,z^4\}$ belong to one non-dihedral involution. These six sites are distinct. [Lean witness](../../../ArkLib/Research/ProximityGap/Frontier/ThreeInvolutionPairs.lean)

## Prime-field conclusion

Choose three of the prescribed matches as anchors. Every further match gives equality of the two ordered cross ratios, which is equivalent to having zero determinant for rows $(1,x,y,xy)$. The squared-prime resultant divisibility and the four row norms give transfer to the complex roots whenever $p^2>16^{\varphi(N)}$. For dyadic $N\ge2$ this is $p>2^N$. The one complex projectivity determined by the anchors has all the prescribed matches and is dihedral if there are at least seven. The equalities of the differences or sums of the matched exponents then hold modulo $N$, so the scaling or reciprocal map with the same exponent matches every prescribed pair over the prime field. Three matches identify it with the original projectivity. Independent rotations and coset scalings are harmless. [Lean four-point transfer](../../../ArkLib/Research/ProximityGap/Frontier/CyclotomicProjectiveTransfer.lean)
