# Prescribed rational projective sets averaged over primes

Let $A,B\subset\mathbf P^1(\mathbb Q)$ be given before the prime is chosen. Represent each point by primitive integers of maximum absolute value at most $P^C$, for fixed $C>0$. The sets, their denominators and their sizes may change with $P$. At an odd prime $p$ each representative reduces to a projective point. Write $\bar A,\bar B$ for the two sets of distinct reductions and $\chi_p$ for the Legendre symbol. The projective Paley matrix uses $\chi_p(\det(v,w))$ on homogeneous representatives. Changing representatives changes only row and column signs.

Suppose $a=|A|,b=|B|\ge P^\epsilon$, where $0<\epsilon\le1$. Put $k=\max(2,\lceil8C\rceil)$. For any fixed $0<\delta<\epsilon/(16k)$, outside
\[
              O_{C,\epsilon,\delta}(P^{1-\epsilon/(2k)+8\delta+o(1)})
\]
primes in $[P,2P]$, the projective matrix on $\bar A\times\bar B$ has operator norm at most $\sqrt{|\bar A||\bar B|}\,P^{-\delta}$. Both vertex weights, dense subsets and a common projective change of coordinates may be chosen after seeing the prime. In particular, take $A=B$ and suppose its reductions are distinct. The proportion of singular four-site principal minors over $\mathbb F_3$ is $1/4+O(P^{-2\delta}+1/a)$. The same conclusion uses $|\bar A|$ when there are collisions. [Projective sign and rank identities](paley-four-site-rank.md)

This permits independently specified rational transformations on the two templates and individual denominators at every site. Reducing such sites can give different subsets as $p$ varies. Exceptions may depend on the original rational points. For example, an integer set and an independent set of reciprocals of nonzero integers are included. For two integer templates a quadratic equation suffices and the exponent is stronger. [Integer prime-average theorem](paley-prescribed-prime-average.md#both-sides-adaptive-throughout-the-full-interval)

## A squareclass with four prescribed branch points

For primitive lifts write $[x,t]=x_1t_2-x_2t_1$. Fix four distinct rational points $x_1,\dots,x_4$ of the stated height. Let $\ell_j(t)=[x_j,t]$ and $F(t)=\prod_j\ell_j(t)$. For any fixed nonzero rational squareclass, at most $P^{o(1)}$ rational points of height at most $P^C$ have nonzero $F(t)$ in this class. All constants are uniform in the four points and the squareclass.

Indeed, choose the signed squarefree integer $D$ in the class. If it occurs, $F(t)=Dz^2$ for some nonzero integer $z$, and $|D|\le16P^{8C}$. The primitive lift of $t$ is unique up to sign and $F$ has even degree. Set $r=\ell_1/\ell_4$ and $y=z/\ell_4^2$. In the basis $\ell_1,\ell_4$ of linear forms, write $\ell_2/\ell_4=A r+B$ and $\ell_3/\ell_4=E r+G$. The coefficients are ratios of determinants of the fixed rows. They are all nonzero, with $AG\ne BE$, since the four rows are distinct as projective points. We obtain
\[
       D y^2=r(Ar+B)(Er+G).
\]
Put $c=DAE$, $X=cr$ and $Y=cDy$. Then
\[
       Y^2=X(X+DEB)(X+DAG).
\]
The three rational roots are distinct. This elliptic curve therefore has full rational two-torsion. The map to $X$ is injective on the allowed column sites since $\ell_1/\ell_4$ is a projective coordinate. [Lean checks of the coordinate identity, injectivity, cubic equation and distinct roots](../../../ArkLib/Research/ProximityGap/Frontier/PaleyQuarticTwist.lean)

The heights of the rational coefficients of this Weierstrass equation and of $X$ are $P^{O_C(1)}$. Each comes from a fixed number of arithmetic operations on integers of polynomial size, with nonzero denominators. Naccarato's Theorem 1.1 gives at most $H^{O(1/\log\log H)}$ rational points of $x$-coordinate height at most $H$ on an elliptic curve with a rational point of order two, provided $H$ exceeds a fixed power of the model height. Take $H$ to be a sufficiently large fixed power of $P$ to meet both height conditions. The count is $P^{o(1)}$, as claimed. This use of a uniform theorem covers a different quadratic twist for every squareclass. [Naccarato, Theorem 1.1 and height conventions](https://arxiv.org/pdf/2105.04032)

## Counting squareclasses of rectangles

Let $N_g$ count ordered $(x,y,t,u)\in A^2\times B^2$ for which
\[
                 K=[x,t][x,u][y,t][y,u]\ne0
\]
has rational squareclass $g$. Write $1$ for the class of nonzero squares. For fixed $(t,u)$, group all rows $x$ giving nonzero $[x,t][x,u]$ according to its squareclass. If the multiplicities are $s_h$, the number of row pairs counted at $g$ is $\sum_h s_hs_{gh}\le\sum_hs_h^2$ by Cauchy–Schwarz. Hence $N_g\le N_1$.

Write $T_{tu}=\sum_hs_h^2$. Then $N_1=\sum_{t,u}T_{tu}$. Count $T_{tu}^2$ as ordered pairs of row pairs. When a row is repeated among the four entries, mark one of the six pairs of equal positions. The product of all four row values is a square, so the other two rows have equal squareclass. There are at most $6a T_{tu}$ such terms. For four distinct rows, fix them and $t$. Each contributing $u$ has $F(u)$ in the squareclass of $F(t)$. The elliptic bound gives $P^{o(1)}$ possibilities. Summing and using Cauchy–Schwarz again yields
\[
 N_1^2\le b^2\sum_{t,u}T_{tu}^2
 \le b^2\big(6a N_1+a^4 b P^{o(1)}\big).
\]
Thus uniformly in $g$,
\[
             N_g\ll a^2b^2 P^{o(1)}(a^{-1}+b^{-1/2}).             \tag{1}
\]
The same bound holds after exchanging $A,B$. Four determinants change sign on transposition, preserving $K$. Take $a\le b$ in the remaining argument. Specifying only the odd squarefree part $q$ of $|K|$ allows at most four full squareclasses, so (1) also bounds its multiplicity up to a factor of four.

## Averaging the matrix norm

Use primitive integer labels initially. For any set $\mathcal E$ of $L\ge1$ primes in $[P,2P]$, the fourth power of the operator norm at each prime is bounded by the sum of squared Gram entries. The prime sum of those entries expands as the sum of $\sum_{p\in\mathcal E}(K/p)$ over all rectangles above. The conductor $q$ is at most $16P^{8C}$. For $q>1$ the inner sum is at most $4U(q)+O_C(1)$ in absolute value, where $U(q)$ is the maximum over odd residue classes $j\bmod8$ of $|\sum_{p\in\mathcal E,\ p\equiv j\bmod8}(p/q)|$. The additive error covers the $O_C(1)$ primes dividing the square cofactor of $K$. The prime-supported quadratic large sieve gives $\sum_{q>1}U(q)^{2k}\ll P^{k+o(1)}L^k$ over the eligible odd squarefree conductors. A fixed constant factor in the conductor limit does not change the estimate. [Derivation from Heath-Brown's large sieve](paley-prescribed-prime-average.md#both-sides-adaptive-throughout-the-full-interval)

Set $\gamma=a^{-1}+b^{-1/2}$. For $q=1$ the normalized contribution is $O(L\gamma P^{o(1)})$. For $q>1$ apply weighted Hölder using the largest multiplicity from (1) and at most $a^2b^2$ rectangles in total. This gives
\[
 \sum_{p\in\mathcal E}\frac{\|M_p\|^4}{a^2b^2}
   \ll P^{o(1)}
       \left(L\gamma+\sqrt{PL}\,\gamma^{1/(2k)}+1\right).
\]
Take $\mathcal E$ to consist of primes exceeding the claimed labelled norm threshold. Then $LP^{-4\delta}$ is a lower bound on the left; the $L\gamma$ term is absorbed for large $P$. Since $\gamma\le2P^{-\epsilon/2}$, squaring the remaining inequality gives the announced exceptional count. A constant factor in the threshold only changes the implied constant.

Finally, reductions of distinct rational points $s,t$ coincide only at primes dividing the nonzero integer $[s,t]$, whose absolute value is at most $2P^{2C}$. Put $\eta=\epsilon/(2k)\le1/4$. Truncate either template to $\min(|X|,\lfloor P^{1-\eta}\rfloor)$ labels. Summing colliding pairs as in the integer case shows that each truncated set retains at least half as many distinct points outside $O_C(P^{1-\eta})$ primes. When neither template was truncated, restrict the labelled inequality to distinct representatives at half the target threshold. When at least one was truncated, the product of the two image sizes is $\gg P^{1-\eta+\min(1-\eta,\epsilon)}$. The full projective conference matrix has norm $\sqrt p$, giving a stronger saving than $P^{-\delta}$ there. These arguments prove the bound with the stated distinct-image normalization. [Conference matrix identity](paley-production-spectrum.md#every-projective-image-including-its-pole)
