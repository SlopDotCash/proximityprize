# Distance from three successively transformed fibers

Let $H=\mu_n$ at the first named prime, $n=2^{30}$. A quarter-rate MCA failure at 447,392,428 errors supplies three complete simple fibers $A,B,C$ of a degree-$d=n/4-2$ map $R$. Each half-rate triangle pencil required at 268,435,457 errors has the same property with $d=n/4-1$. For **arbitrary** such fibers, every rotation $s$ of order at least sixteen at quarter rate satisfies

$$
              |sA\setminus B|+|sB\setminus C|\ge 17,895,696 .
$$

For a half-rate triangle the lower bound is **17,895,697** for all rotations of order at least eight. The ordering of the three fibers is arbitrary. A Möbius transformation other than a subgroup rotation has loss at least $d$ at either endpoint. The separate exclusion of an exact progression covers the smaller rotation orders as well. [Endpoint and exact-progression proof](quarter-successor-mobius-progressions.md)

## A four-step comparison

Write $u=|sA\setminus B|$, $v=|sB\setminus C|$, $w=|sC\cap A|$, and $E=H\setminus(A\cup B\cup C)$, of size $d+q$ with $q=n-4d$. Normalize the three target values to $0,1,\infty$ in the stated order. The maps $R(sX)$ and $\pi(R(X))$, with $\pi$ the corresponding target three-cycle, agree at $(d-u)+(d-v)+w$ sites. The maps are distinct, since otherwise the order-three action would be a quotient of the dyadic rotation group. Their agreement determinant has degree $2d$, giving $w\le u+v$.

Under the proposed cycle of site sets $A\to B\to C\to E\to A$, the first two losses are $u,v$. The third is at most $w+u+v$, because the $B,C$ sites unavailable to $sA,sB$ number $u,v$ respectively. The fourth is at most $q+w+u+v$, because at most $w+u+v$ sites of $A$ are occupied by $sC,sA,sB$. The four losses therefore sum to at most $5(u+v)+q$. For each of $A,B,C$, a point that leaves its set after four rotations must fail one of its four indicated transitions. At each transition the rotation gives an injection into the corresponding lost sites. The sum of the three four-step losses is consequently at most $3(5(u+v)+q)$.

At quarter rate the order of $s^4$ is at least four under the stated hypothesis, and does not divide $d$. At half rate it is at least two and $d$ is odd. Thus $s^4$ cannot preserve all three fibers. The nonzero determinant comparing $R(s^4X)$ and $R(X)$ vanishes at source zero and infinity in addition to all the sites retained in their own fiber. Therefore at most $2d-2$ of the $3d$ fiber sites are retained. This proves $d+2\le 3(5(u+v)+q)$ and the two ceilings above. [Rotation determinant](half-four-fiber-parity.md#rotation-distance-over-the-production-field)

For a scaled reciprocal preserving $H$, its square is the identity and $A,C$ are disjoint, so the two losses already sum to at least $d$. A scaling or scaled reciprocal with scale outside $H$ sends no site into $H$. Every other Möbius map sends at most 3,960,117 subgroup sites to subgroup sites, so the two losses sum to at least $2d-3,960,117$. [Named-field intersection bound](quarter-split-pencil-pullbacks.md#a-source-symmetry-is-unique-if-it-exists)

## Order four and a rational coefficient

Suppose $s$ has order four. Choose the full fiber members $F_0,F_1,F_2$ vanishing on $A,B,C$ respectively, rescaled to sum to zero. Put $a=F_1(sX)/F_0(X)$ and $b=F_2(sX)/F_1(X)$. Their rational degrees are $u,v$. All six polynomials have degree $d$ and nonzero constant term, so $a,b$ are regular and nonzero at zero and infinity. For $c=b/a$ and $f=F_1/F_0$ the pencil equation gives

$$
                   f(sX)=-1/(1+c(X) f(X)),\qquad \deg c\le u+v .
$$

If $4(u+v)<d$, the product of the four successive projective matrices $M(c_i)$, with $c_i=c(s^iX)$ and $M(z)=\left(\begin{smallmatrix}0&-1\\z&1\end{smallmatrix}\right)$, is scalar. Indeed, clear the denominator of each matrix separately, making its entries polynomials of degree at most $u+v$. A nonscalar product gives a nonzero polynomial equation in $X,f$ of degree at most $4(u+v)$ in $X$ and at most two in $f$. The coprime graph equation of $f$ divides it by Gauss's lemma. This is impossible since the degree in $X$ of that graph equation is $d$.

In $M(c_3)M(c_2)M(c_1)M(c_0)$ the upper right entry is $c_1+c_2-1$. The scalar identity and substitution by the order-four rotation give $c(sX)=1-c(X)$. A constant $c$ would give an exact projective covariance, and the displayed map would send the $A$ fiber to $B$ and then to $C$, the excluded progression. For nonconstant $c$, its values at zero and infinity are both $1/2$. Its deviation from $1/2$ changes sign under the rotation. The local vanishing orders at both source points are therefore $2\bmod 4$. In particular every order-four rotation has $u+v\ge4$ at both endpoints.

## Three arbitrary rotational translates

Suppose the three complete fibers are rotations of one set, with no prescribed relation between the rotations. Write their locators as scalar multiples of $P(X),P(rX),P(sX)$, taking reciprocals of the rotation factors as needed, and let $l=|\langle r,s\rangle|$. The three fiber members satisfy a relation with constant nonzero coefficients. For every exponent $j$ with $[X^j]P\ne0$, the point $(r^j,s^j)$ lies on a common line with nonzero slope and nonzero intercept. In particular it lies on the line through $(1,1)$ and $(r^d,s^d)$, since $P$ has nonzero constant and leading coefficients.

Here $r^d,s^d$ are distinct and both differ from one. If just one equals one, the second point cannot lie on that line. If both equal one, the two distinct nonidentity rotations would belong to a subgroup of size at most two. If they are equal and nontrivial, the line is the diagonal, forcing $P(rX)=P(sX)$ and two fibers to coincide.

The active exponent residues $J$ modulo $l$ form a Sidon set. Indeed write $v_j=s^j=a r^j+b=a u_j+b$ with $ab\ne0$. If $i+j=k+m\bmod l$, the products $u_i u_j=u_k u_m$ and $v_i v_j=v_k v_m$ are equal. Expanding the latter gives $u_i+u_j=u_k+u_m$, hence the two unordered pairs of $u$-values coincide. The line determines the corresponding $v$-values, and a pair $(r^j,s^j)$ determines $j\bmod l$. Thus $|J|(|J|-1)\le l-1$, giving at most 32,768 coefficient residues even for $l=2^{30}$.

In addition, **three arbitrary translates are impossible when $l\le4096$** at either endpoint. The finite prime-field test compares

$$
           (z^j-1)/(z^d-1),\qquad z\in\mu_{4096},\quad 0\le j<4096 .
$$

After omitting zero denominators and the two values $0,1$, no two distinct denominator values produced the same ratio for the same $j$. The test checks 16,723,968 such ratios for each of the residues $d=-2,-1\bmod4096$. Consequently each active residue $j$ must satisfy $(r^j,s^j)=(1,1)$ or $(r^d,s^d)$, so $j=0,d\bmod l$. Rotation by a generator of $\langle r,s\rangle$ now preserves the pencil: its orbit on $P$ lies in the span of the two pieces of $P$ in these residue classes, and $P(rX),P(sX)$ already span that two-dimensional space. Since this orbit contains at least three different fibers, three consecutive members are a forbidden Möbius progression. [Exact finite search](../../../scripts/probes/probe_successor_fiber_rotation_distance.py)

## When two different reflections exchange fiber pairs

At the quarter successor, suppose that **two different** scaled reciprocals each exchange two of $A,B,C$, with different exchanged pairs. Each involution preserves the pencil, since the two exchanged vanishing forms span it. Both reciprocals have scalars in $H$. They generate a dihedral source group whose rotations have order $l$, a power of two. The orbit of the three target points under the group consists of exactly four full fibers: it contains at least three, its size is dyadic, and five disjoint full fibers would exceed the domain. The kernel on the pencil has order at most two by the source-automorphism theorem. The target group acts faithfully on the four-point orbit, since an element fixing three points of the target is the identity. [Source-automorphism bound](quarter-split-pencil-pullbacks.md#a-source-symmetry-is-unique-if-it-exists)

The target image of the generating rotation, as a permutation on these four points, has order at most four. Order four would supply the excluded progression. Order one would leave a target group generated by just one involution. Thus it has order two. Since the target group is generated by two involutions with product of order two and has an orbit of size four, it is the Klein four. This forces either a faithful source Klein four or a source group of order eight with its antipode in the kernel.

Faithful Klein-four covariance on source and target forces **odd map degree**. To see this over the algebraic closure, lift the two source involutions and the corresponding target involutions to determinant-one matrices. On each side the two lifts anticommute. Indeed commuting lifts would be simultaneously diagonalizable, but a diagonal projective torus has only one nonidentity involution. Since the projective images commute, the lifts commute up to sign and the sign must be minus. If $(P,Q)$ is a coprime homogeneous pair of degree $d$, applying a source lift gives the corresponding target lift on $(P,Q)$ up to a *constant* scalar, by equality of the rational maps and coprimality. Applying both generators in both orders gives $(-1)^d=-1$. This rules out the faithful case at the even quarter degree.

The survivor consequently descends by squaring to a degree-$m=n/8-1$ map on $H'=\mu_{n/2}$. On this domain the faithful source Klein four is generated by $y\mapsto-y$ and $y\mapsto b/y$, $b\in H'$. The four target fibers form a free orbit; all four points in each of the $m$ corresponding regular source orbits occur. The four leftover sites are either one regular orbit, or the two special two-point orbits. In the second case they are exactly the roots of $y^4-b^2$. Indeed the only source points of $H'$ whose orbit has size two satisfy $y^2=b$ or $y^2=-b$; either both pairs occur or neither does, since $-1$ is a square in $H'$.

In fact the four target values are simultaneously in a projective copy of $H'$. The two source points zero and infinity go to distinct fixed points of the target involution induced by negation, since $m$ is odd. Normalize them to zero and infinity, and scale a full fiber value to $-1$. The descended map is now $O(y)/E(y)$ with $O$ odd and monic of degree $m$ and $E$ even of degree less than $m$. Put $\xi=E(0)$, the constant coefficient of the monic full vanisher $O+E$. Then $\xi\in H'$ since all roots belong to $H'$ and $-1\in H'$. The other target involution interchanges zero and infinity and hence acts by $z\mapsto\gamma/z$. Comparing the two coprime presentations of the reciprocal map gives

$$
 y^m O(b/y)=(b^m/\xi)E(y),\qquad y^m E(b/y)=\xi O(y).
$$

The constants follow from the constant coefficient of the first identity and the leading coefficient of the second. Therefore $\gamma=b^m/\xi^2\in H'$, and the four target values are $\{1,-1,\gamma,-\gamma\}$. The existence of such an odd-degree map with all four fibers full remains open.
