# Projective minor covers at the second-prime eighth-rate boundary

At $n=2^{30}$, $d=n/8-1$ and $e=671088640$, an over-budget quartet would give a rational plane map $f$ from the signed triangle determinants of its four polynomial heads. The degree of $f$ over its image must belong to
\[
 \{1,2,4\}\ \cup\
 \{3273603,\ 4329604,\ 5368709,\ 22369621,\ 26843545,\ 33554431,\
 44739241,\ 44739242,\ 67108862,\ 67108863,\
 134217723,\ 134217724,\ 134217725,\ 134217726\}.
\]
At degrees two and four the cover must be the quotient by a subgroup of the dihedral group preserving the named domain. The fourteen higher possibilities each force between four and 164 prescribed fibers of one rational function, with at most **18 points missing from complete splitting on the named subgroup in total**. Degree one remains possible. This restricts the triangle minor map even when the physical rows undergo an invertible change of coordinates that varies with the evaluation point. [Physical quartet reduction](eighth-rich-head-safety.md#at-exactly-five-eighths)

## Base points and the row degrees

Work over the algebraic closure. Translate by a head, write the other three differences as a two-by-three matrix $V$, and homogenize its two rows to degree $d$. Its signed maximal minors represent $f$; the fourth triangle determinant is their signed sum. They all have homogeneous degree $2d$. Write $h$ for the degree of their common homogeneous gcd, including any zero at infinity, and $D=2d-h$ for the base-point-free degree. All four faces are nonzero since no three heads are collinear over the function field.

For a physical site with $w$ owners, the order of a face determinant is at least the positive part of its number of owners minus one. For $w=0,1,2,3,4$, the sum of the four required orders is respectively $0,0,2,5,8$. Write $g_x$ for the minimum of the four actual orders. The sum of actual orders is at least $g_x+2(w-1)_+$, by these five cases and the further lower bound $4g_x$. At every point off the physical domain, including infinity, it is at least $g_x$. If $s=n+4d-\sum_i|C_i|$ is the physical slack and $x_j$ counts sites with $j$ owners, summing gives
\[
 h+2(4d-s+x_0)\le8d,\qquad h\le2s\le8.
\]
The same face budget gives $2x_0+x_3+2x_4\le2s$. Combining this with $x_2+2x_3+3x_4+s=4d+x_0$ gives $x_2\ge4d-5s$. [Triangle orders](../../../ArkLib/Research/ProximityGap/Frontier/_HalfPredecessorRateQuarterDeterminantMultiplicity.lean) · [Integer accounting](../../../ArkLib/Research/ProximityGap/Frontier/EighthQuartetMinorCovers.lean)

Suppose $f=g\circ\phi$, where $\phi$ has degree $q$, and the plane map $g$ has homogeneous degree $m$ without common zeros. Consequently $qm=D$. Every nonzero homogeneous syzygy $C$ of the reduced minor vector has degree at least $d-h$. Indeed $C$ is independent of at least one of the two original rows $A,B$ over the rational function field. The nonzero cross product with that row is a polynomial multiple of the primitive minor vector by unique factorization, and hence $\deg C+d\ge D$.

Three degree-$m$ entries in two homogeneous variables have a nonzero syzygy in degree $k=\lfloor m/2\rfloor$. The linear system has $3(k+1)$ unknowns and at most $m+k+1$ equations. Pulling back by the two coprime degree-$q$ coordinates for $\phi$ preserves nonzero syzygies, since $\phi$ is surjective. Thus $d\le q\lfloor m/2\rfloor+h$. Equivalently $q\lceil m/2\rceil\le d$. Taking the remainder modulo $q$ gives
\[
 2(d\bmod q)\le 2\bigl(d-q\lceil m/2\rceil\bigr)\le h\le2s.
\]
If $q>h$, the same inequality for $\lfloor m/2\rfloor$ excludes odd $m$. In this case $h=2(d\bmod q)$ and $m=2\lfloor d/q\rfloor$. In particular **no rational right factor can have degree divisible by eight**, since $d\equiv7\pmod8$. This argument applies to inseparability as well; at the production characteristic all the degrees considered are less than $p$.

## Almost complete fibers

In the target plane the four face coordinates give the four lines of a complete quadrilateral. Their six distinct intersection points specify equality of the corresponding two heads: the projective kernel of $V$ contains the corresponding fixed difference vector precisely at such an equality when $V$ has rank two. Each of these marked target points lies on two face lines. Let $E$ be their complete geometric inverse image under $f$. Summing the degrees of the four reduced face divisors gives $|E|\le2D$. At a physical double site with rank two the kernel gives the corresponding marked point. Rank drops occur at at most $h$ geometric points, so $e_H=|E\cap H|\ge x_2-h$ for $H=\mu_n$.

Let $Y=\phi(E)$, $M=|Y|$, and $e_y=|\phi^{-1}(y)\cap H|$ for $y\in Y$. Every point in those fibers lies in $E$, and each marked point costs two face zeros downstairs. Thus
\[
 M\le2m,\quad
 \Delta:=\sum_{y\in Y}(q-e_y)=qM-e_H\le4d-2h-(x_2-h)\le 5s-h,
 \quad
 2e_H-qM\ge2x_2-4d\ge P:=4d-10s.
\]
This includes a ramified point with only one distinct physical representative. For $q>5s$ the same bound on $e_H$ gives $M=2m$, since $q(2m-1)<e_H$. In that case all $2m$ marked parameters are distinct and use both face zeros simply.

Every projective deck symmetry $\tau$ of $f$ permutes $E$. At least $2e_H-|E|\ge P\ge536870868$ physical sites $x$ have $\tau(x)\in H$. A non-dihedral Möbius graph contains at most 3,143,679 points of $H^2$. A transformation $x\mapsto ax$ or $a/x$ with one such hit has $a\in H$. Hence the deck group is a subgroup of the dihedral group of order $2n$. Its order is itself the degree of a right factor of $f$, by the fixed-field theorem and Lüroth's theorem. The remainder criterion excludes eight as a divisor of this order, so it is at most four. In particular, every deck symmetry of $\phi$ belongs to this same group. [Named-characteristic Möbius bound](../../../ArkLib/Research/ProximityGap/Frontier/MobiusSubgroupBound.lean)

## Non-Galois covers have large degree

Consider one geometrically irreducible component $W$ of $\phi(x)=\phi(y)$ inside the torus. The two coordinate degrees agree: composing either coordinate with $\phi$ gives the same function. Denote the common degree by $r$. Each marked fiber contributes at least $(2e_y-q)r$ distinct physical ordered pairs on $W$. To see this, the monodromy orbit for $W$ on ordered pairs of the $q$ generic sheets gives a directed graph with in-degree and out-degree $r$ on each vertex. Specialize all sheets using a place of the Galois closure over the marked value and keep one sheet for each of its $e_y$ distinct physical points. Removing the other vertices deletes at most $2(q-e_y)r$ edges. The remaining pairs specialize to distinct physical pairs on $W$. Thus its normalization has at least $Pr$ physical places in $H^2$. [Specialization argument for protected sheets](production-fiber-correspondence.md#counting-the-protected-sheet-pairs)

If $W$ is the translate of a subtorus, equal bidegrees make it a single graph $y=cx$ or $y=c/x$. This follows by writing its primitive binomial equation, whose two exponents are coprime. These graphs give deck transformations. For every remaining component, the independent coordinate functions $x,y$ on its normalization have genus at most $(r-1)^2$ and at most $4r$ zeros and poles. In particular $\chi\le2r^2$. Corvaja–Zannier's Theorem 2 applied to $x^n,y^n$ gives
\[
 Pr\le (108n^2r^4)^{1/3}.
\]
The degrees of the coordinates are positive and below the characteristic, $p\nmid n$, and $12n^2r^2/p<1$. Consequently $r\ge1242757$. [Corvaja–Zannier, Theorem 2](https://ems.press/content/serial-article-files/31918#page=3)

For the sharper bound, descend to the normalization $W'$ of the image of $W$ under $(x,y)\mapsto(x^n,y^n)$. The degree $J$ of this descent is the order of the stabilizer of $W$ in $H^2$, by the ambient Galois cover of the torus. If $(1,c)$ preserves $W$, then $\phi(cy)=\phi(y)$ on its generic point, so $c$ acts by a scaling deck transformation. The kernel of projection of the stabilizer to the first coordinate therefore has order at most four; in particular $J\le4n$. The two power coordinates on $W'$ generate its function field and have degree $nr/J\ge r/4>14$. The coefficients descend to a finite field. The cover is étale on the torus, tame at the boundary, and the Euler characteristics with the boundary removed satisfy $J\chi(W')=\chi(W)$. The common-zero degree of the two power coordinates minus one likewise multiplies by $J$ on pullback.

Take integer parameters $(14,4)$ in Corvaja–Zannier's Proposition 2. Its height coefficients sum to $(14+3\cdot4)/74=26/74$, and its Euler coefficient is $73/2$. The small-degree alternative is excluded by $nr/J>14$, and the characteristic guard $18nr/J<p$ holds. Pulling back gives
\[
 Pr \le \tfrac{26}{74}nr + \tfrac{73}{2}\chi(W)
       \le \tfrac{26}{74}nr+73r^2,
 \qquad r\ge\left\lceil\frac{74P-26n}{74\cdot73}\right\rceil
       \ge \mathbf{2186442}.
\]
If every component is toric, their graphs give all $q$ sheets, so $\phi$ is precisely a dihedral Galois quotient of degree at most four. Otherwise a nontoric component and the distinct diagonal force $q\ge2186443$. [Corvaja–Zannier, Proposition 2](https://ems.press/content/serial-article-files/31918#page=13) · [Related descent for three full fibers](production-fiber-correspondence.md#bounding-the-independent-components)

## The fourteen large possibilities

In the large case put $a=d\bmod q\le s$. If $a=0$, then $h=0$ and $m=2d/q$. Downstairs there are at least two linearly independent syzygies of degree $m/2$ by the same dimension count. Upstairs the space of degree-$d$ syzygies is exactly the constant span of the two physical rows: crossing any such syzygy with either physical row gives a constant multiple of the primitive minor vector of degree $2d$. Thus the two physical rows are constant linear combinations of the pullbacks of the downstairs syzygies. In a fixed $\phi$-fiber the evaluated head configurations then differ only by translation and a common scale. Among physical sites with multiple owners, a downstairs configuration contributes at most two distinct directions: one repeated pair leaves two other heads, two distinct repeated pairs give only their mutual direction, and a triple leaves one. There are at most $2m$ such parameters, since $h=0$. The singleton and uncovered sites contribute at most $3(n-4d+5s)+4s$. Even adding $4m\le2\lfloor4d/3\rfloor$ and all 20,607,410 residual labels gives fewer than $2n$. This excludes $a=0$ in the large case.

For every large cover there is also an explicit description of the remaining row freedom. Choose independent degree-$m/2$ syzygies $R_1,R_2$ of the downstairs coordinates. No lower-degree syzygy exists there: its pullback would have degree at most $d-a-q<d-h$. Consequently $R_1,R_2$ are independent over the function field, since two nonconstant polynomial multiples of one primitive row would give a lower-degree syzygy. Their cross product equals a nonzero constant times the downstairs minor vector by primitivity and equality of degrees. After pullback, crossing each original physical row with each pulled-back basis row now gives the primitive upstairs minor vector times a homogeneous binary form of degree $d+(d-a)-D=a$. Cramer's rule therefore expresses the two physical rows as a two-by-two matrix of degree-$a$ binary forms times the two pulled-back rows. Its determinant has homogeneous degree $2a$. Thus even the unrestricted coordinate-dependent changes in the fourteen large cases have entries of degree at most four.

The remaining $a\in\{1,2,3,4\}$ give the table. Enumerating the divisors of $d-a$ above the component cutoff suffices. Equivalently the half outer degree $(d-a)/q$ is at most 61. For each pair, $M=2m$ and $\Delta\le5s-2a\le18$.

| $a$ | $(q,m)$ in increasing cover degree |
|---:|---|
| 1 | $(22369621,12)$, $(44739242,6)$, $(67108863,4)$, $(134217726,2)$ |
| 2 | $(5368709,50)$, $(26843545,10)$, $(134217725,2)$ |
| 3 | $(4329604,62)$, $(33554431,8)$, $(67108862,4)$, $(134217724,2)$ |
| 4 | $(3273603,82)$, $(44739241,6)$, $(134217723,2)$ |

Lean checks the local and global degree charges, integer syzygy descent, component-floor arithmetic and the fourteen divisors. The projective argument, sheet specialization and application of the published curve estimates are written proofs. The independent integer program reproduces every table entry and checks all owner masks and allowed exceptional incidence counts. The unconstrained birational case, possible twisted dihedral covers at degrees two and four, and the fourteen large covers keep the unrestricted first failure in **[671,088,640, 679,477,248]**. [Lean arithmetic](../../../ArkLib/Research/ProximityGap/Frontier/EighthQuartetMinorCovers.lean) · [Independent verifier](../../../scripts/probes/probe_eighth_minor_covers.py)
