# Three complete quarter-rate fibers cannot form a Möbius progression

At the first designated prime, put $n=2^{30}$, $H=\mu_n$ and $D=n/4-2=268435454$. An MCA counterexample at 447,392,428 errors requires a degree-$D$ map $R$ with three complete simple fibers of size $D$ in $H$. **No projective linear transformation of the source, even over the algebraic closure, can send the first of these sets to the second and the second to the third.** Their order can be chosen arbitrarily. Arbitrary triples also obey a quantitative lower bound for the number of sites lost under two successive rotations. Their existence remains open. [Rotation-distance proof](successor-fiber-rotation-distance.md) [Endpoint equivalence](quarter-successor-split-pencil.md)

## A differential constraint for complete fibers

Work in characteristic zero or characteristic greater than $n$. If a rational map has $j\ge3$ complete simple fibers in $H$ at the $j$-th roots of unity, write $R=P/Q$ in coprime binary forms of degree $d$. Assume $jd<n$, and let $K$ be the homogeneous simple vanisher of the $n-jd$ holes, the points of $H$ outside the displayed fibers. Up to a nonzero scalar,

\[
 K(P^j-Q^j)=X^n-Z^n .
\]

Write $r=\sum_{R(x)\in\{0,\infty\}}(e_x-1)$ for the total ramification over the two indicated target points. Let $b$ count the points of the **source** pair $0,\infty$ mapping into this target pair, and let $k$ count its preimages among the holes. Then

\[
                   2r+b+k\ \le\ n-2-2(j-2)d .
\]

Indeed $S=\partial_X\partial_Z(KP^j)=\partial_X\partial_Z(KQ^j)$ has degree $n-2$ and is nonzero. In the given characteristic the kernel of this mixed derivative on binary degree-$n$ forms is the span of $X^n,Z^n$. If $KP^j$ belonged to this span, evaluating at any hole would make it proportional to $X^n-Z^n$. The identity would force $P^j,Q^j$ to be proportional.

At a root of $P$ or $Q$ of index $e$, the corresponding side has order at least $je$, plus one at a hole. Two derivatives reduce this order by at most two. At $X=0$ only the $X$-derivative can reduce the exponent of $X$, and likewise at $Z=0$. Hence that root contributes at least $(j-2)e+2(e-1)$ zeros of $S$, plus one at a hole or a source point $0,\infty$. The two fibers are disjoint and their indices sum to $2d$. Comparison with $\deg S=n-2$ proves the assertion.

For **any three successor fibers**, move their target values $0,1,\infty$ to $\mu_3$ by a target projectivity over the algebraic closure. The two new central targets $0,\infty$, in the original coordinate, are the fixed points of the order-three transformation cyclically permuting the original triple. They are conjugate over the named prime field, since $p\equiv2\pmod 3$. The map $R$ is defined over that field. Therefore neither a hole nor a source point $0,\infty$ maps to a central target. The two individual ramification sums coincide, and **each is at most 134,217,728** by the bound for $j=3$. This conclusion imposes no symmetry on the fibers.

If four complete successor fibers are a projective image of $\mu_4$, choose the inverse target projectivity. The bound becomes **$2r+b+k\le6$**. Thus the *two central target fibers together* have ramification at most three, and their union contains at least $2D-3=536870905$ distinct geometric points. This applies to every such harmonic target quadruple independently of how its sites sit in the subgroup.

## From a progression to four complete fibers

Suppose a Möbius map sends a full fiber $A$ to $B$ and then to $C$. It sends at least $D$ subgroup sites to the subgroup. Every Möbius map other than a scaling or scaled reciprocal sends at most 3,960,117 such sites back to the subgroup. The subgroup point images force the scale factor to belong to $H$. A reciprocal is an involution and cannot give three distinct sets, so the map is multiplication by some $s\in H$. [Production Möbius bound](quarter-split-pencil-pullbacks.md#a-source-symmetry-is-unique-if-it-exists)

Let $T$ act on binary forms by rotation, taking each fiber vanisher to the vanisher of its $s$-translate, up to scale. The two distinct forms for $A,B$ span the two-dimensional pencil. The same holds for $B,C$. Since $T$ takes the first basis to proportional copies of the second, it preserves the pencil. Its induced projective action has dyadic order $q$. In the stated characteristic this action is diagonalizable. A nonfixed target point has orbit of length $q$, and every member of the orbit of $A$ is another complete simple fiber on $H$. Thus $3\le q\le n/D<8$, forcing $q=4$. Its orbit can be sent to $\mu_4$ by a target coordinate change taking the two fixed points to $0,\infty$.

Let $l$ be the order of the source rotation. Its kernel on the pencil has order $l/4$. It acts freely on $A\subset H$, so $l/4\mid D$. Since $D\equiv 2\pmod4$, this leaves $l=4,8$. Source points $0,\infty$ map to central targets. They land in different targets, since if both mapped to one, the other target fiber would be a union of free orbits with multiplicities constant on each, giving $l\mid D$. At each source fixed point the local index is consequently congruent to $D\bmod l$.

For $l=4$ the local action on a target uniformizer at a central point is a primitive fourth root. The action on a source uniformizer is also primitive of order four. Comparing the leading term of the pullback forces odd local index, whereas $D\equiv2\pmod4$. For $l=8$ both local indices are at least six since $D\equiv6\pmod8$. This would give $r\ge10$, contradicting $2r+b+k\le6$.

The same argument excludes a Möbius progression for **each triangle pencil required at the first half-rate successor**, 268,435,457 errors. Here the fiber degree is $D'=n/4-1$. The orbit on the pencil again has length four, and $l/4\mid D'$ forces $l=4$ because $D'$ is odd. The two source fixed points go to distinct central targets with indices $3\bmod4$, so $r\ge4$ and $b=2$. But the mixed partial gives $2r+b+k\le n-2-4D'=2$. The half-rate punctured criterion always supplies at least two such triangle pencils. [Triangle construction](first-prime-punctured-four-list.md#a-full-odd-pencil-is-necessary) · [Number of triangles](half-successor-joint-pencil-height.md#how-many-of-the-four-head-triangle-pencils-must-be-indecomposable)

## An independent check after descent in the order-eight case

The kernel in this case is the antipode, so $R$ descends by $x\mapsto x^2$ to a degree-$M-1$ map on $\mu_{4M}$, where $M=n/8=4L$. Each of its four complete fibers consists of $(D/2)=M-1$ simple sites, since the square map is unramified on $H$ and each original fiber is antipodally invariant. The four remaining sites form one orbit under the faithful order-four rotation, so all satisfy $x^4=a$ for a single $a\in\mu_M$.

Invert the new target coordinate if necessary to have value zero above source zero. Invariance up to multiplication by a primitive fourth root makes the map $x^u A(x^4)/B(x^4)$, with $u\in\{1,3\}$, coprime $A,B$ and $B(0)\ne0$. Indeed its ratio to $x^u$ is invariant; a possible nonnegative multiple of four in its vanishing order at zero goes into $A$. Since its degree is $M-1\equiv3\pmod4$, its numerator has degree $M-1$, so $u=3$, $\deg A=L-1$ and $s=\deg B\le L-1$. The four fibers give the identity in $Y=x^4$

\[
 (Y-a)Y^3 A(Y)^4-(Y-a)B(Y)^4=c(Y^M-1),\qquad c\ne0 .
\]

The differential operator $J(G)=Y G''-(M-1)G'$ kills $1,Y^M$. Both terms on the left have the same image. On the denominator side the input has degree $4s+1<M$, so its image is nonzero of degree $4s$, since $J(Y^v)=v(v-M)Y^{v-1}$. Every nonzero root of $A$ or $B$ of multiplicity $v$ gives at least $4v-2\ge2v$ zeros of this image. A root at $a$ even has the additional $Y-a$ factor. At zero the numerator input is divisible by $Y^{3+4v_0(A)}$, so the image has order at least $2+4v_0(A)$. Coprimality and $B(0)\ne0$ now give at least $2+2\deg A+2s=2L+2s>4s$ zeros with multiplicity. This proves the same contradiction directly on the quotient.

The proof is written. The finite-field checker verifies 900 scaled harmonic pencils in $\mathbf F_{17}$; the largest local charge attains its theoretical bound of six. It also checks both production degrees and the arithmetic of the descended equation. [Finite-field checker](../../../scripts/probes/probe_quarter_mobius_progressions.py)
