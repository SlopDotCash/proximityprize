# Character tests for opposite edges of four saturated heads

A possible four-head overrun of the budget $2n$ at $n/2$ errors and rate one quarter on the second named field would have four singleton sites. The other sites belong to six disjoint double strata, paired into three opposite pairs. The two sides of pair $i$ have the same size $s_i$, where $2\le s_i\le d-1$ and $\sum_i s_i=2d$ for $d=n/4-1$. The four triangle determinants are nonzero multiples of their monic locators and have a signed relation. The results below apply to that relation at any length. [Derivation of saturation and the six strata](quarter-saturated-symmetry.md)

## A product of three rational functions

Write $(A,A'),(B,B'),(C,C')$ for the opposite pairs of monic locators, with orientations chosen so that the four face locators are $ABC,AB'C',A'BC',A'B'C$. There are nonzero coefficients $t,u,v,w$ satisfying
\[
 tABC+uAB'C'+vA'BC'+wA'B'C=0. \tag{1}
\]
Over a field of odd characteristic adjoin $z$ with $z^2uvw=t$. Set $U=zuA/A'$, $V=zvB/B'$, $W=zwC/C'$. Dividing (1) by $A'B'C'$ and multiplying by $z$ gives $UVW+U+V+W=0$. Equivalently the three rational functions $(1+U)/(1-U)$, $(1+V)/(1-V)$ and $(1+W)/(1-W)$ have product one. Each has degree $s_i$, with its full $+1$ and $-1$ fibers the roots of its positive and negative locators, respectively. Coprimality and odd characteristic prevent cancellation. If $tuvw$ is nonsquare, the nontrivial automorphism of the quadratic extension exchanges each function with its inverse. Its value at a base-field point belongs to the norm-one group wherever the numerator and denominator are nonzero. This factorization tests the face equation. Realization by heads and their number of fresh directions require additional conditions. [Lean factorization](../../../ArkLib/Research/ProximityGap/Frontier/QuarterOppositeEdgeCharacters.lean) · [Direction condition](quarter-saturated-opposite-directions.md)

## Recovering the orientations from the coarse partition

Let $D_i$ be the union of the two sides, $P_1=AA'$, $P_2=BB'$, $P_3=CC'$, and $Q$ the four-hole locator. For $x\in D_i$, with $i,j,k$ in cyclic order, define $\eta_i(x)=\chi(P_j(x)P_k(x))$ for the quadratic character. The coarse partition and the holes alone determine these signs. On a subgroup of order $n$ in characteristic prime to $n$, differentiating $P_1P_2P_3Q=X^n-1$ gives
\[
 \eta_i(x)=\chi\left(\frac{n}{xQ(x)P_i'(x)}\right).
\]
Write $c_0=t$ and $(c_1,c_2,c_3)=(u,v,w)$. On the positive side of $D_i$ the sign is $\chi(-c_k/c_j)$, and on the negative side it is $\chi(-c_i/t)$. For instance at a root of $A$ the equation becomes $vBC'=-wB'C$, so $BB'CC'=(-w/v)(B'C)^2$. At a root of $A'$ the corresponding square is $(-u/t)(B'C')^2$. The product of these two signs is always $\theta=\chi(tuvw)$, and the product of the three positive-side signs is $\chi(-1)$.

Consequently a split partition ($\theta=1$) has a constant sign on each $D_i$. A nonsplit partition has exactly $s_i$ sites of either sign in each $D_i$ and the three sign masks determine its orientations up to four choices. There is also a check using just one block and the holes. Over a field where $-1$ is square, multiply the derivative identity over $D_i$. The product of the $P_i'$ values is a signed square by the Vandermonde determinant. Since $|D_i|$ is even, the result is
\[
 \chi\left(P_i(0)\prod_{Q(h)=0} P_i(h)\right)=\theta^{s_i}.
\]

When $4\mid(q-1)$ the quartic character provides a further linear test for split partitions. Choose an additive quartic character $[\ ]_4$ on the nonzero field elements, with reduction $[\ ]_2$. For $x\in D_i$ let $L_j=[P_j(x)]_4$, $L_k=[P_k(x)]_4$ and
\[
 R^+=[-c_k/c_j]_4+L_j-L_k,\qquad R^-=[-c_i/t]_4+L_j+L_k.
\]
If $a_y$ is one on each positive side and zero on the negative side, put $b_x=\sum_{y\in D_j\cup D_k}[x-y]_2a_y$. On the positive side of $D_i$, the equation gives the square of the ratio of the two positive locators at $x$, so $2b_x=R^+$ modulo four. On the negative side the square of their product gives $2b_x=R^-$ modulo four. In a split partition passing the quadratic tests both $R$ values are even. Thus for fixed coarse blocks and coefficient character classes the following is a single affine linear system over $\mathbb F_2$:
\[
 b_x=R^-/2+a_x(R^+-R^-)/2 .
\]
It also requires exactly $s_i$ positive sites per block. A common scaling sets $t=1$, leaving at most $4^3$ coefficient character choices. [Lean side signs and derivative](../../../ArkLib/Research/ProximityGap/Frontier/QuarterOppositeEdgeCharacters.lean) · [Exact checks of the quartic equations](../../../scripts/probes/probe_quarter_opposite_pairs.py)

## Exact enumeration at length 16

Here $d=3$ forces $s_1=s_2=s_3=2$. There are $\binom{16}4\binom{12}4\binom84/6=10,510,500$ coarse layouts. Blocks are unordered and a fixed canonical ordering is used to count orientations. Each coarse layout has $6^3$ possible oriented subdivisions before screening. The computation groups hole sets under dihedral symmetry. Inversion sends every six-root monic face polynomial to its reflected face polynomial times a nonzero scalar and a common Laurent monomial, preserving rank. In each allowed orientation two faces alone survive at a negative-side site, determining the unique possible normalized coefficient for one face. Evaluating the resulting degree-six relation at seven distinct roots suffices.

| Field | Split coarse layouts passing the sign test | Nonsplit coarse layouts passing the sign test | Oriented layouts tested | Oriented layouts satisfying (1) |
|---|---:|---:|---:|---:|
| $\mathbb F_{97}$ | 23,324 | 1,166,784 | 9,705,120 | 1,792 |
| First named field | 31,716 | 1,253,536 | 11,864,800 | 1,344 |
| Second named field | 31,716 | 1,253,536 | 11,864,800 | 1,344 |
| $\mathbb F_{65537}$ | 10,510,500 | 0 | 2,270,268,000 | 1,344 |

All counts include the sizes of the hole-set orbits. Run `python3 scripts/probes/probe_quarter_opposite_pairs.py --fields 97 first second 65537`. It checks the quartic equations and the product over the holes for every surviving orbit representative.

## Why the length-16 rank tests transfer between fields

Label the sites by powers of a primitive complex sixteenth root $\zeta$ and specialize $\mathbb Z[\zeta]$ at any prime of residue characteristic $p\equiv1\pmod{16}$. Each coefficient in row $j$ of the four degree-six monic face locators has absolute value at most $\binom6j$ under every embedding. By Hadamard, the absolute value of a four-row minor is at most $40\cdot30\cdot30\cdot12=432000$. The same bound applies to smaller minors. A nonzero minor therefore has a nonzero integer norm of absolute value at most $432000^8$. For every $p>432000^8$ such a minor stays nonzero upon specialization. Every vanishing minor specializes to zero. Thus the face ranks, layout by layout, agree with the complex ranks. Every triple of faces is independent because evaluating a relation on the opposite-side roots forces all its coefficients from the first one, and all ratios are nonzero. Hence the 1,344 signed relations are the same layouts over characteristic zero and at every such prime.

The same argument covers the actual fresh directions. Subtract head zero from the other three scalar splines of degree at most three. The twelve double-site constraints form a matrix with twelve columns. Each row is either the evaluation of one spline or the difference of two evaluations, with at most eight unit-modulus entries. After choosing the four singleton owners, each fresh head-site difference is another row of the same kind. The rank after adjoining one row detects whether it vanishes on the spline kernel, and the rank after adjoining two nonzero restrictions detects whether they give the same projective functional there. When the kernel has dimension two, any independent pair of scalar solutions gives exactly those projective directions; a dependent pair gives at most one. Every square minor of every augmented matrix has absolute value at most $(\sqrt8)^{12}$. Its norm is bounded by $2^{144}$. These spline ranks therefore transfer at every $p>2^{144}$. Both named primes exceed both bounds. This transfer works with an arbitrary primitive root in each field because the complex ranks are Galois invariant. It concerns sixteen sites; the growing norm bound does not transfer the production layout problem.

For a characteristic-zero approach to maps taking roots of unity to roots of unity, Beukers and Smyth give an explicit bound in terms of the Newton polygon area, together with an algorithm. Their theorem applies to torsion values in both coordinates. The norm-one condition above alone need not have a torsion lift to characteristic zero. [Beukers and Smyth, *Cyclotomic points on curves*](https://www.maths.ed.ac.uk/~chris/preprints/beukers_smyth.pdf)
