# A prescribed Mordell–Weil height for a punctured four-head list

Let $n=4h$ at the first named production prime and suppose that one of the three punctured four-head configurations exists. Its marked sites determine an elliptic curve over $\overline{\mathbf F}_p(X)$. Its Mordell–Weil lattice must contain a **primitive section of Shioda height $h-3/2$** in the complete overlap graph and **$h-1$** in the other two cases. Except for one possible $I_4$ fiber in the missing-edge case, this is the smallest height any non-torsion section on that surface could have. The argument applies to these marked arrangements over other fields of characteristic greater than three as well, with $h\ge3$ and $p\nmid n$.

## The twist and its everywhere integral double

Use the notation $O,U_i,F,G,R$ for the ordinary sites, private classes, two pencils and their quotient in the [four-fiber equations](four-fiber-quadratic-characters.md). Write $A_i=L_{U_i}$, and choose the squarefree polynomial representative $D$ of $F(F-1)(F-R)$ including its constant square class. In the two shapes with distinct overlaps its finite roots are $O\cup\{a,d\}$, and in the triple shape they are $O\cup\{d\}$. Thus the marked sites determine $D$ up to constant twist over the base field and up to squares over its algebraic closure. Put $N=\deg D$ and $m=N/2$. The values of $N$ are $n-6,n-4,n-4$ in complete, missing-edge and triple order.

Consider the elliptic surface
$$
 E:\quad Y^2=Z(Z-D)(Z-DR).
$$
Both $D$ and $DR$ are degree-$N$ polynomials. There is a rational section $P$ with $Z(P)=DF$ because the product of its three factors is a square. The duplication formula gives
$$
 Z(2P)=\frac{D(F^2-R)^2}{4F(F-1)(F-R)}.
$$
In fact $Z(2P)$ is a constant times $B^2$, for the polynomials shown below.

| Shape | $B$ |
|---|---|
| Complete six overlaps | $[\alpha^2 A_0^2(X-a)(X-b)-\kappa A_1^2(X-c)(X-d)]/(X-f)$ |
| Missing edge | $\alpha^2 A_0^2(X-a)(X-b)-\kappa A_1^2(X-c)(X-d)$ |
| Triple | $\alpha^2 A_0^2-\kappa A_1^2(X-c)(X-d)$ |

These formulas follow by substitution. In the first row $F(f)=R(f)=1$ makes the displayed numerator vanish at $f$. In all three rows $\deg B\le m$. Thus $2P$ avoids the zero section even at infinity, where the integral chart divides $Z$ by $X^N$. The other two duplication formulas likewise make $Z(2P)-D$ and $Z(2P)-DR$ exact squares in the rational function field, and they are polynomials of degree at most $N$. We obtain three polynomials of degree at most $m$ satisfying $B_0^2-B_1^2=D$ and $B_0^2-B_2^2=DR$.

## The height floor and primitivity

At an ordinary site where $R$ avoids $0,1,\infty$, the twist has fiber $I_0^*$. At a simple zero or pole of $R$, or simple root of $R-1$ outside $O$, the fiber is $I_2$. This includes infinity if the second root of $R-1$ is infinite. The three types of colliding roots at a pole, zero and unit value of $R$ are respectively $\{0,D\}$, $\{0,DR\}$, and $\{D,DR\}$. All other unmarked places have good reduction. These assertions follow from the valuations of $\Delta=16D^2(DR)^2(D-DR)^2$ and $c_4=16(D^2-D^2R+D^2R^2)$ in the indicated integral charts. The complete case has $n-8$ fibers of type $I_0^*$ and six of type $I_2$. The triple case has $n-5$ and three, respectively.

There are two possible collisions in the missing-edge case. A second root of $R-1$ at an ordinary site yields $I_2^*$, while a second root coinciding with $e$ yields $I_4$. At an $I_4$ point the section $P$ meets the identity component because $F(e)$ is finite and differs from 1, the full unit fiber of $F$ being $U_2$. All the displayed Weierstrass charts are minimal, with discriminant order at most eight. Their transition at infinity, or equivalently the sum of the discriminant orders, gives $\chi(\mathcal O_E)=m$. [Schütt and Shioda, §§4, 6 and 8](https://arxiv.org/abs/0907.0298)

The geometric component groups of $I_2,I_0^*,I_2^*$ have exponent two. Consequently $2P$ meets the identity component at every place. Its height is $2m$ because it is disjoint from the zero section. Hence the height of $P$ is $m/2$.

More generally every non-torsion $Q$ has $4\langle Q,Q\rangle=\langle2Q,2Q\rangle\ge2m$ in the absence of $I_4$. In the exceptional $I_4$ case only its component of index two can contribute to $2Q$, and its local correction term is one, giving $4\langle Q,Q\rangle\ge2m-1$. Both conclusions follow from the height pairing and nonnegativity of the intersection of distinct sections. If $P=kQ+T$ with $|k|\ge2$ and $T$ torsion, they imply $m/2\ge2m-1$, impossible for $m\ge1$. This proves primitivity, and in the cases without $I_4$ it gives equality in the universal lower bound for non-torsion heights. These are necessary geometric conditions on the marked twist. Its production rank and attainment of this floor remain open. [Shioda, Theorem 8.6](https://rikkyo.repo.nii.ac.jp/record/10027/files/AA00610867_39-02_05.pdf) · [Correction terms in Schütt and Shioda, §11.8 and Table 4](https://arxiv.org/abs/0907.0298)

## Two independent shortest sections under a marking symmetry

In the complete overlap case, suppose a Möbius involution $s$ preserves $H$ and exchanges the members of each pair $(a,d),(b,c),(e,f),(z,w)$. Then $R\circ s=R$ because it permutes each of three labeled fibers. The odd-valuation divisor of $D$ is preserved, hence $D\circ s/D$ is a square over the algebraic closure of the constants. The resulting lift of $s$ to $E$ preserves the labels of the global 2-torsion sections $T_0,T_D,T_{DR}$. It supplies a second section $sP$ with the same height.

Exactly one point in each of the first three marked pairs is a singular reduction of $P$. These are $a,b,f$, as seen by substituting $Z(P)=DF$ into the three respective collisions of roots. At the other sites $d,c,e$, the section has smooth reduction. If $sP=\pm P+T$ for a torsion section $T$, its projection to the local $I_2$ component group must therefore be nonzero at all three collision types. The 2-primary torsion of $E$ equals $E[2]$, since it injects into the component group at any $I_0^*$ site in odd characteristic: the formal group and additive identity component have no 2-primary torsion. Odd order torsion always has zero component at $I_2$. No nonzero member of $E[2]$ belongs to all three of the pairs $\{T_0,T_D\},\{T_0,T_{DR}\},\{T_D,T_{DR}\}$. This excludes such $T$. Equal positive heights would force $sP=\pm P$ modulo torsion if the sections were dependent. Thus this marking requires **two independent shortest sections**.

For $s(X)=\tau/X$ with both fixed points in $H$, both fixed points are ordinary since the eight exceptional marks are distinct and paired. The product of the roots of $D$ is $-\tau^{N/2}$, using the two fixed roots and all remaining two-point orbits. Consequently a square root of $D(\tau/X)/D(X)$ is $cX^{-N/2}$ with $c^2=-\tau^{N/2}$. Its product with its transform is $-1$, so either lift acts on $E$ with square equal to negation. Invariance of the height pairing gives $\langle P,sP\rangle=-\langle sP,P\rangle=0$. In this case the two shortest sections are orthogonal.

The finite verifier computes $Z(2P)$ by exact polynomial division and checks that all three shifted polynomials are squares of the stated half-degree bound for every genuine example in the three sixteen-site controls. [Polynomial verification](../../../scripts/probes/probe_four_fiber_quadratic_characters.py)

## A converse with finitely many local component requirements

Fix one of the marked configurations, including the hole and any all-agree coordinate. Require that the displayed rational $R$ exists with the stated fibers. In particular, in the complete case $R(e)=R(f)=1$. The corresponding punctured four-word configuration exists over the base prime field **if and only if**, on one of the two constant square-class twists, there is a base-rational section $P$ of height $m/2$ satisfying the conditions in the table. Here singular and smooth refer to specialization on the minimal Weierstrass cubic; the smooth locus gives the identity component of the Néron model.

| Shape | Required local components |
|---|---|
| Complete | Singular at $a,b,f$, smooth at $d,c,e$. |
| Missing edge | Singular at $a,b$, smooth at $d,c$ and at every root of $R-1$ outside $O$, including infinity if present. At an ordinary root of $R-1$, $P$ or $P+T_0$ must lie in the identity component. |
| Triple | Smooth at $c,d,e$. |

Necessity follows directly from the prescribed divisors of the two normalized pencils. At an ordinary root of $R-1$ in the missing-edge case one has either a pole of $F$ or a simple zero. At a pole $DF$ is a unit; at a zero the translated coordinate $D^2R/(DF)$ is a unit. These are the two allowed $I_2^*$ components.

For sufficiency, $2P$ is narrow by the fiber types and the smooth requirement at any $I_4$ point. Its height is $2m$. The height formula gives $(2P)\mathbin{.}\mathcal O=0$, so $2P$ never specializes to the zero section. Every translate of $P$ by a 2-torsion section is consequently disjoint from the zero section. At a good place $P$ cannot specialize to 2-torsion. Write $F=Z(P)/D$ and $G=F/R$.

At each ordinary $I_0^*$ place, exactly one of $P,P+T_0,P+T_D,P+T_{DR}$ has identity component: the three nonzero 2-torsion points have distinct nonidentity components, as each reduces to the singular point and their pairwise differences are the third point. The identity translate has finite nonzero $Z$ residue. For any two other roots $e_j,e_k$ of the cubic, translation by the root $e_i$ satisfies
$$
 (Z(P+T_{e_i})-e_i)(Z(P)-e_i)=(e_i-e_j)(e_i-e_k).
$$
All differences of the three roots have order one at this place. Thus the identity choice for $P$ itself gives a simple pole of $F$, and the choices $T_0,T_D,T_{DR}$ give a simple zero of $F,F-1,F-R$ respectively. Their other finite branches remain distinct. If an ordinary root of $R-1$ has type $I_2^*$, the allowed identity or $T_0$ translate yields a pole or simple zero by the same formula, since $D^2R$ still has order two.

At an $I_2$ site exactly two roots coalesce to first order. If $P$ reduces to their singular point, adding either colliding 2-torsion section puts it in the identity component. It cannot meet a smooth 2-torsion section there since $2P$ avoids zero. The translation identity then shows its distance to each colliding root has order exactly one. If $P$ is smooth, it avoids the singular point as well as the remaining smooth 2-torsion. At the possible doubled $I_4$ root the required smooth reduction gives the same avoidance. This determines all exceptional zeros and poles; at infinity use $Z/X^N,D/X^N$ in the identical argument. All other good places avoid the four branch values.

It follows that the divisors of $F,G,F-1,G-1$ are exactly the four split-pencil divisors from the character test. The ordinary sets $U_0,U_1,U_2,U_3$ consist of the sites where $F$ is zero, infinite, one or equal to $R$. Comparing the degrees of these complete zero and pole fibers and using $\sum |U_i|=|O|$ gives the four private sizes in each of the three tables. This step uses neither a prior balanced coloring nor prescribed ordinary components.

To recover the scalar polynomials, take $D_0=0$. In the complete case set $D_1=(X-w)(X-f)A_2A_3$, and in the other two cases set $D_1=A_2A_3$. Define $D_2=D_1/(1-F)$ and $D_3=D_1/(1-G)$. Substituting the divisors proves these are polynomials of degree at most $2h-2$. At ordinary points in $U_i$ the other three scalar polynomials agree while $D_i$ differs. The same formulas at $a,b,c,d$ give the designated double errors, and at $e$ the identity $R=1$ makes $D_2=D_3$. At $f$ in the complete case the common zero of $1-F$ and $1-G$ is canceled and $D_0=D_1$; both differing values are nonzero. The optional all-agree site $w$ vanishes in every word. At the triple site $t$ set the center to $D_1(t)$, which differs from the other three values because none of $F(t),G(t)$ is $0,1,\infty$. This gives all four required joint agreement counts. The criterion is arithmetic: a section defined only after extending the constant field does not yield a list over the named prime field.
