# One of the paired half-successor pencils must be indecomposable

Let $D=2^{28}-1=268435455$. A four-head punctured list at the first half-rate successor requires a degree-$D$ pencil with natural geometric monodromy **$A_D$ or $S_D$ on all its sheets**. In fact any two of the required pencils with nonconstant quotient of degree at most two cannot both decompose over the algebraic closure. The earlier single-pencil obstruction allowed an outer map of degree three or five for each pencil separately. The existence of an indecomposable pencil satisfying the marked finite-field conditions remains open. [The two pencils](four-fiber-quadratic-characters.md) · [Single-pencil monodromy](half-successor-pencil-monodromy.md)

## A family of curves of genus at most sixteen

Work over the algebraic closure of either named field. Suppose $F=U(T)$ and $G=V(S)$ both decompose. Their outer degrees $a=\deg U$ and $b=\deg V$ belong to $\{3,5\}$. Each outer function has simple zeros and poles, because the corresponding composite fibers are simple. Write $e=\deg R$ for $R=F/G$, so $1\le e\le2$.

In $\mathbf P^1_z\times\mathbf P^1_w\times\mathbf P^1_r$ take the closure $Y$ of $U(z)=rV(w)$. The pencil on the first two lines has $2ab$ distinct simple base points, where both functions vanish or both have poles. Its graph is their blowup and is smooth. A general fiber is a smooth connected curve of bidegree $(a,b)$ and genus $g=(a-1)(b-1)\le16$. For $r\ne0,\infty$ a singularity requires two critical points, one of each outer function, with critical values of ratio $r$. The base points are smooth in every fiber. Thus at most $2+(2a-2)(2b-2)\le66$ finite or infinite base values can be singular. Smoothness follows away from these values and connectedness follows from ampleness of a positive bidegree divisor.

At $r=0$ the fiber consists of $a$ vertical and $b$ horizontal projective lines. Each component has at least three nodes, and each node has local smoothing equation $uv=r$ in suitable étale or completed coordinates. In particular the pencil has nonzero generic Kodaira–Spencer class. Indeed it is a family of stable curves near $0$. The tangent map to the local deformation space of a node sends $\partial/\partial r$ to a nonzero first-order smoothing. The tangent bundle of the stack of stable curves is locally free, so a differential generically zero would also be zero there. Nonzero generic Kodaira–Spencer persists under every separable base change. [Deformation theory of stable curves](https://www.numdam.org/articles/10.1007/BF02684599/) · [Szpiro, Exposé III, §3](https://www.numdam.org/item/AST_1981__86__R1_0.pdf)

Under the base change $r=R(x)$ from $B=\mathbf P^1_x$, the generic curve has a rational point $(z,w)=(T(x),S(x))$. Let $A\subset B$ contain all preimages of the possible singular fibers and one extra point outside them. Then $|A|\le133$. We next choose a smooth projective curve $B'$ mapping finitely and separably to $B$, tamely ramified only above $A$. Write $d=[K(B'):K(B)]$. The marking given by the rational point will extend to a smooth section $E$ of a semistable model $X$ over $B'$.

## A degree-six cover branched only at the section

On a smooth once-pointed genus-$g$ geometric fiber there is a connected $S_3$-Galois cover with inertia three at the marking and no other branch points. In the prime-to-characteristic presentation of the punctured fundamental group, send the first pair of handle generators to $(12),(23)$ and the other pairs to the identity. Their commutator is a 3-cycle, giving the required inverse puncture loop. There are at most $6^{2g}$ such homomorphisms since the puncture loop is determined. [SGA 1, Exposé XIII](https://arxiv.org/abs/math/0206203)

Here is why the data extend over a tame $B'$ with the stated branch set. First adjoin level-three structure on the original genus-$g$ Jacobian. This extension is étale at every good fiber and tamely ramified everywhere, since every prime divisor of $|\mathrm{GL}_{2g}(3)|$ is at most $3^{32}<p$. It gives semistable reduction. In the inertia criterion the eigenvalues of an inertia element are roots of unity, and an integral 3-adic matrix congruent to identity modulo three has no root-of-unity eigenvalue other than one. Indeed every eigenvalue differs from one by 3-adic valuation at least one, whereas a nonidentity 3-power root has smaller valuation. The Jacobian is therefore semistable, which is equivalent to semistability of the curve. Extend the marking in the regular semistable model and stabilize the pointed fibers. [Deligne–Mumford, Theorem 2.4](https://www.numdam.org/articles/10.1007/BF02684599/)

Over the smooth locus the chosen covers form a finite étale cover of the base. A connected $S_3$-cover with identified group has relative automorphism group the center of $S_3$, which is trivial. The degree is at most $6^{2g}\le6^{32}<p$, so its normal closure is also tame. Over the boundary, properness of the stack of balanced admissible covers extends this family after a local tame extension. The relative stack is tame over the fixed pointed stable target: at a node the two branches have inverse inertia and the local smoothing parameter acquires a root whose order divides the group order. Automorphisms over the fixed target act on covers of each component through permutations of at most six sheets, with further node stabilizers of order dividing six. Hence no wild stabilizer occurs. To realize these local tame extensions on one projective curve, take a common prime-to-$p$ multiple of their ramification indices and a cyclic Kummer cover with full ramification over the required places. One point above the extra point of $A$ suffices to balance the branch divisor degree modulo this multiple. The required root of its divisor class exists by divisibility of the geometric degree-zero Picard group. No new singular fibers occur over the smooth locus. [Abramovich, Corti and Vistoli, §§3–4](https://arxiv.org/abs/math/0106211)

We obtain a finite admissible cover $\pi:Z\to X$ of degree six over $B'$. The pointed target is semistable after forgetting its single marking. A rational component has at least two nodes, with a marking if it has only two. The source remains semistable without markings. On each normalized component the tame Hurwitz formula with the node branches deleted multiplies the target logarithmic degree, counting the marked point with weight $2/3$. This degree is positive on every rational target component. The source has no unstable rational tail. Total-space singularities of the nodal families are of type $uv=t^m$ and have crepant surface resolutions. Section intersections and relative dualizing squares can be computed on these models or their regular semistable resolutions.

Write $H=\omega_{X/B'}\cdot E$. Adjunction gives $E^2=-H$. In codimension one the only ramification of $\pi$ is the horizontal inertia-three ramification above $E$. At generic points of the reduced special fibers the base uniformizer has order one and the residue-field extensions are separable. Thus as rational divisor classes

$$
\omega_{Z/B'}=\pi^*(\omega_{X/B'}+\tfrac23 E),\qquad
\omega_{Z/B'}^2=6\omega_{X/B'}^2+\tfrac{16}{3}H\ge\tfrac{16}{3}H.
$$

The source has fiber genus $g'=6g-3\le93$. Its modular inseparability exponent is zero because the $S_3$ quotient has nonzero generic Kodaira–Spencer. Indeed the automorphisms of a smooth genus-at-least-two curve form an unramified group scheme, so descent of the source through Frobenius would descend its automorphisms and their quotient as well. Szpiro's bound on the relative dualizing square and tame logarithmic Riemann–Hurwitz on $B'\to B$ now give

$$
\tfrac{16}{3}H\le4g'(g'-1)(2g(B')-2+\#\{\text{singular source fibers}\})
\le4\cdot93\cdot92\cdot131\,d.
$$

The last logarithmic degree is at most $d(|A|-2)$ because every singular source fiber lies over $A$. This proves $H/d\le840627$. [Szpiro, Exposé III, Lemma 0 and Theorems 2 and 3](https://www.numdam.org/item/AST_1981__86__R1_0.pdf)

## The adjunction degree at the same section

Let $v:B'\to\mathbf P^1_r$ denote the composite base map of degree $ed$. The equation defining $Y$ has tridegree $(a,b,1)$. Adjunction identifies

$$
\omega_{Y/\mathbf P^1_r}\otimes f^*\mathcal O(-1)=\mathcal O_Y(a-2,b-2,0).
$$

Take all the standard monomials of bidegree $(a-2,b-2)$ as sections of this bundle. Equivalently they are absolute canonical two-forms with a twist by $f^*\mathcal O(1)$, since $\omega_{\mathbf P^1}=\mathcal O(-2)$. Pull them back along the dominant separable rational map from a regular semistable resolution of $X$ to $Y$. The resulting absolute two-forms, twisted by $v^*\mathcal O(1)$ from the base, are regular everywhere. Indeed a rational map to the proper smooth surface $Y$ is defined at every codimension-one point of a normal surface. Regular sections of the resulting line bundle extend across the remaining finite set on the smooth source.

Along $E$ these forms are sections of a line bundle of degree $H+2g(B')-2+ed$. They induce the Segre–Veronese map of $(T,S)$ of bidegree $(a-2,b-2)$ on $B'$. This follows on the generic fiber where the base change is separable and the displayed relative differentials are the adjunction basis. A common zero of the restricted sections only increases the degree of the line bundle relative to that of the induced morphism. Consequently

$$
 d\big((a-2)\deg T+(b-2)\deg S\big)\le H+2g(B')-2+ed\le H+133d.
$$

Each term $(a-2)\deg T=(1-2/a)D$ and $(b-2)\deg S=(1-2/b)D$ is at least $D/3$. We obtain $H/d\ge178956837$, contradicting the upper bound $840627$. The argument includes multiple critical values and non-nodal fibers of the original pencil because it pulls regular absolute forms from its smooth total space. The source and target height calculations use the same section of the semistable model. [Kernel-checked numerical contradiction](../../../ArkLib/Research/ProximityGap/Frontier/HalfSuccessorPencilMonodromy.lean) · [Integer cross-check](../../../scripts/probes/probe_half_successor_pencil_monodromy.py)

The group and surface arguments are written proofs using the cited theorems. Lean checks the endpoint inequalities. This proves the simultaneous-decomposition exclusion, leaving the common finite-field fiber and marking equations for a full alternating or symmetric pencil as the remaining obstacle.

## How many of the four-head triangle pencils must be indecomposable?

A triple of heads gives a degree-$D$ pencil whenever its three pairwise error intersections are distinct singleton sites. There are four such triangles in the six-double marking, three in the triple-site marking, and two in the five-double marking. In the triple-site marking they consist of the head outside the triple and any two heads in it. In the five-double marking they are the two triangles of the graph with one missing edge. [Triangle construction](first-prime-punctured-four-list.md#a-full-odd-pencil-is-necessary)

Any two such triangles share an edge $ij$. Choose the target coordinates on the pencil for $ijk$ so its zero and pole fibers are the sets obtained from $E_i,E_j$ by deleting their two triangle overlaps. Replacing $k$ by the fourth head changes each of these fibers at most by a single replacement. All the candidate zero sets are disjoint from all the candidate pole sets, since the common $ij$ site has been removed. The new quotient therefore has degree at most two. It is nonconstant: both fibers change in the six- and five-double markings, and the fiber belonging to the head outside the triple changes in the triple-site marking. The obstruction applies pairwise. Hence at least **three of four** triangle pencils in the six-double marking, **two of three** in the triple-site marking and **one of two** in the five-double marking have full natural alternating or symmetric monodromy.

## A degree gap for nonconstant quotients of two compositions

The same proof gives a quantitative conclusion for any two degree-$D$ compositions $U(T),V(S)$ with outer degrees $a,b\in\{3,5\}$ and simple outer zeros and poles. Suppose their quotient is nonconstant of degree $e$. It is separable since $e\le 2D<p$. Write $L=2+(2a-2)(2b-2)$, $g'=6(a-1)(b-1)-3$ and $c=3g'(g'-1)/4$. There are at most $Le+1$ excluded points on $B$. The two height inequalities with this count give

$$
 (a-2)\deg T+(b-2)\deg S+c+1\le ((c+1)L+1)e.
$$

Thus the quotient has degree at least **31,457** for two cubic outer maps, **4,959** for a cubic and a quintic, and **761** for two quintic outer maps. This last calculation uses the two small outer maps and the named characteristic only. The split-fiber and monodromy estimates supply the permitted outer degrees in the four-head application. [Lean integer ceilings](../../../ArkLib/Research/ProximityGap/Frontier/HalfSuccessorPencilMonodromy.lean) · [Independent rational calculation](../../../scripts/probes/probe_half_successor_pencil_monodromy.py)
