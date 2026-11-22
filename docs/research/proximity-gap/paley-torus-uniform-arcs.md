# Uniform Paley discrepancy on arcs of a typical torus generator

Let $T$ be a split or nonsplit maximal torus in $\mathrm{PGL}_2(\mathbb F_p)$, with regular orbit $\Omega$ of size $m=|T|=p\pm1$. Fix $0<\epsilon<1$, an integer $r\ge\lceil2/\epsilon\rceil$, and $0<\delta<\epsilon/(4r)$. At every sufficiently large odd prime, all but a fraction
$$
 O_r\big(p^{-\epsilon/2+2r\delta+o(1)}\big)
$$
of generators $g$ satisfy the following simultaneously. For every $p^\epsilon\le H\le m$ and **every two starting sites** $x,y\in\Omega$, the Paley operator between the arcs $(g^ix)_{0\le i<H}$ and $(g^jy)_{0\le j<H}$ has norm at most $2H p^{-\delta}$. The starts, lengths, weights and subsets can all be chosen after $g$. In particular this includes $H$ of order $\sqrt p$ and arbitrary relative exponent offsets. The generator is sampled in the torus at each fixed prime.

The matrix entry for projective sites $u,v$ is $\chi(\det(\tilde u,\tilde v))$, with nonzero homogeneous lifts and $\chi(0)=0$. Changing lifts or applying a common projectivity affects norms only by unit signs. Therefore the starting sites are determined up to a single relative translation $c\in T$. Dense subsets of the two arcs, with arbitrary vertex weights bounded by one, have relative discrepancy $O(p^{-\delta})$ when the densities are bounded below. On every subset of size $z\ge c_0H$ of a single arc, the fraction of singular four-site principal Paley minors modulo three is $1/4+O_{c_0}(H^{-1}+p^{-2\delta})$. Indeed its fourth trace is at most its squared operator norm times its squared Frobenius norm, at most $4H^2z^2p^{-2\delta}$. The scope here is arcs of typical generators. [Projective signs and the exact four-site identity](paley-four-site-rank.md#exact-normalization-and-the-four-site-determinant)

## The two-parameter moment

Fix $1\le L\le m$ with $2L<p$. Let $P_{A,C}$ be the $L$-by-$L$ block with sites $A^ix$ and $CA^jx$, $0\le i,j<L$, for $(A,C)\in T^2$. Retain repeated exponent labels when $A$ has smaller order. We prove
$$
 \frac{1}{m^2}\sum_{A,C\in T}
 \frac{\operatorname{tr}((P_{A,C}P_{A,C}^{*})^r)}{L^{2r}}
 \ll_r L^{1-r}+\frac{L}{p}.                                      \tag{1}
$$
The second parameter is a physical torus translation. For a closed alternating walk expand the trace into its $2r$ brackets $\det(A^iv,CA^jv)$, where $v$ is one fixed lift of $x$. Rescaling a lift of any projective site multiplies the row or column by a sign. Every occurrence as a row or column index meets two edges in the walk, so these signs cancel, also when labels happen to agree.

Use the two-dimensional rational algebra $V=\mathbb F_p\times\mathbb F_p$ or $\mathbb F_{p^2}$. Both parameter planes are projective lines of multiplication matrices. The bracket product $F$ is an actual section over $\mathbb F_p$ of $\mathcal O(2a,2r)$ on $S=\mathbf P(V)\times\mathbf P(V)$, where $a$ is the sum of the $r$ row and $r$ column exponents counting their appearances in the vertex sequences. Thus the equation $w^2=F$ in the line bundle $\mathcal O(a,r)$ defines the desired double cover over $\mathbb F_p$. At any rational parameter, the number of points in its fiber is exactly $1+\chi(F)$ in any rational trivialization. This fixes the arithmetic twist, including its sign.

Over the algebraic closure, let $a_1,a_2$ and $c_1,c_2$ be the two eigenvalue forms in the first and second parameter, and set $t=a_1/a_2$, $y=c_1/c_2$. The two components of $v$ are nonzero. Each bracket has the form
$$
 K a_2^{i+j}c_2\,t^j(t^{i-j}-y)
$$
with the same nonzero constant $K$. Around the walk $K$, $a_2$ and $c_2$ occur to even total powers, and $\sum_{\rm edges}j$ is even as well. Hence the geometric square class is the product of $y-t^d$ over the distinct **signed** gaps $d=i-j$ of odd multiplicity. There are an even number of them. In particular, negative gaps and zero gaps are allowed. The canceled powers may still have zeros, which will be included when comparing point counts. In the nonsplit case Galois exchanges the two eigenlines, acting on both eigenratio coordinates by simultaneous inversion; the graphs $y=t^d$ and the pair of boundary fibers $t=0,\infty$ are stable in this description. The arithmetic model throughout is the bracket cover just defined. [Single-parameter factorization and trace expansion](paley-torus-generators.md#the-character-polynomial-in-the-generator)

If every signed gap occurs evenly, pair the $2r$ edge positions by their common gaps. The starting row has $L$ choices. For each pair there are at most $L$ choices for its first next vertex and at most one for its second, since the current vertex, its side, and the signed gap determine the next exponent. There are at most $(2r-1)!!L^{r+1}$ such walks, each contributing at most $m^2$ to the sum. For every other walk we show $|\sum_{A,C\in T}\chi(F)|\ll_r Lp$. There are at most $L^{2r}$ walks in all, which proves (1).

## A surface estimate for the nonpaired walks

Write $D$ for the set of odd-multiplicity gaps and $k=|D|$, so $2\le k\le2r$. The double cover is geometrically integral: on its generic $t$-fiber it has $k$ distinct simple branch points. On $S_{\overline{\mathbb F}_p}$ the horizontal branch curves are the rational sections $y=t^d$ for $d\in D$. Additional geometric branching before resolution is possible on the two vertical boundary fibers because a negative exponent has a pole. There is no horizontal component at $y=\infty$, since $k$ is even. We give a resolution requiring $B=O_r(L)$ geometric point blowups.

* At $t=0$, blow up above $y=0$ along the chain with charts $y=t^j u$, $1\le j\le\max(0,\max D)$, and above $y=\infty$ along the corresponding chain for $1/y$ and the negative gaps. A section with gap $j>0$ meets the $j$th component at $u=1$; sections of larger positive gap pass to the next center at $u=0$. There is one section per signed gap. The section of gap zero, when present, meets the original fiber at $y=1$. Make the same construction at $t=\infty$ in the parameter $1/t$. These are at most $4L$ blowups altogether. Every component in either resulting vertical chain has at most two vertical neighbors and one horizontal section, at distinct points.
* For $t\ne0,\infty$, two sections of different gaps meet only if $t^{d-e}=1$. Their slopes differ there, since $0<|d-e|<2L<p$. A single blowup separates all sections through any such point. There are at most $\sum_{\{d,e\}\subset D}|d-e|=O_r(L)$ centers. After these blowups, the horizontal sections are disjoint. The branch divisor after dropping even components consists of some of the smooth rational sections and vertical components, with only transverse double crossings. Away from the two boundary fibers the original vertical fiber is unbranched and a new exceptional line meets at most $k$ sections.
* Blow up each crossing of two odd branch components. The new exceptional multiplicity is even, so it is unbranched. There are $O_r(L)$ such crossings by the incidence counts above. On the resulting rational surface $S'$ the reduced odd branch divisor $R$ is smooth, disjoint, and has $O_r(L)$ rational geometric components. At every step, subtract twice the integer part of each half-multiplicity from the pulled-back branch divisor and adjust the covering line bundle accordingly. This normalization preserves the quadratic function-field extension.

The collection of centers at each stage is Galois-stable. In particular the two chains at the conjugate boundary fibers in the nonsplit case are taken together, and all other multiple points and branch crossings are treated simultaneously. The blowups and normalized cover $\pi:X\to S'$ therefore descend to $\mathbb F_p$. Equivalently take the normalization in the original bracket extension after the indicated blowups. In odd characteristic a double cover branched along a disjoint union of smooth divisors is smooth, as can also be seen locally from $w^2=u$ at a branch point. [Pardini, *Abelian covers of algebraic varieties*](https://doi.org/10.1515/crll.1991.417.191)

We prove $b_1(X)=b_3(X)=0$ over the algebraic closure. Every component in the fiber above $t=0$ is rational. A branch component lifts isomorphically on its reduced preimage. An unbranched original vertical component meets at most three possible branch points by the chain description. A separable double cover of a projective line has an even number of simple branch points, so here there are at most two, and every component upstairs is rational by Riemann–Hurwitz. The final exceptional lines above branch crossings each meet two branch components. This accounts for the whole fiber.

The Albanese morphism contracts every rational curve. The pullback of an ample class on the Albanese thus has degree zero on the entire fiber over $0$, counting multiplicities. All fibers are linearly equivalent, so every smooth fiber also has degree zero and is contracted. Each such fiber is geometrically connected, since it is branched at the distinct points $t^d$. The ramification curve over any one horizontal branch section is itself rational and maps isomorphically to the base parameter line. It meets all these fibers. Its constant Albanese image is therefore the image of a dense open of $X$, proving the Albanese trivial. The first étale Betti number equals twice the dimension of the Albanese, and duality gives $b_3=b_1$. [Positive-characteristic surface invariants, §§3.2–3.4](https://arxiv.org/abs/0912.4291)

For the remaining Betti number, write $R\sim2M$. The local double-cover equation gives $\pi_*\mathcal O_X=\mathcal O_{S'}\oplus\mathcal O_{S'}(-M)$ and $K_X=\pi^*(K_{S'}+M)$. Surface Riemann–Roch and Noether's formula then yield
$$
 \deg c_2(X)=2\deg c_2(S')+R\cdot(R+K_{S'})
             =2(4+B)-2\,\#\{\text{geometric components of }R\}.
$$
The last step uses adjunction on each disjoint rational component. The étale Euler characteristic is $\deg c_2(X)$, so $b_2(X)=O_r(L)$. Grothendieck's trace formula and the Weil bounds for smooth projective varieties give $|\#X(\mathbb F_p)-(1+p^2)|\le b_2(X)p$. [Surface Riemann–Roch and étale Euler characteristic](https://arxiv.org/abs/0912.4291) · [Deligne, *La conjecture de Weil I*, §§1–2](https://www.jmilne.org/math/Documents/DeligneWeilI.pdf)

For the comparison with the sum, discard the exceptional and boundary curves on $S'$, and the graphs of all the at most $2r$ original distinct gaps. These cost $O_r(Lp)$ rational points on the base and at most twice as many upstairs. Each graph is defined over $\mathbb F_p$ as the graph of the torus power map on its projective compactification. Exceptional curves from a rational center have $p+1$ points before further blowups, and those above a nonrational center have none. On the remaining open the arithmetic double cover agrees with the bracket equation, so its fiber count is $1+\chi(F)$. Also $\#S'(\mathbb F_p)=(p+1)^2+O_r(Lp)$. Restoring all parameters of $T^2$ changes the sum by $O_r(Lp)$. These estimates prove the claimed character bound, retaining the possible nonsplit arithmetic twist.

## Sliding windows and every relative start

For a generator $g$, write $P^H_{g,c_0}$ for the two length-$H$ arcs at relative start $c_0$. Cover each exponent interval $[0,H)$ by all $L$-windows with integer starts in $[-L+1,H-1]$, a set of size $s=H+L-1$. Every target integer has exactly $L$ representations as a window start plus an index in $[0,L)$. Form the matrix of all labeled windows. The isometric embedding of a vector on $[0,H)$ copies each entry into its $L$ representations with scale $1/\sqrt L$ and puts zero on the other labels. Compressing both sides then gives $L P^H_{g,c_0}$. This uses integer representations even when the physical sites wrap around the torus, with consistent homogeneous lifts of each physical site.

The squared norm of a block matrix is bounded by the sum of squared block norms, by Cauchy–Schwarz. For starts $a,b$ the block has the norm of $P_{g,c_0g^{b-a}}$ by simultaneous translation. Jensen's inequality and $s<2H\le2m$ now give
$$
 \sup_{c_0\in T}\left(\frac{\|P^H_{g,c_0}\|}{H}\right)^{2r}
 \le \frac{2^{2r+1}}H\sum_{c\in T}
             \frac{\operatorname{tr}((P_{g,c}P_{g,c}^*)^r)}{L^{2r}}.       \tag{2}
$$
Indeed Jensen first gives $(s/H)^{2r}$ times the mean over the $s^2$ block pairs of $(\|P_{g,c_0g^{b-a}}\|/L)^{2r}$. At each fixed $a$, at most two $b$ give any one relative element since $g$ is a generator. This bound is uniform even at $H=m$.

Choose $L=\lfloor\sqrt H\rfloor$, so $2L<p$ for sufficiently large $p$. All the traces in (2) are nonnegative, and (1) includes nongenerators. Dividing the summed bound by $\varphi(m)$ gives
$$
 \mathbb E_{g\text{ generator}}\sup_{c_0}
     (\|P^H_{g,c_0}\|/H)^{2r}
 \ll_r p^{o(1)}\left(pH^{-(r+1)/2}+H^{-1/2}\right),
$$
using $m/\varphi(m)=p^{o(1)}$. For $r\epsilon\ge2$ and $H\ge p^\epsilon$ this is $O_r(p^{-\epsilon/2+o(1)})$. Apply Markov's inequality at the dyadic ceilings of the desired lengths, using $m$ itself as the ceiling when a power of two exceeds $m$. There are $O(\log p)$ tests and the selected ceiling is always at most $2H$. Compress the matrices from each passing test to the shorter intervals. This proves the simultaneous assertion.

The geometric estimate is a proof in classical algebraic geometry. The finite control enumerates the actual matrices and two-parameter character sums over small prime fields and tests the window multiplicities, including a full wrapped orbit. [Finite control](../../../scripts/probes/probe_paley_torus_uniform_arcs.py)

```sh
python3 -B scripts/probes/probe_paley_torus_uniform_arcs.py
```
