# A uniform exact three-head threshold on arbitrary evaluation domains

Let $16\mid n$, $n\ge2^{30}$, $p>3n^2$, and let $\mathbb F$ be any finite field of characteristic $p$. Use any injective domain of $n$ evaluation points and dimension $2\le k\le n/16$. Set
\[
 d=n/16-1,\quad t_0=\lfloor n/3\rfloor-1,\quad
 e_{\min}=\lfloor2(n-k)/3\rfloor+1,\quad e_{\max}=n-t_0.
\]
For every $e_{\min}\le e\le e_{\max}$ the exact worst-case two-row MCA numerator is **$3(e+1)$**. For every integer budget
\[
 3e_{\min}\le B\le3(e_{\max}+1)+2
\]
the first failing Hamming error count is $\lfloor B/3\rfloor$, and the operational real threshold is $\lfloor B/3\rfloor/n$. In particular one may take $B=\lfloor|\mathbb F|/2^{128}\rfloor$. At rate $1/16$ the lower budget endpoint is $15n/8+3$. According to $n\bmod3=0,1,2$, the upper endpoints are $2n+8$, $2n+9$, $2n+10$, respectively. This is a written extension of the [terminal cubic proof](second-prime-terminal-cubic.md). The bounds below identify which estimates are uniform as $n$ increases.

## The dimension range at the production length

Let $n=2^{30}$ and let $q$ be the size of a finite field of characteristic
above $1{,}744{,}830{,}589$. Set $B=\lfloor q/2^{128}\rfloor$ and
$j=\lfloor B/3\rfloor$. For $2{,}013{,}265{,}923\le B\le2{,}147{,}483{,}648$, every injective
domain of length $n$ over the field has first failing count $j$ at each
positive interleaving width and each message dimension $k$ satisfying
\[
  \max\!\left(2,\left\lceil\frac{2n-3j}{2}\right\rceil\right)
       \le k\le 2^{26}.
\]
The good real radii are exactly $0\le\delta<j/n$. The sufficient lower
dimension decreases from $67{,}108{,}863$ at the first budget to $2$ at
the last. This covers $4{,}503{,}599{,}694{,}479{,}355$ integer
budget–dimension pairs. Prime fields in the displayed budget range automatically meet the characteristic bound. [Simultaneous dimension and budget theorem](../../../ArkLib/Research/ProximityGap/Frontier/DimensionThreeHeadWindow.lean)

To see the bound, set $t=n-j$. At $k\ge3$ the three-head construction
requires $3(t-k)\le n-k$, equivalently $3t\le n+2k$. For $k=2$ the
affine construction requires $3(t-1)\le n$, which follows from the
same dimension condition because $n\equiv1\pmod 3$. Averaged projection
then puts more than $B$ bad scalars at $j$. At $j-1$, dimension
monotonicity transfers the known safe bound from $2^{26}$ to every
smaller positive dimension. The same argument gives exact worst error
$3(e+1)/|\mathbb F|$ for $671{,}088{,}640\le e\le715{,}827{,}881$ if
$3(n-e)\le n+2k$, the characteristic exceeds $1{,}744{,}830{,}589$,
and $\binom{3(e+1)}2\le |\mathbb F|$.

Dimension one stays safe farther. A bad scalar at $t=n-e$ agreements
determines at least $t-1$ unordered pairs of sites, and each such pair
determines a unique scalar. Hence $\binom n2<(B+1)(n-e-1)$ suffices for
security. This gives safety through
$e=n-2-\lfloor\binom n2/(B+1)\rfloor$, ranging from $787{,}410{,}670$ at
the smallest budget to $805{,}306{,}367$ at the largest. [Circuit incidence
bound](../../../ArkLib/Research/ProximityGap/Frontier/CircuitDensity.lean)

## Reducing the upper count to a large cubic

Prove the upper bound for all $5n/8\le e\le e_{\max}$ by selecting $3(e+1)+1$ alleged MCA-bad labels with one degree-at-most-$(k-1)$ witness each. They all have at least $n-e\ge t_0$ agreements. The first-order monomial support $0\le j\le4$, $0\le i\le34-j$, $0\le a<t_0-jd$ gives $165t_0-320d-35n=55(3t_0-n)+320\ge45$ more coefficients than received-line conditions. Thus a nonzero interpolant $Q$ of total $(Z,Y)$-degree at most 34 and value degree at most four contains every selected point $(z,q_z)$ over $\overline{\mathbb F}(X)$.

The [linear and quadratic component proofs](second-prime-terminal-reduction.md#factors-and-populations) give the same caps 184 for a nonlinear factor of $Y$-degree one, and 4128 for an irreducible quadratic. The only length-dependent lower checks in those proofs are $52(185t_0-34n)>151^2 d$ and $(2014-102)(2d+1-\lceil70n/2048\rceil)>2014d$. Both follow already using $t_0\ge n/3-2$ and $\lceil70n/2048\rceil\le70n/2048+1$. The squarefree calculations use degrees below $p$. Each actual affine head has at most $e+1$ labels by the fresh-site count. If all factors have value degree at most two, at least three heads must carry more than 512 labels since $2(e+1)+4\cdot4128+34<3(e+1)+1$. Each such head has core at least
\[
 z=n-e-\lfloor e/512\rfloor \ >331n/1000.
\]
This follows from $e\le n-t_0$. Three noncollinear large heads cover all selected points: the determinant of their three head pairs bounds the core union below by $3z-2d$ and an outside point agrees at most $n-3z+5d<t_0$ times. The three heads supply at most $3(e+1)$ labels. If the $j=3$ or $4$ large heads are collinear, their fresh-site count, allowing exceptions for all other factors, is at most
\[
 jn-(j-1)\bigl(jz-\tbinom j2d\bigr)+4\cdot4128+34
   <15n/8+1 .
\]
The proof is the evaluation-site count in the [terminal reduction](second-prime-exact-threshold.md#an-upper-bound-for-every-received-pair). Thus there must be a cubic or quartic irreducible factor.

A quartic factor carries at least $M_4=15n/8-34$ points, since all other factors have value degree zero. A cubic factor carries at least $M_3=5n/4-34$, since at most one unit of value degree and at most $e+1$ points lie in other positive-value-degree factors. These lower bounds allow 34 labels from all factors independent of $Y$.

## Weight and multiplicity estimates

Write $D(h,v)=\sum_{j=0}^h(h-j+1)\max(v-jd,0)$, and let $W$ be the component's weight for $(X,Z,Y)$ of weights $(1,0,d)$. For $b=4$, take $h=119$; for $b=3$, take $h=2^{25}$. In both cases $34h<M_b$. Every degree-$h$, weight-below-$t_0$ interpolant on the received lines is an integral multiple of the component. The dimension lower bound and the quotient capacity give
\[
 D(h,t_0)-(h+1)n\le D(h-b,t_0-W).
\]
Since $5d<t_0<6d$, $D(h,t_0)=(6h-9)t_0-(15h-40)d$. If $W\ge w_b n$, with $w_4=283/1000$ and $w_3=271/1000$, one has $t_0-w_b n<d$. The right side is then at most $(h-b+1)\max(t_0-w_b n,0)$. This contradicts the lower bound for either $b$, as checked by substituting $t_0\ge n/3-2$ into the difference (the coefficient of $t_0$ after subtraction is positive). Thus $W<w_b n$.

Use $\mu=64$, $s=400000000$ for both component degrees, and put $\eta=\lceil n/90\rceil$. Let $R$ denote the sum of the received-line local orders of $F$. In the quartic case the [second scalar derivative calculation](second-prime-quartic-intrinsic.md#multiplicities-over-the-scalar-function-field) gives $7R\le6n+22W-48d$, hence $R<1319n/1000$. Its identically-zero alternative allows only four labels. In the cubic case the [generic polar and normalized Hessian estimate](second-prime-persistent-singularities.md#local-charges-for-the-two-derivatives) gives
\[
 5R\le2n+47W-78d-8g_{\rm pol}.
\]
The identically-zero case allows only three labels. If $g_{\rm pol}\ge3(W-d)-\eta$, the displayed bound gives $5R\le2n+23W-54d+8\eta$, hence $R<99n/100$. All degrees used to split the finitely many coordinate centers and all bounded inverse-derivative heights in these results are below $p$.

In both cases the [polynomial-multiplier jet interpolation](second-prime-intrinsic-cubic.md#imposing-polynomial-jet-membership) applies. Its variable count exceeds its net cost because
\[
 (s-b+2)\left(b\mu t_0-\tbinom b2d\right)
   >(s+1)\mu R+34 n\tbinom{\mu+1}{2}.
\]
Indeed the inequality holds with $t_0=n/3-2$, $d=n/16$ on the left, and the preceding linear bound for $R$ on the right. The resulting nonzero value-degree-below-$b$ polynomial gives a scalar resultant of degree at most $bs+(b-1)(34-b)<M_b$. This eliminates the quartic and the high-polar cubic.

## The low-polar cubic

It remains to consider $g_{\rm pol}<3J-\eta$, $J=W-d$. Use the [polynomial matrix for powers of the Jacobian ideal](second-prime-terminal-cubic.md#a-finite-polynomial-matrix-for-powers-of-the-jacobian-ideal). Take $a=40$ and the same $s=400000000$. The generic polar resultant has degree $D=6W-9d-3$ in $X$ after the common coordinate change and degree $H_p\le6\cdot34-9=195$ in $Z$. The polynomial matrix in that proof has ambient dimension
\[
 N=(3a+3)a(D+W)\le(3a+3)a(7\cdot271n/1000-9n/16+6).
\]
Its column span has codimension at most $a g_{\rm pol}$. The construction gives a nonzero polynomial of $Y$-degree below three and weight below $aJ$ whenever
\[
 (s+1)(3aJ-3d-a g_{\rm pol})>aH_p N.
\]
This inequality follows by replacing the left side by $(s+1)n(a/90-3/16)$ and the right side by $195a$ times the displayed upper bound on $N$. The difference is affine in $n$, with positive slope and positive value at $2^{30}$. Evaluation of the constructed polynomial on each simple polynomial section is divisible by $F_Y(X,z,q_z)^a$ of degree exactly $aJ$ after the common coordinate change. Thus it vanishes there identically. At most $34\cdot33$ labels are lost for nonsimple sections; the nonzero resultant has scalar degree at most $3s+68<M_3-34\cdot33$. This proves the upper bound throughout the stated window.

## Three heads attaining the upper bound

For $e_{\min}\le e\le e_{\max}+1$ put $t=n-e$,
\[
 h=\max\{0,\lceil(3(t-1)-n)/2\rceil\},\qquad r=t-1-h.
\]
The inequality $h\le k-2$ follows from $3e\ge2(n-k)+1$. Also $r\ge0$ and $3r\le n-h$. Choose $h$ common sites, three disjoint private sets of $r$ sites each, and $\ell=n-h-3r$ extra sites. In this window $\ell\le11$. Let $H$ be the locator polynomial of the common sites. Use the three head pairs
\[
 H(X)(0,0),\qquad H(X)(X,1),\qquad H(X)(2X+c,3).
\]
Both entries have degree at most $h+1<k$. Receive zero on the common sites and the corresponding head on each private set. A site $x$ private to $j$ gives a fresh agreement with each other head $i$ at a scalar of one of the three forms $-x,-(2x+c)/3,-(x+c)/2$. Each type occurs on $2r$ sites and is injective for fixed $c$. Between types the coefficients of $c$ are different. Thus at most $3(2r)^2\le4n^2/3$ forbidden $c$ produce any intertype collision. Choose another $c$ in $\mathbb F$.

At each extra site choose the received pair as $H(x)(U,V)$ with $V\notin\{0,1,3\}$. The three scalars for its agreements with the three heads are affine nonconstant functions of $U$ with distinct slopes. At most three $U$ values cause pairwise coincidences. At most $3(6r+3\ell)$ more can hit earlier labels. There are fewer forbidden $U$ than $|\mathbb F|>3n^2$, so choose $U$ successively. For each resulting fresh label, use its head's $t-1$ defining sites and the fresh site. The defining sites determine both code polynomials uniquely since $t-1\ge k$. The fresh row-pair differs from this head there, while the fold agrees. This is a literal MCA-bad support of size $t$. The labels are distinct and number
\[
 6r+3\ell=3(e+1).
\]
Combining this attack with the upper bound gives the asserted equality on integer errors. At $e^*=\lfloor B/3\rfloor$, $3(e^*+1)>B$, whereas $3e^*\le B$ at its predecessor. When $e^*=e_{\min}$ the upper proof still covers $e_{\min}-1\ge5n/8$. When $e^*=e_{\max}+1$ only the attack is needed at that final step. The monotonicity of the literal MCA error and constancy between consecutive Hamming steps give the real threshold in the statement. [Uniform arithmetic certificate](../../../scripts/probes/probe_uniform_three_head_threshold.py)

At rate $1/16$ a three-seam attack also determines the preceding budget interval, throughout which the first failing radius is $5/8$. [Preceding plateau](rate-sixteenth-three-head-plateau.md)
