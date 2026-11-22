# Tangent determinants and three second-prime safety bounds

At the second designated prime and length $n=2^{30}$, the first failing MCA error count on any injective domain and at any positive width has the following lower bounds. Independent kernel replay accepted 10,509 declarations for the determinant theorem on actual rational coordinates and 16,603 for the six interpolants and finite allocations. The normalization, tame differentiation and plane-curve duality steps are written mathematics. [Tangent heights and exceptional incidences](logarithmic-section-heights.md) · [Lean interpolants and prices](../../../ArkLib/Research/ProximityGap/Frontier/TangentPolarWindows.lean) · [Integer calculation](../../../scripts/probes/probe_tangent_polar_windows.py)

| Rate | Safe through | First failure at least | Maximum number of bad labels in the proof |
|---|---:|---:|---:|
| $1/2$ | 309,800,000 | **309,800,001** | 2,110,558,412 |
| $1/4$ | 529,350,000 | **529,350,001** | 2,141,997,998 |
| $1/8$ | 671,088,639 | **671,088,640** | 2,128,274,755 |

The determinant argument also applies to a supplied nonlinear component past Johnson. At rate $1/8$ and **696,254,464 errors**, an irreducible nonlinear component of total scalar/value degree at most 25 and coordinate weight at most 754,974,719 supports at most **140,161** selected labels. This is 2,137,701 steps beyond the first integer above Johnson. The assertion concerns witnesses on that component. At this radius the full MCA event already admits attacks using affine heads. [Eighth-rate attack](eighth-transverse-mobius.md)

Using two interpolants after greedy affine-head removal raises the half-rate lower bound to **310,285,001**. [Residual surfaces and the fixed-row triangle count](half-core-weighted-jets.md)

## A determinant bound for the tangents

Use the notation of the logarithmic height argument. Write $b\ge2$ for the value degree of a primitive irreducible component, $m$ for its actual total scalar/value degree, $W$ for its coordinate weight and $d$ for the maximum witness degree. Of its labels, at most $G+2bm$ are put aside, where $G=(2b-2)m-b(b-1)$. Each retained label supplies a rational tangent $(R_i,V_i)$ over the coordinate function field with $R_i=q_i-z_iV_i$. After a common change of coordinate, its denominator has degree $c_i$ and both numerators have degree at most $d+c_i$. On at least $t-\ell_i$ sites the denominator is a unit and $(R_i,V_i)$ evaluates to the received pair. We have
$$\sum_i c_i\le C_0=2AG+2Wm,\quad A=(2b-2)W-b(b-1)d,\qquad
\sum_i\ell_i\le R=(G+m)n.$$
These two estimates hold independently of the position of $t$ relative to Johnson. They use characteristic zero or characteristic greater than $\max(A,b)$. The polar step below additionally requires characteristic zero or characteristic greater than $m(m-1)$.

Fix a positive integer $s$ and $1\le a\le s$. Use the $h=\binom{s+2}{2}$ monomials in two affine variables of total degree at most $s$. Their degrees sum to $E=s(s+1)(s+2)/3$. Evaluate them at $h$ retained rational tangent pairs, multiplying row $i$ by its denominator to the power $s$. Every determinant term has degree at most $Ed+s\sum c_i$. At a site with $r_x$ good rows, translate the two affine variables by the received pair. Binomial expansion gives a triangular change of columns with diagonal one, including for rows originally written with different denominators. In every good row a translated column of degree $j$ vanishes to order at least $j$. Each determinant term uses distinct columns. Their total degree in the good rows is at least $ar_x-\binom{a+2}{3}$ since across the full basis the total of the shortfalls $(a-j)_+$ is $\binom{a+2}{3}$. Summing these orders over the injective sites, a nonzero determinant requires
$$D=ah t-\binom{a+2}{3}n-Ed\ \le\ \sum_i(a\ell_i+sc_i).$$
The row translation, local determinant divisibility and global degree comparison have Lean statements. [Tangent evaluation matrices](../../../ArkLib/Research/ProximityGap/Frontier/TangentVeronesePacking.lean)

When $D>0$, discard the rows for which $h(a\ell_i+sc_i)\ge D$. There are at most $\lfloor h(aR+sC_0)/D\rfloor$. Every $h$-row evaluation minor of the remaining rows vanishes. Linear algebra therefore puts their tangent pairs on a single plane curve of degree at most $s$, also if fewer than $h$ rows remain.

## Which curves can contain the tangents?

Work over an algebraic closure of the coordinate function field. A retained rational smooth point guarantees geometric irreducibility of the original irreducible plane component over that field extension. Indeed its geometric components are conjugate, and two through the same smooth rational point are impossible. Geometric nonreducedness would preclude a smooth point. The projective Gauss map sends a smooth primal point to its tangent line, represented by the three homogeneous first derivatives. Its affine tangent coordinates here are $(R_i,V_i)$.

For a nonlinear plane curve of degree $m$, any nonconstant Gauss map has degree at most $m(m-1)$ by cutting its image with a general line and applying Bézout to the corresponding polar. A constant projective tangent would contain every smooth point and force a line. The characteristic hypothesis makes the Gauss map separable. Plane-curve reflexivity then identifies the primal curve as the dual of its image. In particular if the dual image has degree at most $s$, the primal degree is at most $s(s-1)$ by the same polar intersection bound (a dual line would have a point as its dual). [Pardini, Proposition 1.2](https://numdam.org/item/CM_1986__60_1_3_0.pdf)

If $m>s(s-1)$, the polynomial of degree at most $s$ obtained from the minors cannot vanish on the entire dual curve. Substituting the primal gradient gives a polynomial of degree at most $s(m-1)$ which is coprime to the primal equation. Bézout bounds the remaining distinct selected primal points by $sm(m-1)$, even if several points have the same tangent. Thus
$$M\le G+2bm+sm(m-1)+\left\lfloor\frac{h(aR+sC_0)}D\right\rfloor.$$
When the actual $m$ might be smaller than $s(s-1)$, price that range separately with the original tangent count evaluated at $\min(m_{\max},s(s-1))$. Each degree or weight used on the right is an upper bound in its indicated range. When both the ordinary tangent and polar estimates apply, use the smaller one.

## A component calculation beyond Johnson

Take $t=45n/128=377487360$, $d=n/8-1$ and $W\le2t-1$. Then $t^2<nd$ but with $s=2,a=1$ the determinant gap is $6t-n-8d>0$. For actual $m\ge3$ the dual curve has degree above two. The possible $b=2,3,4,5$ (since $bd\le W$) have caps **21,387, 54,370, 96,663 and 140,161**, using $m\le25$.

For $m=b=2$ the dual of the smooth geometric conic is a conic in the designated characteristic. Modulo its equation take the constant, both linear and two of the three quadratic monomials as a basis. Their five degrees sum to six. For $r_x$ good rows of the resulting five-column determinant, its order is at least $r_x-1$. Indeed, in the local ring at the site the good denominators are units. Scale each good row to have constant entry one and subtract one such row from the others. Each of the $r_x-1$ differences is divisible by the site parameter in every column. Thus the gap is now $5t-n-6d=n/128+6>0$. A linear combination of the five columns gives a polynomial independent of the conic equation. Substitution of the primal gradient allows at most four cheap labels by Bézout. The cap in this case is **12,093**. No assumption on character-sum cancellation enters this component estimate.

## From components to all received pairs

For each rate use two mixed Hasse interpolation surfaces. Their shapes $(r,v,s_0)$ record vanishing multiplicity, maximum value degree and total scalar/value degree. The row bounds use identities in the scalar variable at each evaluation site. Every selected witness is contained by both surfaces because each agreement contributes multiplicity $r$ to the specialized coordinate polynomial of degree below $rt$. [Jet interpolation and factor allocation](weighted-hodge-windows.md#joint-allocation-among-linear-and-nonlinear-factors)

| Rate | Primary shape | Companion shape | Two surpluses | Head cutoff $L$ | Polar parameters $(s,a)$ |
|---|---|---|---|---:|---|
| $1/2$ | $(23,32,85457)$ | $(46,65,1093)$ | 2,875,632 and 3,249,617,445 | 5,589,682 | $(8,7)$ |
| $1/4$ | $(18,35,27103)$ | $(34,68,896)$ | 25,116,738 and 3,313,809,932 | 2,067,774 | $(7,5)$ |
| $1/8$ | $(6,16,335)$ | $(9,26,128)$ | 77,656 and 805,373,634 | 81,920 | $(4,2)$ |

Assign one witness at each scalar to a factor of the primary surface. All its value-independent factors together cost at most its total degree $s_0$ in distinct labels. Each factor above $L$ divides both surfaces by the scalar degree of the value resultant. The identity-site test shows that a value-linear factor above $L$ is an actual affine head. Each such head has joint core at least $c=t-\lfloor e/L\rfloor$. With $j$ large heads and total assigned positive value degree $f$, a common factor of value degree $b$ has $W\le rt-1-(f-b)d$ and $m\le s_0'-j$ using the companion's total degree. A factor certified only up to $L$ costs $L$.

At the first two rates $3c>n+2d$, so every three or more large heads are collinear. For $j$ collinear heads the core union has size at least $\lceil jc^2/(c+(j-1)d)\rceil$. Each covered site supplies at most one distinct fresh label, and each uncovered site at most $j$. The additional per-head bound $e+1$ holds at all rates.

At eighth rate use the published four-head cap **2,125,114,027** at 671,088,639 errors, including the exceptional noncollinear profile of deficits $(1,1,1,5)$. Its proof uses the constant projective involution pairing opposite directions in a saturated quartet. Among five large heads there are four collinear. With a transverse fifth head these five carry at most **2,058,021,547** at the stated agreement. Six or more large heads are all collinear by the five-plus-one incidence exclusion. The endpoint at this rate was previously established with 2,145,721,437 labels. The tangent-polar prices increase the resulting gap below budget from 1,762,211 to **19,208,893**. [Four-head bound](eighth-rich-head-safety.md#four-rich-heads-off-a-single-line) · [Six-head incidence](../../../ArkLib/Research/ProximityGap/Frontier/EighthCollinearOutlier.lean) · [Four plus one](eighth-four-plus-one.md)

For the remaining $f-j$ units of value degree, a bound $p_b$ on a degree-$b$ part gives at most $(f-j)\max_b(p_b/b)$ labels for any partition. Adding the bound for $j$ heads and the full $s_0$ allowance gives the three maxima in the first table. Their maximizing $(j,f,b)$ are $(5,32,27)$, $(5,35,30)$ and $(4,16,12)$, respectively. All lie below $2n=2147483648$. Monotonicity in the error count and MCA interleaving invariance give the stated safety intervals.
