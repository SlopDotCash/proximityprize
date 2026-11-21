# Exact three-head window at rate one eighth

Let $16\mid n$, $n\ge2^{30}$, $k=n/8$ and $d=k-1$. Take any injective domain over any finite field of characteristic $p>3n^2$. Put
\[
 E=\lfloor7n/12\rfloor+1,\qquad
 t_0=\lfloor(n+5d+21)/4\rfloor+1,\qquad U=n-t_0 .
\]
The exact worst-case two-row MCA numerator is $3(e+1)$ for $E\le e\le U$. Every integer budget $3E\le B\le3(U+1)+2$ has first failing count $\lfloor B/3\rfloor$. At $n=2^{30}$ these error counts run from **626349398 through 637534203**, and the exact budget interval is **1879048194 through 1912602614**. The second designated prime, with budget $2n$, consequently has first failure at least **637534204** at this rate. The proof below is written mathematics with checked finite inequalities.

## Producing factors of small total degree

To establish the upper count, take $E-1\le e\le U$ and a family of $3(e+1)+1$ bad scalar labels with one polynomial witness per label. Write $t=n-e\ge t_0$, $L_x(Z)=u(x)+Zv(x)$ and work over the algebraic closure of the field. Every selected section has degree at most $d$. Use coordinate weight $\deg_X+d\deg_Y$ on monomials, and total degree in $(Z,Y)$.

Take a double interpolant of value degree at most six, total degree 74, and weight strictly below $2t_0$. Vanishing of the received-line jets of order below two costs at most $224n$ conditions. The coefficient surplus is $1008t_0-1484d-224n>0$, since $t_0\ge13n/32$. It contains every selected point over the coordinate function field. Independently, take a triple interpolant of value degree at most nine, total degree 27 and weight below $3t_0$. Its surplus is $705t_0-975d-164n>0$. Here the six Hasse jet restrictions at each site have $Z$-degrees bounded by $27-j$ for each $(i,j)$ of total order below three. A witness substitution maps $(X-x,Y-L_x(z))^r$ into $((X-x)^r)$ at every agreement, for $r=2,3$.

An irreducible factor $F$ of the first interpolant containing more than $74\cdot27$ selected points divides the second over the coordinate function field by plane Bézout. By taking primitive representatives over the coordinate polynomial ring, its total degree $m$ is then at most 27, and its weight $W$ still satisfies $bd\le W<2t_0<814n/1000$, where $b=\deg_YF$. The first interpolant has at most 74 vertical labels from all factors independent of $Y$. A value-linear factor other than a genuine affine secant carries at most 4095 selected labels, even without the degree-27 improvement. Indeed with 4096 witnesses its received identity set has $(4096-74)|I|\ge4096t_0-74n$. There are at most 73 misses per such site, and each of the 75 witnesses with fewest misses has at most $73|I|/(4096-74)$ misses. Every three share more than $d$ sites. Thus all 75 lie on a common secant and restriction forces that secant to divide the factor.

## Counting auxiliary polynomials modulo the component

We show that each irreducible factor of value degree $2\le b\le6$ has at most $bs+8500$ selected labels, where $s=70000000$. We may suppose $m\le27$ by the previous paragraph. The new dimension count permits the auxiliary polynomial to have value degree greater than $b$. Subtracting the space of all multiples of $F$ guarantees a nonzero restriction to $F$.

Write $S(v)=\sum_{j\ge0}\max(v-jd,0)$. For integers $v\ge W$ one has
\[
 S(v)-S(v-W)\ge (vW-W^2/2)/d .
\]
Indeed its piecewise-linear interpolation has derivative $\lceil x/d\rceil$ almost everywhere for $x>0$, which is at least $x/d$. Integrate from $v-W$ to $v$. For scalar degree at most $s$ and weight below $v$, the number of free polynomial coefficients modulo all permitted multiples of $F$ is at least $(s+1)(S(v)-S(v-W))$. For total $(Z,Y)$-degree at most $s$ it is at least $(s-j_{\max}+1)(S(v)-S(v-W))$ where $j_{\max}=\lfloor(v-1)/d\rfloor\le s$. These estimates follow by subtracting quotient spaces of weight below $v-W$, even allowing quotients the full scalar or total degree $s$. Gauss's lemma gives integral quotients. For the second bound, subtract the two weights termwise at each $j$ with the common coefficient $s-j+1$.

Use the common coordinate change of the [polar argument](second-prime-persistent-singularities.md#a-lower-bound-for-the-persistent-intersections), choosing the site at infinity away from all selected simple fibers' derivative roots and away from the generic value discriminant. Every simple polynomial section has $\deg_X F_Y(X,z,q_z)=J=W-d$ in this chart. The nonsimple sections number at most $(2b-1)m-b^2<400$ by the scalar degree bound for $\operatorname{Res}_Y(F,F_Y)$. Fractional coordinate change rescales each received affine pair by a common constant at each site and preserves its agreements and the weight. If the second implicit scalar derivative vanishes identically, its bounded-height inverse derivative argument splits $F$ into at most $b$ scalar-affine lines over the algebraic closure of the coordinate function field. Two selected points on one such line force it to be defined over the coordinate function field, contradicting irreducibility for $b\ge2$. The constants used in this elementary descent have scalar height at most $b(m+1)+bm<p$. [Inverse derivative argument](second-prime-quartic-intrinsic.md#multiplicities-over-the-scalar-function-field)

## Large polar count

Let $g$ be the generic polar gcd degree, or equivalently the sum of the branchwise minimum valuations of the two homogeneous affine partials over finite $X$. Let $R=\sum_x r_x$ be the sum of the plane local multiplicities of $F$ at the received ordinates over all sites. The normalized Hessian argument gives
\[
 5R\le 2n+(18b-7)W-(9b^2-b)d-8g . \tag{1}
\]
Here is the extension of the [local proof](second-prime-persistent-singularities.md#local-charges-for-the-two-derivatives) to value degrees four through six. The normalized resultant has degree at most $(6b-3)W-(3b^2-b)d$, after subtracting the universal contribution of the value-leading coefficient. This is the weighted Sylvester sum and the reciprocal-value identity $V^{3b-2}N_F(1/V)\equiv V(2S_Z^2S_V+VN_S)\pmod{S}$ up to sign, where $V=1/Y$, $S=V^bF(1/V)$, and $N$ is the implicit second derivative numerator. On a finite branch let $\nu$ be the generic polar order, $e_P$ its ramification index over $X$, and $\sigma$ its plane branch multiplicity. At a singular branch $\nu\ge \sigma(r-1)$ for total point multiplicity $r$. If $\sigma=r=2$ and the branch has $\sigma=2$, the doubled tangent shows $\nu\ge3$. If $e_P=\sigma\ge2$, subtract the constant term and the term of order $e_P$ from the local series of $Y$ over $X=\alpha+u^{e_P}$. Its second scalar derivative has order at least $1-e_P$. Since $\nu\ge3(e_P-1)$, $N=-F_Y^3Y''$ has order at least $8\nu/3$. For $e_P>\sigma$, the proof gives order at least $3\nu+e_P-2\sigma$. When $\sigma=1$ the correction is nonnegative. When $\sigma=2$ it is at least $-1$ with $\nu\ge3$. For $\sigma\ge3$ it is at least $1-\sigma\ge-\nu/3$. At $e_P=1$ the local regular series has regular second derivative. At fixed received branches, differentiation preserves order and the received ordinate has second derivative zero, giving the stronger charge $3\nu+\sigma$. Summing the surplus over each received point bounds it below by $(5r_x-2)/3$, also valid when $r_x=0$. In the reciprocal-value chart the remaining normalized charge is at least $8\nu/3-2f/3$, where $f=\operatorname{ord}V$; this calculation is independent of $b$ and $\sum f\le W-bd$. Combining the bounds gives (1). All local extension degrees are at most six and every relevant coordinate center has degree below $p$, so tame local parameters with separable constants suffice.

Set $a=16$ and $\eta=(W^2/(2d)+n)/a$. Suppose $g\ge JW/d-\eta$. In (1) this implies
\[
 5(t_0 W/d-R)\ge (8-4/a)W^2/d+(5t_0/d-18b-1)W
                   +(9b^2-b)d-(2+8/a)n.
\]
The quadratic is increasing on $W\ge bd$: its derivative there is at least $5t_0/d-(2+8/a)b-1\ge1/4$. Its value at $bd$ is $5bt_0-((1+4/a)b^2+2b)d-(2+8/a)n$. For each $2\le b\le6$ this exceeds $5n/12$, by $t_0\ge13n/32$, $d<n/8$. Thus $t_0W/d-R>n/12$.

Use the [polynomial jet multipliers](second-prime-intrinsic-cubic.md#imposing-polynomial-jet-membership), now with all value degrees and $\mu=64$, $v=\mu t_0$. Each received site costs at most $(s+1)\mu r_x +27\binom{\mu+1}{2}$ net scalar conditions. Counting the multiplier space and then subtracting the dimension of all $F$ multiples gives a polynomial coprime to $F$ if
\[
 (s-j_{\max}+1)\frac{vW-W^2/2}{d}>(s+1)\mu R+27n\binom{\mu+1}{2}.
\]
Here $j_{\max}\le210$, $R\le6n$ and $W^2/(2d)<27n/10$. The strict inequality follows since the surplus is at least
\[
 (s-209)(\mu/12-27/10)n-210\mu\cdot6n-27n\tbinom{\mu+1}{2}>0.
\]
Specializing the polynomial identities at each selected label gives $\mu$ roots per agreement and forces vanishing on its polynomial section. The nonzero scalar resultant has degree at most $bs+27\cdot210<bs+8500$.

## Small polar count

Suppose $g<JW/d-\eta$. Use the [finite polynomial matrix for Jacobian powers](second-prime-terminal-cubic.md#a-finite-polynomial-matrix-for-powers-of-the-jacobian-ideal) with value degree $b$ in place of three. The homogeneous polars have degree $b$ in the value coordinate. Put
\[
 D=2bW-b^2d-b,\quad H=2bm-b^2,\quad
 v'=\max(ba+b-1,\lceil aJ/d\rceil),\quad N=(v'+1)a(D+W).
\]
The generic polar resultant has exact coordinate degree $D$ after the coordinate change and scalar degree at most $H$. The columns in the cited construction are the degree-$v'$ multiples of $F$, of the products of $a$ homogeneous partials, and of the $a$th power of the polar resultant in $X$ for one fixed generic direction. Their entries have scalar degree at most $aH$. The proof reducing modulo that resultant applies because $v'\ge ba+b-1$: after choosing a value chart on each local factor, binary degree at least $b-1$ spans the resulting value algebra of length $b$. Thus the column codimension is at most $ag$, the sum of the generic polar valuations multiplied by $a$.

Allow every coefficient of every value degree of weight below $aJ$, with scalar degree at most $s$. This space embeds in the displayed matrix since $v'\ge aJ/d$ and its coordinate degrees are below $aJ<a(D+W)$. The polynomial-multiplier dimension argument costs at most $(s+1)ag+aHN$ scalar conditions. A nonmultiple of $F$ therefore exists if
\[
 (s+1)\bigl(S(aJ)-S(aJ-W)-ag\bigr)>aHN .
\]
Here $aJ\ge W$ since $b\ge2$. The parenthesized expression is greater than $a\eta-W^2/(2d)=n$. To bound the matrix dimension, use $v'\le\max(17b-1,90)$ and
\[
 D+W<(2b+1)(814n/1000)-b^2(n/8-1)-b .
\]
For each $b=2,\ldots,6$ one has $a(54b-b^2)N<(s+1)n$. Thus an auxiliary coprime to $F$ exists. Each simple section evaluates the auxiliary to a multiple of $F_Y(X,z,q_z)^a$, of degree $aJ$, while its own degree is strictly below $aJ$. The scalar resultant has degree at most $bs+27\cdot90$. Adding fewer than 400 nonsimple sections still leaves at most $bs+8500$ selected labels.

## Counting the remaining heads

Every nonhead positive-value-degree factor contributes at most $b(e/8+1)$ labels. Indeed $s+8500<e/8$ for the entire window and the nonlinear bounds have just been proved. Call an actual affine head large if its occupancy exceeds $e/8+1$. Its core has size at least $t-7$, since $(L-1)(t-c)\le e$ when $c<t$. Write $j$ for the number of large heads. If $j\le2$, the total is at most $j(e+1)+(6-j)(e/8+1)+74<3(e+1)+1$.

If three large heads are noncollinear, the determinant of their polynomial head pairs gives total core union at least $3(t-7)-2d$. An outside witness agrees at most $d$ times on each core, hence at most $n-3t+5d+21<t$ times overall. The three heads therefore already cover every label and hold at most $3(e+1)$. Otherwise the $3\le j\le6$ large heads are collinear over the coordinate function field. Their cores each have size at least $z=406n/1000<t_0-7$. If their union has size $V$, then
\[
 V\ge\max\left(jz-\tbinom j2d,\ \frac{(jz)^2}{jz+j(j-1)d}\right).
\]
The second inequality uses Cauchy–Schwarz on the site multiplicities, and the function $w^2/(w+j(j-1)d)$ increases with the summed core population $w$. A site inside the core union supplies at most one distinct fresh scalar to all these collinear heads, while an outside site supplies at most $j$. Including the remaining components, the total is at most
\[
 jn-(j-1)V+(6-j)(e/8+1)+74<7n/4\le3(e+1).
\]
The strict comparison holds for each $j=3,\ldots,6$, even using $d\le n/8$ and $e/8+1\le75n/1000$. This contradiction proves the upper bound.

The [common-locator three-head construction](uniform-three-head-threshold.md#three-heads-attaining-the-upper-bound) applies at every $E\le e\le U+1$ since $3e\ge2(n-k)+1$. In this interval the positive common locator gives zero or one extra site. It attains $3(e+1)$ on every domain. Comparing the predecessor and the attack proves the first-failure formula via Hamming-step constancy. [Uniform exact arithmetic](../../../scripts/probes/probe_rate_eighth_three_head_window.py)
