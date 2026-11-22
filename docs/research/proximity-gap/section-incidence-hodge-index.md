# A Hodge-index bound for polynomial sections of an interpolation surface

**Status.** Written proof. It uses the Hodge index theorem on a smooth
projective surface, Mumford's intersection pairing on a normal surface,
adjunction, Abhyankar's lemma and Riemann–Hurwitz as cited theorems. The
numerical consequences and the production arithmetic are kernel-checked in
[HodgeSectionIncidence.lean](../../../ArkLib/Research/ProximityGap/Frontier/HodgeSectionIncidence.lean),
and the step from the Hodge index inequality to Lemma 3 in
[HodgeSectionLattice.lean](../../../ArkLib/Research/ProximityGap/Frontier/HodgeSectionLattice.lean),
with every geometric fact an explicit hypothesis. The counting half of
Theorem D′, from the tangent-head data to the population bound, is
kernel-checked in
[TangentHeadCount.lean](../../../ArkLib/Research/ProximityGap/Frontier/TangentHeadCount.lean). The lattice inequalities are
checked on an explicit surface, where they are attained, by
[the exact probe](../../../scripts/probes/probe_section_incidence_hodge.py).
Nothing here is an end-to-end Lean theorem about `epsMCA`.

**Result.** Let $F(X,\Gamma,Y)$ be an absolutely irreducible polynomial of
value degree $b=\deg_YF\ge2$. Polynomial witnesses $(\gamma,P_\gamma)$ lying on
$F$ are sections of one fibration of the surface $F=0$. The received lines
$Y=u_0(x)+\Gamma u_1(x)$ are fibre components of the other fibration.
Theorem A bounds the **total number of incidences** between the two families
by $16\,b^2(a+1)(h_\Gamma+1)(h-1)$, where $a,h_\Gamma,h$ are degrees of $F$.
A family of $N$ witnesses with $t$ agreements each needs about $Nt$
incidences, so $N$ is bounded by a quantity that does not grow with the block
length.

**Consequence at the second named prime.** The hypothesis left open by
`secondPrime_threshold_of_cubic_exclusion` in
[SecondPrimeCubicOnly.lean](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeCubicOnly.lean)
is a population bound below $1431655733$ for an irreducible cubic over the
algebraic closure, of coordinate/value weight at most $290805098$, dividing a
supported interpolant. Corollary B gives **at most 360,973** sections on such
a cubic. With the Lean reduction this is a written proof of the rate-$1/16$
MCA threshold $715827882/2^{30}$ at that prime. It is independent of the
polar, Hessian and jet estimates.

**General form.** Theorem C removes every hypothesis on weight and on the
interpolation multiplicity: any absolutely irreducible $F$ with $b\ge2$
carries $O\!\bigl(b^6h^2(a+n)/(t-d)\bigr)$ sections with $t$ agreements.
With the value-linear count this shows that all but a bounded number of bad
scalars lie on affine heads dividing the interpolant, for every interpolant
of bounded scalar degree.

**Below the Johnson radius.** Theorem D replaces the Hodge inequality by a
rigidity statement for the rational *tangent heads* of the sections. It needs
$t^2>nd$ and gives a bound of order $b^2h\,a/(t^2/n-d)$ for every kind of
site. It gives at most 48,038 sections on the terminal cubic, and at most
$1.1\cdot10^6$ on any nonlinear factor of a multiplicity-three interpolant in
the open first-prime rate-$1/4$ bracket.

The exact rate-$1/16$ threshold on the second named prime now also has an independent end-to-end Lean proof. The geometric arguments below retain their stated surface-theoretic inputs. [Exact threshold](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeCubicExact.lean)

## Setting

Let $k$ be an algebraically closed field. Fix a finite set $D\subset k$ of
$n$ sites and two rows $u_0,u_1:D\to k$, and write
$\ell_x(\Gamma)=u_0(x)+\Gamma u_1(x)$. Fix a degree cap $d\ge0$.

Let $F\in k[X,\Gamma,Y]$ be irreducible, $F=\sum_{j\le b}f_j(X,\Gamma)Y^j$, with

* $b=\deg_YF\ge2$, $a=\deg_XF$, $h_\Gamma=\deg_\Gamma F$;
* $h$ the total degree of $F$ in $(\Gamma,Y)$, so $h_\Gamma\le h$ and
  $\deg_\Gamma F(X,\Gamma,\ell(\Gamma))\le h$ for affine $\ell$;
* weight $W=\max(i+dm)$ over the monomials $X^i\Gamma^jY^m$ of $F$.

Assume $\operatorname{char}k=0$ or $\operatorname{char}k>(2b-2)a+1$.
If $a=0$ then no site is a core site, since $Y-\ell_x(\Gamma)$ does not
divide $F$, and the count below gives $Nt\le hn$ directly.

A **section** is a pair $\sigma=(\gamma,P)$ with $\gamma\in k$, $P\in k[X]$,
$\deg P\le d$ and $F(X,\gamma,P(X))=0$ in $k[X]$. It is **simple** if
$F_Y(X,\gamma,P(X))\ne0$. Its **agreement set** is
$A(\sigma)=\{x\in D:P(x)=\ell_x(\gamma)\}$.

A site $x$ is a **core site** if $F(x,\Gamma,\ell_x(\Gamma))=0$ in
$k[\Gamma]$. Then $F(x,\Gamma,Y)=(Y-\ell_x(\Gamma))^{\mu_x}G_x(\Gamma,Y)$ with
$G_x(\Gamma,\ell_x(\Gamma))\ne0$ and $1\le\mu_x\le b$. The core site is
**simple** if $\mu_x=1$, equivalently
$v_x(\Gamma):=F_Y(x,\Gamma,\ell_x(\Gamma))\ne0$. It is **totally ramified**
if $\mu_x=b$, that is $F(x,\Gamma,Y)=f_b(x,\Gamma)(Y-\ell_x(\Gamma))^b$.

For a simple section $\sigma=(\gamma,P)$ let $J(\sigma)$ be the set of simple
core sites $x\in A(\sigma)$ with $v_x(\gamma)\ne0$. These are the
**ordinary incidences**.

Let $E_h\subset k$ be the set of scalars $\gamma$ for which the whole line
$\Gamma=\gamma$ lies in the branch curve defined below. It has at most
$(2b-2)h_\Gamma$ elements.

## Statements

**Theorem A (incidences at simple core sites).** Let $\mathcal P$ be a family
of simple sections with pairwise distinct scalars, none in $E_h$. Then
$$
\sum_{\sigma\in\mathcal P}|J(\sigma)|\ \le\
\frac{4b^2}{(b-1)^2}\,(h-1)\,\bigl((2b-2)h_\Gamma+1\bigr)\bigl((2b-2)a+1\bigr)
\ \le\ 16\,b^2\,(a+1)(h_\Gamma+1)(h-1).
$$

**Corollary B (population, weight below $t+d$).** Let $\mathcal Q$ be a
family of sections with pairwise distinct scalars and $|A(\sigma)|\ge t$ for
every $\sigma\in\mathcal Q$. If $W-d<t$, then
$$
|\mathcal Q|\ \le\ (4b-2)h_\Gamma+1+
\Bigl\lfloor\frac{16\,b^2\,(a+1)(h_\Gamma+1)(h-1)+h\,n}{t-W+d}\Bigr\rfloor.
$$
This is `populationBound` in the Lean file. The proof excludes only
$(4b-3)h_\Gamma$ scalars, which is within the allowance $(4b-2)h_\Gamma+1$.

**Theorem C (population, no weight hypothesis).** Let $\mathcal Q$ be as in
Corollary B with $t>d$, and put $\beta_X=(2b-2)h_\Gamma+1$,
$\beta_\Gamma=(2b-2)a+1$. Then
$$
|\mathcal Q|\ \le\ (4b-2)h_\Gamma+1+\max\Bigl\{\,h+3h_\Gamma\frac{t+d}{t-d},\
\frac{2\bigl((h+\beta_X)\,n+4b^2(b-1)\beta_X^2\beta_\Gamma\bigr)}{t-d}\Bigr\}.
$$

*Proof of Corollary B from Theorem A.* If a section is not simple, $P$ is a
common root of $F(X,\gamma,Y)$ and $F_Y(X,\gamma,Y)$, so the Sylvester
resultant $\operatorname{Res}_Y(F,F_Y)(X,\Gamma)$ vanishes identically at
$\Gamma=\gamma$. The resultant is nonzero because $F$ is irreducible and
separable in $Y$, and its degree in $\Gamma$ is at most $(2b-1)h_\Gamma$.
Together with $E_h$ at most $(4b-3)h_\Gamma$ scalars are excluded.

For a remaining $\sigma=(\gamma,P)$ split $A(\sigma)$ into four classes. At a
site which is not a core site, $F(x,\Gamma,\ell_x(\Gamma))$ is a nonzero
polynomial of degree at most $h$ vanishing at $\gamma$, so the site serves at
most $h$ sections. At a core site with $\mu_x\ge2$ one has
$F_Y(x,\gamma,P(x))=v_x(\gamma)=0$; the nonzero polynomial
$F_Y(X,\gamma,P(X))$ has degree at most $W-d$, so the section meets at most
$W-d$ such sites. A simple core site serves at most $h-1$ sections with
$v_x(\gamma)=0$. The remaining sites form $J(\sigma)$. Summing over the $N$
remaining sections, $\sum_\sigma|J(\sigma)|\ge N(t-W+d)-hn$, and Theorem A
gives the claim. $\qquad\blacksquare$

## The surface

Let $K$ be the fraction field of $k[X,\Gamma,Y]/(F)$ and let
$\nu:S'\to\mathbb P^1_X\times\mathbb P^1_\Gamma$ be the normalization of
$\mathbb P^1\times\mathbb P^1$ in $K$. It is finite of degree $b$ and
separable. Let $\pi:\widetilde S\to S'$ be the minimal resolution and
$\varphi=\nu\pi$, with projections $f_X,f_\Gamma$ and fibre classes
$\Phi_X,\Phi_\Gamma$. Then
$$
\Phi_X^2=\Phi_\Gamma^2=0,\qquad \Phi_X\cdot\Phi_\Gamma=b .
$$
On $S'$ we use Mumford's rational intersection pairing of Weil divisors,
$D\cdot D'=\pi^*D\cdot\pi^*D'$. Principal divisors are numerically trivial,
effective divisors without common components have nonnegative local
intersection numbers, the pullback of an effective divisor is effective, and
the projection formula holds for Cartier divisors pulled back along $\nu$.

**Hodge index.** The intersection form on
$\operatorname{Num}(\widetilde S)_{\mathbb Q}$ has signature $(1,\rho-1)$. As
$\Phi_\Gamma$ is nef with $\Phi_\Gamma^2=0$, every class $T$ with
$T\cdot\Phi_\Gamma=0$ has $T^2\le0$, and two such classes satisfy
$(T\cdot C)^2\le T^2\,C^2$. The same holds for Mumford's pairing on $S'$,
which embeds isometrically by $\pi^*$.

**Ramification.** The Jacobian of $\varphi$ defines an effective divisor $R$
with $K_{\widetilde S}=\varphi^*K_{\mathbb P^1\times\mathbb P^1}+R
\equiv-2\Phi_X-2\Phi_\Gamma+R$. Let
$\mathrm{Br}\subset\mathbb P^1\times\mathbb P^1$ be the reduced branch curve
of $\nu$. Ramification indices are at most $b<\operatorname{char}k$, so $\nu$
is tame, $K_{S'}\equiv\nu^*K+R'$ with $R'=\sum(e_i-1)R_i'\le\nu^*\mathrm{Br}$,
and $K_{\widetilde S}=\pi^*K_{S'}-Z$ with $Z\ge0$ exceptional because the
resolution is minimal. The divisors $R$ and $\pi^*R'-Z$ have the same strict
transform and the same intersection with every exceptional curve, so they are
equal. Hence
$$
R\ \le\ \varphi^*\mathrm{Br}. \tag{1}
$$
The cover is étale over every point of the affine plane at which the
degree-$b$ discriminant $\operatorname{Disc}_Y(F)$ is nonzero, including
points where $f_b$ vanishes, since the binary form of degree $b$ then has $b$
distinct roots on $\mathbb P^1_Y$. The discriminant has degree at most
$(2b-2)h_\Gamma$ in $\Gamma$ and $(2b-2)a$ in $X$. Counting the two lines at
infinity, $\beta_X:=\mathrm{Br}\cdot(\{x\}\times\mathbb P^1)$ and
$\beta_\Gamma:=\mathrm{Br}\cdot(\mathbb P^1\times\{\gamma\})$ satisfy
$$
\beta_X\le(2b-2)h_\Gamma+1,\qquad \beta_\Gamma\le(2b-2)a+1. \tag{2}
$$

## Four lemmas

**Lemma 1 (received lines).** Let $x$ be a simple core site. There is a
unique irreducible curve $\Lambda_x'\subset S'$ over $\{x\}\times\mathbb P^1$
whose image in the affine surface is the received line
$L_x=\{(x,\gamma,\ell_x(\gamma))\}$. It is a reduced component of
$\nu^*(\{x\}\times\mathbb P^1)$, it maps isomorphically to $\mathbb P^1_\Gamma$,
and
$$
\Lambda_x'\cdot\Phi_X=0,\qquad\Lambda_x'\cdot\Phi_\Gamma=1,\qquad
0\le a_x':=-(\Lambda_x')^2\le h-1 .
$$
Curves $\Lambda_x'$ at distinct sites are disjoint.

*Proof.* At a point of $L_x$ with $v_x(\gamma)\ne0$ one has $F_Y\ne0$. The
affine surface is smooth there and étale over the $(X,\Gamma)$-plane, so
$S'$ is isomorphic to it nearby and the fibre is the reduced curve $L_x$.
This gives uniqueness, reducedness and the two intersection numbers. A finite
birational map onto $\mathbb P^1$ is an isomorphism. A fibre component has
nonpositive square.

Put $w=Y-\ell_x(\Gamma)\in K$ and write
$\operatorname{div}(w)=j\Lambda_x'+V-P_w$ on $S'$ with $j\ge1$, $V\ge0$ not
containing $\Lambda_x'$, and $P_w\ge0$ the polar divisor. Intersecting with
$\Lambda_x'$ gives $j\,a_x'=V\cdot\Lambda_x'-P_w\cdot\Lambda_x'$.

Let $\Psi(X,\Gamma)=F(X,\Gamma,\ell_x(\Gamma))=(X-x)^m\Psi^\circ$ with
$\Psi^\circ(x,\Gamma)\ne0$. Taylor expansion in $Y$ at $\ell_x(\Gamma)$ gives
$\Psi=-wE$ on $S'$, where $E=\sum_{i\ge1}F^{[i]}(X,\Gamma,\ell_x(\Gamma))\,w^{i-1}$
has coefficients in $k[X,\Gamma]$. On a component $T$ of $V$ over the affine
plane, $w$ and $E$ are regular at the generic point, so
$\operatorname{ord}_T\Psi\ge\operatorname{ord}_Tw$. No component of $V$ lies
over $\{x\}\times\mathbb P^1$: on such a component $w=0$, so it would map onto
$L_x$ and equal $\Lambda_x'$. Thus $X-x$ is a unit along $T$ and
$V\le\nu^*Z(\Psi^\circ)$ over the affine plane.

At the point $s_\infty$ of $\Lambda_x'$ over $\Gamma=\infty$ use
$\Gamma'=1/\Gamma$, $Y'=Y/\Gamma$ and
$w'=\Gamma'w=Y'-u_1(x)-u_0(x)\Gamma'$. The polynomial
$\Gamma'^hF(X,1/\Gamma',Y'/\Gamma')$ has the same shape, and the same argument
bounds the zeros of $w'$ near $s_\infty$ by the pullback of the homogenized
curve. Since
$\operatorname{div}(w)=\operatorname{div}(w')-f_\Gamma^*(\infty)+f_\Gamma^*(0)$
and $f_\Gamma^*(\infty)\cdot\Lambda_x'=1$ is supported at $s_\infty$, summing
the local contributions gives
$$
j\,a_x'\ \le\ \nu^*\overline Z\cdot\Lambda_x'-1
=\overline Z\cdot(\{x\}\times\mathbb P^1)-1=h-1,
$$
where $\overline Z$ is the divisor of the bihomogeneous form of
$\Gamma$-degree $h$ defined by $\Psi^\circ$. $\qquad\blacksquare$

**Lemma 2 (sections).** Let $\sigma=(\gamma,P)$ be a simple section. Its
graph has a strict transform $\widetilde C_\sigma\subset\widetilde S$, a
smooth rational curve in $f_\Gamma^{-1}(\gamma)$ with
$\widetilde C_\sigma\cdot\Phi_X=1$, $\widetilde C_\sigma\cdot\Phi_\Gamma=0$
and
$$
c_\sigma:=-\widetilde C_\sigma^{\,2}=R\cdot\widetilde C_\sigma\ \ge0 .
$$
Its image $C_\sigma'\subset S'$ satisfies $-(C'_\sigma)^2\le c_\sigma$.
Sections with different scalars are disjoint. If $x\in J(\sigma)$ then
$C_\sigma'\cdot\Lambda_x'\ge1$.

*Proof.* The graph is generically étale over the plane, so it is not in the
singular locus, it has a strict transform, and it is not a component of $R$.
The restriction of $f_X$ is finite and birational onto $\mathbb P^1$, hence an
isomorphism. Adjunction gives
$-2=\widetilde C^2+K\cdot\widetilde C=\widetilde C^2-2+R\cdot\widetilde C$.
Mumford's pullback is $\pi^*C'=\widetilde C+\sum\theta_iE_i$ with
$\theta_i\ge0$, so
$(C')^2=\widetilde C^2+\sum\theta_iE_i\cdot\widetilde C\ge\widetilde C^2$.
At an ordinary incidence the point $(x,\gamma,\ell_x(\gamma))$ is a smooth
point at which the surface is étale over the plane, and both curves pass
through it. $\qquad\blacksquare$

**Lemma 3 (Bessel inequality).** For a simple section $\sigma$,
$$
c_\sigma\sum_{x\in J(\sigma)}a_x'\ \ge\ \Bigl(1-\frac1b\Bigr)^2|J(\sigma)|^2,
\qquad\text{hence}\qquad
c_\sigma\ \ge\ \Bigl(1-\frac1b\Bigr)^2\frac{|J(\sigma)|}{h-1}.
$$

*Proof.* Put $T=\sum_{x\in J(\sigma)}(\Lambda_x'-\tfrac1b\Phi_X)$. Then
$T\cdot\Phi_\Gamma=0=C_\sigma'\cdot\Phi_\Gamma$,
$T^2=-\sum a_x'$ and $T\cdot C_\sigma'\ge|J(\sigma)|(1-\tfrac1b)\ge0$. Apply
$(T\cdot C')^2\le T^2(C')^2$ and Lemmas 1 and 2. $\qquad\blacksquare$

**Lemma 4 (ramification budget).** For simple sections with pairwise
distinct scalars outside $E_h$,
$$
\sum_\sigma c_\sigma\ \le\ 2\,\beta_X(\beta_\Gamma-1)\ \le\ 2\,\beta_X\,\beta_\Gamma .
$$

*Proof.* The cover is tame, so every prime divisor $D$ of $S'$ over
$\mathrm{Br}$ has coefficient $e_D$ in $\nu^*\mathrm{Br}$ and $e_D-1$ in $R'$.
Hence $R'=\nu^*\mathrm{Br}-B'$ with $B'$ the reduced preimage of
$\mathrm{Br}$, and
$$
R=\varphi^*\mathrm{Br}-\pi^*B'-Z .
$$
Let $q\in\widetilde C_\sigma$ with image $\mathrm{pt}$ on the line
$\ell_\gamma=\mathbb P^1\times\{\gamma\}$. If $\mathrm{pt}\notin\mathrm{Br}$
then $q\notin\operatorname{Supp}R$. If $\mathrm{pt}\in\mathrm{Br}$ then $q$
lies in the support of the effective divisor $\pi^*B'$, which does not
contain $\widetilde C_\sigma$, so $(\pi^*B'\cdot\widetilde C_\sigma)_q>0$. As
$\widetilde C_\sigma\to\ell_\gamma$ is an isomorphism,
$(\varphi^*\mathrm{Br}\cdot\widetilde C_\sigma)_q=(\mathrm{Br}\cdot\ell_\gamma)_{\mathrm{pt}}$.
Therefore
$(R\cdot\widetilde C_\sigma)_q<(\mathrm{Br}\cdot\ell_\gamma)_{\mathrm{pt}}$.
The left side is an integer, because $R$ is an integral divisor on a smooth
surface. Summing over the points of the line,
$$
c_\sigma\ \le\ \sum_{\mathrm{pt}}\bigl((\mathrm{Br}\cdot\ell_\gamma)_{\mathrm{pt}}-1\bigr)
=\beta_\Gamma-\#(\mathrm{Br}\cap\ell_\gamma).
$$
Let $\mathrm{Br}'$ be $\mathrm{Br}$ without its horizontal lines and
$\psi:\widetilde{\mathrm{Br}'}\to\mathbb P^1_\Gamma$ the projection of its
normalization. The deficiency $\beta_\Gamma-\#(\mathrm{Br}\cap\ell_\gamma)$
equals the ramification of $\psi$ above $\gamma$ plus
$\sum(\text{branches}-1)$ over the points of $\mathrm{Br}'$ on the line.
Each component of $\psi$ has degree at most $\beta_\Gamma$, below the
characteristic, so it is separable. Summing over $\gamma$, Riemann–Hurwitz
and $\text{branches}-1\le\delta$ give at most
$2p_a(\mathrm{Br}')+2\beta_\Gamma-2=2\beta_X'(\beta_\Gamma-1)$, since
$p_a(\mathrm{Br}')=(\beta_X'-1)(\beta_\Gamma-1)$ with $\beta_X'\le\beta_X$.
Distinct scalars use distinct lines. $\qquad\blacksquare$

On the quartic del Pezzo surface the four singular conic fibres give four
sections with distinct scalars and $c_\sigma=1$, while $\beta_X=\beta_\Gamma=2$.
The bound $2\beta_X(\beta_\Gamma-1)=4$ is attained. An earlier version of this
note proved the lemma with the constant four.

*Proof of Theorem A.* By Lemmas 3 and 4,
$\bigl(1-\tfrac1b\bigr)^2\sum_\sigma|J(\sigma)|\le(h-1)\sum_\sigma c_\sigma
\le2(h-1)\beta_X\beta_\Gamma$, and (2) bounds the two branch degrees. This is
half of the stated bound. Theorem A, Corollary B and Theorem C are kept in
their original form, which the Lean file and the tables below use; each holds
with its incidence term halved. $\qquad\blacksquare$

## The general version

Theorem A uses only received lines that are simple on $F$. Two further facts
remove that restriction.

**Lemma 5 (any reduced fibre component).** Let $\Lambda'\subset S'$ be an
irreducible component of $\nu^*(\{x\}\times\mathbb P^1)$ of multiplicity one
and of degree $\lambda$ over the line. Then
$$
-(\Lambda')^2\ \le\ (b-\lambda)\,\lambda\,\beta_X .
$$

*Proof.* Write $\nu^*(\{x\}\times\mathbb P^1)=\Lambda'+\sum_jm_j\Lambda_j'$.
Then $-(\Lambda')^2=\sum_jm_j\Lambda_j'\cdot\Lambda'$ and
$\lambda+\sum_jm_j\lambda_j=b$, so $m_j\le b-\lambda$. Adjunction on the
normal surface gives $(K_{S'}+\Lambda')\cdot\Lambda'\ge-2$: for the strict
transform $\widetilde\Lambda$ one has
$(K_{S'}+\Lambda')\cdot\Lambda'=(K_{\widetilde S}+\widetilde\Lambda)\cdot\widetilde\Lambda
+(Z+\textstyle\sum\theta_iE_i)\cdot\widetilde\Lambda$. With
$K_{S'}\equiv\nu^*K+R'$ this reads
$-(\Lambda')^2\le R'\cdot\Lambda'+2-2\lambda$. The curve $\Lambda'$ is
unramified. The ramified components of the same fibre are the $\Lambda_j'$
with $m_j\ge2$, with coefficient $m_j-1$ in $R'$. The rest of $R'$ is at most
$\nu^*\mathrm{Br}_0$, where $\mathrm{Br}_0$ is $\mathrm{Br}$ without the
vertical line through $x$, and
$\nu^*\mathrm{Br}_0\cdot\Lambda'=\lambda\,\mathrm{Br}_0\cdot(\{x\}\times\mathbb P^1)\le\lambda\beta_X$.
Subtracting, $\sum_j\Lambda_j'\cdot\Lambda'\le\lambda\beta_X$, and each term is
nonnegative. $\qquad\blacksquare$

**Theorem A⁺ (incidences with reducible fibres).** For a simple section
$\sigma=(\gamma,P)$ with $\gamma\notin E_h$ let $J^+(\sigma)$ be the set of
sites $x$ such that $(x,\gamma)$ does not lie on a branch component other
than the vertical line through $x$, and the fibre component through the point
of $C_\sigma'$ over $x$ has degree $\lambda_x<b$ over that line. For sections
with pairwise distinct scalars,
$$
\sum_\sigma|J^+(\sigma)|\ \le\ 4\,b^2(b-1)\,\beta_X^2\,\beta_\Gamma .
$$

*Proof.* Near $(x,\gamma)$ the branch curve is contained in a smooth divisor,
so by Abhyankar's lemma $S'$ is regular above this point and exactly one
fibre component $\Lambda_x'$ passes through the point of $C_\sigma'$. As
$C_\sigma'\cdot\nu^*(\{x\}\times\mathbb P^1)=1$, that component has
multiplicity one and $C_\sigma'\cdot\Lambda_x'\ge1$. Put
$\omega_x=1-\lambda_x/b\ge1/b$ and
$T=\sum_{x\in J^+(\sigma)}(\Lambda_x'-\tfrac{\lambda_x}b\Phi_X)$. Then
$T\cdot\Phi_\Gamma=0$, $T\cdot C_\sigma'\ge\sum\omega_x$ and, by Lemma 5,
$-T^2\le\sum b\,\omega_x\lambda_x\beta_X\le b(b-1)\beta_X\sum\omega_x$. The
Hodge inequality gives $\sum\omega_x\le b(b-1)\beta_X\,c_\sigma$, hence
$|J^+(\sigma)|\le b^2(b-1)\beta_X\,c_\sigma$. Apply Lemma 4.
$\qquad\blacksquare$

**Lemma U (totally ramified core sites).** Let $U$ be the set of totally
ramified core sites and $u=|U|$. If $u>d$, any family of sections with
pairwise distinct scalars has at most $h+3h_\Gamma\,u/(u-d)$ members.

*Proof.* The polynomial $f_b(x,\Gamma)$ is nonzero for $x\in U$, since
otherwise $X-x$ divides $F$. If $f_b(x,\gamma)\ne0$ then
$0=F(x,\gamma,P(x))=f_b(x,\gamma)(P(x)-\ell_x(\gamma))^b$, so every section
with scalar $\gamma$ agrees at $x$. Let $\operatorname{miss}(\sigma)$ count
the $x\in U$ with $f_b(x,\gamma)=0$. Then
$\sum_\sigma\operatorname{miss}(\sigma)\le h_\Gamma u$, so at most
$3h_\Gamma u/(u-d)$ sections have
$\operatorname{miss}(\sigma)\ge(u-d)/3$. Any three of the others agree with
the received lines on more than $d$ common sites of $U$. Two of them,
$(\gamma_1,P_1)$ and $(\gamma_2,P_2)$, define $A,B$ of degree at most $d$
with $A+\gamma_iB=P_i$. On the common sites $A=u_0$ and $B=u_1$, so the third
section equals $A+\gamma_3B$. All these sections lie on the affine head
$Y=A+\Gamma B$. The polynomial $F(X,\Gamma,A+\Gamma B)$ is nonzero of degree
at most $h$ in $\Gamma$, so at most $h$ scalars occur. $\qquad\blacksquare$

*Proof of Theorem C.* Put $s=\lfloor(t-d)/2\rfloor$. If $u>d+s$, Lemma U
gives $|\mathcal Q|\le h+3h_\Gamma(t+d)/(t-d)$. Otherwise remove the at most
$(4b-3)h_\Gamma$ scalars that are not simple or lie in $E_h$. Each remaining
section has at most $d+s$ agreements in $U$ and at least $(t-d)/2$ elsewhere.
A site that is not a core site serves at most $h$ sections. At a core site
with $\mu_x<b$, at most $h-1$ sections have $G_x(\gamma,\ell_x(\gamma))=0$
and at most $\beta_X$ have $(x,\gamma)$ on another branch component. For every
other agreement the only fibre curve through the point of the section is the
one over $L_x$. The fibre components over $L_x$ have total degree $\mu_x$
counted with multiplicity, so $\lambda_x\le\mu_x<b$ and $x\in J^+(\sigma)$.
Summing and applying Theorem A⁺,
$N(t-d)/2\le(h+\beta_X)n+4b^2(b-1)\beta_X^2\beta_\Gamma$.
$\qquad\blacksquare$

**Lemma V (value-linear factors).** Let $F=E(X,\Gamma)Y-N(X,\Gamma)$ be
irreducible of total $(\Gamma,Y)$-degree at most $h$ and not of the form
$c\,(Y-A(X)-\Gamma B(X))$. A family of sections with distinct scalars and at
least $t>d$ agreements each has at most
$\max\{h+3h_\Gamma(t+d)/(t-d),\ 2hn/(t-d)\}$ members.

*Proof.* At a core site $E(x,\Gamma)\ne0$, and every section with
$E(x,\gamma)\ne0$ agrees there. The proof of Lemma U applies with $E$ in
place of $f_b$. If more than $h$ sections lay on one head, then
$E\cdot(A+\Gamma B)=N$ identically, and irreducibility would make $F$ that
head. A site that is not a core site serves at most $h$ sections.
$\qquad\blacksquare$

**Corollary S (structure of bad scalars).** Let $Q\in k[X,\Gamma,Y]$ be
nonzero of total $(\Gamma,Y)$-degree at most $h$ and value degree $D$. Let
$\mathcal G$ be a set of scalars, each with a witness $P_\gamma$ of degree at
most $d$ that agrees with $u_0+\gamma u_1$ on at least $t>d$ sites and
satisfies $Q(X,\gamma,P_\gamma(X))=0$. Then every $\gamma\in\mathcal G$
outside a set of size at most $h+D\cdot M$ has its witness on an affine head
$Y=A+\Gamma B$ dividing $Q$, where $M$ is the larger of the bounds of
Theorem C and Lemma V for the irreducible factors of $Q$. No assumption is
made on the multiplicity with which $Q$ interpolates.

## A second route below the Johnson radius: tangent heads

The following argument uses Lemma 4 but not the Hodge index theorem. It treats
every kind of site uniformly and has a much smaller constant when the received
lines are not simple on $F$. It needs $t^2>nd$.

For a simple section $\sigma=(\gamma,P)$ put
$$
V_\sigma=-\frac{F_\Gamma(X,\gamma,P)}{F_Y(X,\gamma,P)}\in k(X),\qquad
R_\sigma=P-\gamma V_\sigma .
$$
The pair $(R_\sigma,V_\sigma)$ is the **tangent head** of the section. It is
an affine head exactly when $V_\sigma$ is a polynomial of degree at most $d$.

The coefficient $f_j$ of $F$ is a form of bidegree $(W-jd,\,h-j)$ on
$\mathbb P^1\times\mathbb P^1$, and $Y$ is a rational section of the pullback
of $\mathcal O(d,1)$. Let $\rho:\widetilde S_1\to\widetilde S$ be a minimal
composition of blow-ups after which $(X,Y)$ is a morphism $\xi$ to the
Hirzebruch surface $\mathbb F_d$, and write $c^1_\sigma$ for minus the
self-intersection of the strict transform of $\widetilde C_\sigma$ there.

**Lemma 6 (height of the tangent head).** There are polynomials $s_1\ne0$ and
$s_2$ with $V_\sigma=s_2/s_1$, $\deg s_1\le c^1_\sigma$ and
$\deg s_2\le d+c^1_\sigma$. The zeros of $s_1$ are the points of the section
that lie on the Jacobian divisor of $\widetilde S_1\to\mathbb P^1\times\mathbb P^1$.

*Proof.* The graph $\Sigma_P\subset\mathbb F_d$ of $P$ has normal bundle
$\mathcal O(d)$, and the normal bundle $N$ of the section in $\widetilde S_1$
is $\mathcal O(-c^1_\sigma)$. The differential of $(\xi,\Gamma)$ maps $N$ to
$\mathcal O(d)\oplus\mathcal O$. Its components are sections $s_2$ of
$\mathcal O(d+c^1_\sigma)$ and $s_1$ of $\mathcal O(c^1_\sigma)$. The second
is the differential of the scalar projection, which vanishes exactly on the
Jacobian divisor. At a general point the normal direction is the lift
$\partial_\Gamma+V_\sigma\partial_Y$, so $s_2/s_1=V_\sigma$.
$\qquad\blacksquare$

**Lemma 7 (height budget).** For simple sections with pairwise distinct
scalars outside $E_h$,
$$
\sum_\sigma c^1_\sigma\ \le\ C':=2\beta_X\beta_\Gamma+b\bigl(W(h-b)+h(W-bd)\bigr)
\ \le\ C^*:=4\beta_X\beta_\Gamma+b\bigl(W(h-b)+h(W-bd)\bigr).
$$

*Proof.* Each blow-up centre lies over one scalar, so it lies on at most one
of the disjoint sections and lowers that self-intersection by one. Hence
$\sum c^1_\sigma\le\sum c_\sigma+K$ with $K$ the number of blow-ups, and
Lemma 4 bounds the first sum. The indeterminacy points of $Y$ are the common
points of its polar divisor $P_Y$ and the zero divisor $Z_A$ of $Y-A$, for any
polynomial $A(X)$ of degree at most $d$. Separating two effective divisors
without common components takes at most $Z_A\cdot P_Y$ blow-ups, since a
blow-up at a common point of multiplicities $m,m'$ lowers this number by
$\min(m,m')^2$. The polynomial sections form a linear system without base
points on $\mathbb F_d$, so for general $A$ the divisor $Z_A$ moves without
fixed components and is nef. As $f_bY$ is integral,
$P_Y\le\varphi^*\operatorname{div}(f_b)$, and
$Z_A\le\varphi^*\operatorname{div}F(X,\Gamma,A)$ by the Taylor expansion used
in Lemma 1. Both pullbacks are nef, so
$K\le\varphi^*\mathcal O(W,h)\cdot\varphi^*\mathcal O(W-bd,h-b)
=b\,(W(h-b)+h(W-bd))$. $\qquad\blacksquare$

**Lemma 8 (regular incidences).** Let $x\in A(\sigma)$ be a core site with
$G_x(\gamma,\ell_x(\gamma))\ne0$ such that the point of the section over $x$
is an étale point of $S'$ over the plane. Then $s_1(x)\ne0$,
$V_\sigma(x)=u_1(x)$ and $R_\sigma(x)=u_0(x)$. For a given section at most
$c_\sigma$ agreement sites have a point that is not étale.

*Proof.* The point $(x,\gamma)$ is not a common zero of the $f_j$, since
$F(x,\gamma,Y)\ne0$. So $Y$ is regular at the point of the section, no
blow-up is centred there, and $S'$ has a branch $Y=y(X,\Gamma)$ with $y$ a
power series, $y(X,\gamma)=P(X)$ and $F(X,\Gamma,y)=0$. On $X=x$ the only
curve of $F(x,\Gamma,Y)=0$ through the point is the received line, so
$y(x,\Gamma)=\ell_x(\Gamma)$. Differentiating $F(X,\Gamma,y)=0$ gives
$V_\sigma=\partial_\Gamma y(X,\gamma)$, which is regular at $x$ with value
$u_1(x)$. A point that is not étale lies on $R$, and distinct sites give
distinct points of $\widetilde C_\sigma$. $\qquad\blacksquare$

**Theorem D (population below the Johnson radius).** Let $\mathcal Q$ be a
family of sections with pairwise distinct scalars and at least $t$ agreements
each. Let $\bar c,\bar n\ge0$ be integers and put $t'=t-\bar n-\bar c$,
$d'=d+2\bar c$. If $t'^2>nd'$, then
$$
|\mathcal Q|\ \le\ (4b-2)h_\Gamma+1+\Bigl\lfloor\frac{C^*}{\bar c+1}\Bigr\rfloor
+\Bigl\lfloor\frac{hn}{\bar n+1}\Bigr\rfloor
+h\Bigl\lfloor\frac{n(t'-d')}{t'^2-nd'}\Bigr\rfloor .
$$

*Proof.* Remove the scalars that are not simple or lie in $E_h$. By Lemma 7
at most $C^*/(\bar c+1)$ sections have $c^1_\sigma>\bar c$. A site that is
not a core site serves at most $h$ sections, and a core site serves at most
$h-1$ sections with $G_x(\gamma,\ell_x(\gamma))=0$. So at most
$hn/(\bar n+1)$ sections have more than $\bar n$ agreements of these two
kinds. For each remaining section let $J_\sigma$ be its set of regular
incidences. By Lemma 8, $|J_\sigma|\ge t'$.

Let $\sigma,\tau$ be two remaining sections with
$|J_\sigma\cap J_\tau|>d'$. The polynomial
$s_2^\sigma s_1^\tau-s_2^\tau s_1^\sigma$ has degree at most
$d+c^1_\sigma+c^1_\tau\le d'$ and vanishes on $J_\sigma\cap J_\tau$, so
$V_\sigma=V_\tau=:V$. Then
$(P_\sigma-P_\tau)s_1-(\gamma_\sigma-\gamma_\tau)s_2$ has degree at most
$d+\bar c$ and vanishes on the same set, so
$P_\sigma-P_\tau=(\gamma_\sigma-\gamma_\tau)V$. Thus $V$ is a polynomial of
degree at most $d$ and both sections lie on the affine head
$Y=R_\sigma+\Gamma V$.

Call two remaining sections equivalent if their tangent heads are equal. A
class with two members lies on one affine head, so it has at most $h$
members. Representatives of different classes have
$|J_\sigma\cap J_\tau|\le d'$. For $N$ sets of size at least $t'$ in an
$n$-set with pairwise intersections at most $d'$, counting incidences gives
$N(t'^2-nd')\le n(t'-d')$. $\qquad\blacksquare$

At the terminal cubic of the second named prime, $\bar c=2^{24}$ and
$\bar n=2^{23}$ give **at most 48,038** sections, and 99,313 for the quartic.

**Theorem D′ (averaged form).** Let $C'$ be as in Lemma 7 and suppose
$t^2>nd$. A family of sections with pairwise distinct scalars and at least $t$
agreements each has at most
$$
(2b-2)h_\Gamma+\Bigl\lfloor\frac{h\,n\,(2t+n)+2C'(t+n)}{t^2-nd}\Bigr\rfloor
$$
members.

*Proof.* Remove the scalars whose horizontal line lies in the zero set of the
discriminant. There are at most $(2b-2)h_\Gamma$ of them, and they include
$E_h$ and every scalar carrying a section that is not simple. Let $N$
sections remain, with regular incidence sets $J_\sigma$ and
$S=\sum_\sigma|J_\sigma|$. A site serves at most $h$ sections at agreements
that are not at a core site or have $G_x(\gamma,\ell_x(\gamma))=0$, and by
Lemma 8 a section has at most $c_\sigma\le c^1_\sigma$ further agreements
outside $J_\sigma$. With Lemma 7,
$$
S\ \ge\ Nt-hn-C'.
$$
Two sections with different tangent heads satisfy
$|J_\sigma\cap J_\tau|\le d+c^1_\sigma+c^1_\tau$, by the two polynomial
identities in the proof of Theorem D. Sections with the same tangent head lie
on one affine head, so each section has at most $h-1$ such partners, and for
those $|J_\sigma\cap J_\tau|\le n$. Counting pairs of sections through each
site,
$$
\frac{S^2}{n}\ \le\ \sum_{\sigma,\tau}|J_\sigma\cap J_\tau|
\ \le\ Nn+N^2d+2NC'+N(h-1)n .
$$
If $Nt\le hn+C'$ the claim holds. Otherwise insert the lower bound for $S$
and divide by $N$:
$N(t^2-nd)\le2t(hn+C')+n(hn+2C')$. $\qquad\blacksquare$

The averaged form needs no cut-offs and uses the sharper constant of Lemma 4.
It gives at most **19,433** sections on the terminal second-prime cubic and
41,542 on the quartic. For the multiplicity-three example above it gives
25,522, 79,953, 168,073, 289,882 and 445,379 sections at value degrees two
through six. [Windows obtained from it](tangent-head-windows.md)

*A multiplicity-three example.* At the first named prime and rate $1/4$ the
last error count below the known attack is $e=480946858$, so $t=592794966$,
$d=2^{28}-1$ and $t^2>nd$. Polynomials of value degree at most six, total
scalar/value degree at most 23 and weight below $3t$ outnumber the conditions
for vanishing to order three along every received line, and 23 is the least
such degree. Every witness is a section of such an interpolant. For an
irreducible factor of value degree $b$, with no assumption beyond
$a\le W<3t$, Theorem D with $\bar c=2^{24}$, $\bar n=2^{22}$ gives

| value degree $b$ | 2 | 3 | 4 | 5 | 6 |
|---|---:|---:|---:|---:|---:|
| sections | 56,175 | 176,645 | 374,183 | 648,789 | 1,000,463 |

All are below $10^{-3}n$. In this bracket the bad scalars are therefore
carried by at most six affine heads up to an additive error near $10^6$, and a
nonlinear factor of value degree $b$ leaves at most $6-b$ heads.

## Sharpness and independent checks

On the quartic del Pezzo surface with conic bundles $|H-E_1|$ and
$|2H-E_2-E_3-E_4-E_5|$ one has $b=2$, every line and every section is a
$(-1)$-curve, $R\cdot C=R\cdot\Lambda=1$, and each section meets one line at
each of the four sites. Lemma 3 reads $1\cdot4\ge(4\cdot\tfrac12)^2$, an
equality. The probe verifies the adjunction identities, Lemma 3 for all 128
choices, the pair inequality below and the budget.

For $F=Y^2-(X-\Gamma)^2-cG(X)H(\Gamma)$ with $\deg G=\kappa$,
$\deg H=\eta\ge2$, the lines $Y=\pm(x_i-\Gamma)$ at the roots of $G$ are
simple and the sections $Y=\pm(X-\gamma_j)$ at the roots of $H$ are each
incident to all $\kappa$ lines of the same sign. The total incidence is
$\eta\kappa$ for distinct scalars, linear in $a$ as in Theorem A.

For $F=(Y-A-\Gamma B)^2-c(\Gamma)M(X)^2$ with $c$ not a square and
$\deg M\le d$, sections exist for **every** scalar. All their agreements at
core sites are at the roots of $M$, which are totally ramified. The count of
Theorem C is then $N(t-d)\le hn$. This example shows that sections cannot be
bounded without using agreements, and that Lemma U is needed.

**Heights in the same example.** Take $\kappa$ even and $d=1$ there. The fibre
of the scalar projection over a root $\gamma_j$ of $H$ is $C_+ + C_-$ with
$y=\pm(X-\gamma_j)$. The two components meet once at $X=\gamma_j$ and with
multiplicity $(\kappa-2)/2$ over $X=\infty$, where the branch curve is smooth
and tangent to the fibre line. So $c_\sigma=\kappa/2$, in agreement with the
local formula in the proof of Lemma 4. The tangent slope is
$V_\sigma=-1+cH'(\gamma_j)G(X)/(2(X-\gamma_j))$, of height $\kappa-1$. The
difference $(\kappa-2)/2$ comes from the indeterminacy of $Y$ at the point of
the section over $X=\infty$. The second term of $C'$ in Lemma 7 therefore
cannot be dropped.

**A pair inequality.** The same computation with
$C_\sigma'-C_\tau'+\mu\bigl(\sum_{\Delta_1}\Lambda_x'-\sum_{\Delta_2}\Lambda_x'\bigr)$,
for equinumerous $\Delta_1\subseteq J(\sigma)\setminus A(\tau)$ and
$\Delta_2\subseteq J(\tau)\setminus A(\sigma)$, gives
$$
\min\bigl(|J(\sigma)\setminus A(\tau)|,\ |J(\tau)\setminus A(\sigma)|\bigr)
\le\tfrac12(h-1)(c_\sigma+c_\tau).
$$
Two sections of small defect have almost the same agreement set.

**Reading in terms of scalar derivatives.** For a simple section the lift of
$\partial_\Gamma$ to the surface along the section is
$\partial_\Gamma+V_\sigma\partial_Y$ with
$V_\sigma=-F_\Gamma(X,\gamma,P)/F_Y(X,\gamma,P)\in k(X)$. Differentiating
$F(x,\Gamma,\ell_x(\Gamma))=0$ shows $V_\sigma(x)=u_1(x)$ for every
$x\in J(\sigma)$. The normal bundle of $\widetilde C_\sigma$ is
$\mathcal O(-R\cdot\widetilde C_\sigma)$, so $c_\sigma$ is the number of poles
of this lifted field counted on $\widetilde S$. Writing
$F(X,\gamma,Y)=(Y-P)H$ one has
$\operatorname{Disc}_YF(X,\gamma)=\operatorname{Disc}_Y(H)\cdot F_Y(X,\gamma,P)^2$,
which is the elementary form of the tangency statement in Lemma 4. Lemma 3
says that a section through $m$ simple received lines forces at least
$(1-\tfrac1b)^2m/(h-1)$ such poles.

## An elementary identity for the value derivative

The following uses no geometry. Let $\sigma=(\gamma,P)$ be a simple section
with $f_b(X,\gamma)\ne0$, and divide by the monic factor:
$F(X,\gamma,Y)=(Y-P(X))\,H_\sigma(X,Y)$. Then
$G_\sigma:=F_Y(X,\gamma,P)=H_\sigma(X,P)$, and the product formula for
discriminants gives
$$
\operatorname{Disc}_YF\,(X,\gamma)=\operatorname{Disc}_Y(H_\sigma)\cdot G_\sigma(X)^2. \tag{3}
$$
So every root of $G_\sigma$ of multiplicity $\mu$ is a root of the specialized
discriminant of multiplicity at least $2\mu$.

Write $\operatorname{Disc}_YF=E^2\Delta_1$ in $k[X,\Gamma]$ with $\Delta_1$
squarefree as a polynomial in $X$. For a scalar at which neither factor
vanishes identically, let $S_\gamma^2$ be the largest square dividing
$\Delta_1(X,\gamma)$. By (3) and unique factorization,
$$
G_\sigma\ \mid\ E(X,\gamma)\,S_\gamma(X),\qquad
\sum_\gamma\deg S_\gamma\ \le\ \deg_\Gamma\operatorname{Disc}_X(\Delta_1),
$$
the sum being over scalars at which the leading coefficient of $\Delta_1$ in
$X$ does not vanish. The second inequality holds because a root of
multiplicity $m$ of a specialization lowers the number of distinct roots by
$m-1\ge\lfloor m/2\rfloor$, and the order of the discriminant at $\gamma$ is at
least that loss.

Two consequences follow.

* If $\operatorname{Disc}_YF$ is squarefree in $X$, then $E=1$ and
  $\sum_\sigma\deg G_\sigma\le\deg_\Gamma\operatorname{Disc}_X(\operatorname{Disc}_YF)$
  over simple sections with distinct scalars. No hypothesis on agreements is
  needed. For value degree two this is the square-fibre count already used for
  quadratic factors.
* In general $\deg G_\sigma-\deg\gcd(G_\sigma,E(X,\gamma))\le\deg S_\gamma$. At a
  received line along which $F$ has $\mu_x$ transversal sheets, a section
  through one of them has $G_\sigma$ vanishing to order $\mu_x-1$ there. A
  factor with many sections must therefore be singular along enough received
  lines, or other curves, to absorb almost all zeros of $G_\sigma$: the
  remaining zeros are the poles counted by the height of the tangent head.

This is a structural remark. It does not give a cap for an arbitrary factor,
because the degree of $E$ is not bounded by the interpolation data.

**Explicit surfaces.** The
[surface probe](../../../scripts/probes/probe_tangent_head_surface.py) builds
polynomials $F$ over $\mathbb F_{10007}$ of value degree two and three by
linear algebra. Each contains four to six planted sections, contains several
received lines simply and is singular along two to four others. On all five
surfaces, at every agreement on a core line where the reduced denominator of
$V_\sigma$ is nonzero, $V_\sigma$ equals the second received row and
$R_\sigma$ the first. This includes 74 agreements on double lines, where
$F_Y$ vanishes on the section. The heights sum to at most 110 against budgets
$C'$ of 690 to 2028, and for value degree two identity (3) holds exactly. On
these surfaces every height equals $W-d$ minus the number of double lines
through the section, as the second consequence predicts.

## The terminal cubic at the second named prime

Let $n=2^{30}$, $d=2^{26}-1=67108863$ and $t=357913943$. The Lean theorem
`actual_cubic` produces, from any family of more than $2147483648$ bad
scalars, a supported interpolant $Q$ over the algebraic closure and an
irreducible factor $F$ of value degree three, weight at most $290805098$ and
population at least $1431655733$. The population consists of scalars with
pairwise distinct labels whose selected witness has degree at most $d$,
agrees with the received line on at least $t$ sites and lies on $F$.
A supported interpolant has total $(\Gamma,Y)$-degree at most $34$, and so
does $F$.

Apply Corollary B with $b=3$, $a\le W\le290805098$, $h_\Gamma\le h\le34$ and
$t-W+d\ge134217708$:
$$
|\mathcal Q|\le10\cdot34+1+
\Bigl\lfloor\frac{144\cdot290805099\cdot35\cdot33+34\cdot2^{30}}{134217708}\Bigr\rfloor=360973 .
$$
The characteristic condition is $p>4\cdot290805098+1=1163220393$, which
holds for the named prime. The field is algebraically closed, so $F$ is
absolutely irreducible.

| factor | weight used | sections by Corollary B | population to exclude |
|---|---:|---:|---:|
| cubic, Lean weight | $\le290805098$ | at most 360,973 | 1,431,655,733 |
| quartic, Lean weight | $\le302954072$ | at most 734,604 | 2,147,483,615 |
| cubic, any weight below $t$ | $\le357913942$ | at most 887,925 | 1,431,655,733 |
| quartic, any weight below $t$ | $\le357913942$ | at most 1,577,981 | 2,147,483,615 |

The four values are the Lean theorem `terminal_bounds`. Theorem C, which does
not use the weight hypothesis, gives 10,812,548 for the cubic and 100,872,934
for the quartic. The quadratic and quartic populations already
have Lean bounds; the cubic row is the one that the Lean reduction still
takes as a hypothesis.

## Actual ordinary incidences at the second prime

The [actual cubic incidence theorem](../../../ArkLib/Research/ProximityGap/Frontier/ActualCubicHodgeIncidences.lean) proves the exceptional-scalar and agreement estimates for the original received rows. The resultant of the cubic and its value derivative is nonzero and has scalar degree at most 161. Remove the scalar values where its whole specialization vanishes as a polynomial in the coordinate. Every remaining cubic fiber has degree three and is separable over $k(X)$.

For each retained section, remove agreements where its value derivative vanishes. The derivative on the section has coordinate degree at most $290805098-67108863=223696235$, leaving at least $134217708$ agreements. At each noncore site the received line meets the cubic at no more than 34 scalars. Every remaining pair is an ordinary incidence as defined above. In particular, a counterexample would produce at least $1431655572$ retained sections and at least **192,153,493,012,046,960** ordinary incidence pairs.

The named threshold now follows in Lean from a strict upper bound of **192,153,493,012,046,960** on those pairs. At the actual cubic weight, Theorem A would give at most **48,366,704,065,680** ordinary incidences. The surface-intersection and ramification estimates in Lemmas 1–4 are the remaining geometric inputs for this route.

## Scope and what remains

1. *Formal status.* The cubic bound is a written proof. Formalizing it needs
   the Hodge index theorem, resolution of normal surface singularities with
   Mumford's pairing, and Abhyankar's lemma, none of which is in the pinned
   Mathlib. The Lean file checks only the inequalities that follow once the
   intersection numbers are given.
2. *Fields of definition.* The statements are over an algebraically closed
   field. A factor irreducible over a smaller field splits into conjugate
   factors of equal value degree. A section defined over the smaller field
   lies on all of them. If the conjugates have value degree at least two,
   apply the theorems to one conjugate. If they are value-linear and there
   are at least two, such sections lie on the intersection of two distinct
   surfaces and number at most the scalar degree of their resultant.
3. *Constants.* Theorem A is attained up to the factor depending on $h$ and
   $b$. The constant in Theorem A⁺ comes from Lemma 5 and is larger by about
   $2b^4$. For sites where only one fibre curve lies over the received line,
   the argument of Lemma 1 gives $-(\Lambda')^2\le\lambda(h-1)$ instead.
4. *Characteristic.* Tameness and separability are used in (1), in
   Abhyankar's lemma and in Riemann–Hurwitz. Additive constructions in
   characteristic two violate the conclusion, as they must.
5. *Use beyond first-order interpolation.* Corollary S applies to any
   interpolant, including multiplicity interpolants below the Johnson radius.
   What it needs as input is an interpolant whose total $(\Gamma,Y)$-degree
   is bounded independently of the length. It reduces every remaining
   threshold question in that range to the count of labels on at most $D$
   affine heads, up to the explicit additive error above.
