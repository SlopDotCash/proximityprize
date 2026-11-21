# A Hodge-index bound for polynomial sections of an interpolation surface

**Status.** Written proof. It uses the Hodge index theorem, resolution of
surface singularities, Riemann–Hurwitz and Abhyankar's lemma as geometric inputs. The numerical consequence of the Hodge intersection inequality,
its sum over sections and the production arithmetic are
kernel-checked in
[HodgeSectionIncidence.lean](../../../ArkLib/Research/ProximityGap/Frontier/HodgeSectionIncidence.lean)
with the geometric facts as explicit hypotheses. The local Bessel inequality attains equality on an explicit surface, as
checked by
[the exact probe](../../../scripts/probes/probe_section_incidence_hodge.py).
Nothing here is an end-to-end Lean theorem about `epsMCA`.

**What it gives.** Let $F(X,\Gamma,Y)$ be an irreducible factor of a
first-order interpolant, of value degree $b=\deg_YF\ge2$. Polynomial witnesses
$(\gamma,P_\gamma)$ lying on $F$ are sections of one fibration of the surface
$F=0$; the received lines $Y=u_0(x)+\Gamma u_1(x)$ are fibre components of
the other. Theorem A bounds the **total number of incidences** between the two
families by $16\,b^2\,(a+1)(h_\Gamma+1)(h-1)$, a quantity linear in the block
length. A family of $N$ witnesses with about $t$ agreements each needs about
$Nt$ incidences, so $N$ is bounded independently of the length. At the last
second-prime predecessor the bound is **887,925** sections on a cubic factor
and **1,577,981** on a quartic factor, against the populations
$1431655733$ and $2147483615$ that the
[exact-threshold reduction](second-prime-exact-threshold.md#the-three-remaining-nonlinear-population-bounds)
must exclude. This is an argument independent of the polar, Hessian and jet
estimates used there.

The bound does not treat value-linear factors ($b=1$). It counts incidences at
*simple* core sites only, which suffices whenever the factor has coordinate
weight below $t+d$; this holds for every factor of a first-order interpolant.
Factors of a higher-multiplicity interpolant can have larger weight, and the
received lines are then multiple fibre components. That case is discussed in
the last section and is open.

## Setting

Let $k$ be an algebraically closed field. Fix a finite set $D\subset k$ of
$n$ sites and two rows $u_0,u_1:D\to k$, and write
$\ell_x(\Gamma)=u_0(x)+\Gamma u_1(x)$.

Let $F\in k[X,\Gamma,Y]$ be irreducible with

* $b=\deg_YF\ge2$, $a=\deg_XF$, $h_\Gamma=\deg_\Gamma F$;
* $h$ the total degree of $F$ in $(\Gamma,Y)$, so $h_\Gamma\le h$ and
  $\deg_\Gamma F(X,\Gamma,\ell(\Gamma))\le h$ for affine $\ell$;
* weight $W=\max(i+dm)$ over the monomials $X^i\Gamma^jY^m$ of $F$, for a
  fixed degree cap $d\ge0$.

Assume $\operatorname{char}k=0$ or $\operatorname{char}k>\max\{b,(2b-2)a+1\}$.

A **section** is a pair $\sigma=(\gamma,P)$ with $\gamma\in k$,
$P\in k[X]$, $\deg P\le d$ and $F(X,\gamma,P(X))=0$ in $k[X]$. It is
**simple** if $F_Y(X,\gamma,P(X))\ne0$.

A site $x\in D$ is a **core site** if $F(x,\Gamma,\ell_x(\Gamma))=0$ in
$k[\Gamma]$. It is a **simple core site** if moreover
$v_x(\Gamma):=F_Y(x,\Gamma,\ell_x(\Gamma))\ne0$. Equivalently
$F(x,\Gamma,Y)=(Y-\ell_x(\Gamma))G_x(\Gamma,Y)$ with
$v_x=G_x(\Gamma,\ell_x(\Gamma))\ne0$.

For a simple section $\sigma=(\gamma,P)$ let $J(\sigma)$ be the set of simple
core sites $x$ with $P(x)=\ell_x(\gamma)$ and $v_x(\gamma)\ne0$. These are the
**ordinary incidences**.

Let $E_h\subset k$ be the set of scalars $\gamma$ for which the whole line
$\Gamma=\gamma$ lies in the branch curve defined below. It has at most
$(2b-2)h_\Gamma+1$ elements.

## Statements

**Theorem A (incidence bound).** Let $\mathcal P$ be a family of simple
sections with pairwise distinct scalars, none in $E_h$. Then
$$
\sum_{\sigma\in\mathcal P}|J(\sigma)|\ \le\
\frac{4b^2}{(b-1)^2}\,(h-1)\,\bigl((2b-2)h_\Gamma+1\bigr)\bigl((2b-2)a+1\bigr)
\ \le\ 16\,b^2\,(a+1)(h_\Gamma+1)(h-1).
$$

**Corollary B (population bound).** Let $\mathcal Q$ be a family of sections
with pairwise distinct scalars such that every $(\gamma,P)\in\mathcal Q$ has
$P(x)=\ell_x(\gamma)$ for at least $t$ sites $x\in D$. If $W-d<t$, then
$$
|\mathcal Q|\ \le\ (4b-2)h_\Gamma+1+
\frac{16\,b^2\,(a+1)(h_\Gamma+1)(h-1)+h\,n}{t-W+d}.
$$

*Proof of Corollary B from Theorem A.* If a section is not simple, $P$ is a
common root of $F(X,\gamma,Y)$ and $F_Y(X,\gamma,Y)$ over $k(X)$, so the
resultant $\operatorname{Res}_Y(F,F_Y)(X,\Gamma)$ vanishes identically at
$\Gamma=\gamma$. This resultant is nonzero because $F$ is irreducible and
separable in $Y$, and its degree in $\Gamma$ is at most $(2b-1)h_\Gamma$.
Together with $E_h$ at most $(4b-2)h_\Gamma+1$ scalars are excluded.

For a remaining $\sigma=(\gamma,P)$ split its agreement sites into four
classes. At a site which is not a core site,
$F(x,\Gamma,\ell_x(\Gamma))$ is a nonzero polynomial of degree at most $h$
vanishing at $\gamma$, so each such site serves at most $h$ sections. At a
core site which is not simple, $F_Y(x,\gamma,P(x))=v_x(\gamma)=0$ since
$v_x=0$; the nonzero polynomial $F_Y(X,\gamma,P(X))$ has degree at most $W-d$,
so each section meets at most $W-d$ such sites. At a simple core site with
$v_x(\gamma)=0$ at most $h-1$ sections are served. The remaining sites form
$J(\sigma)$. Summing, $\sum_\sigma|J(\sigma)|\ge N(t-W+d)-hn$, and Theorem A
gives the claim. $\qquad\blacksquare$

## The surface

Let $K$ be the fraction field of $k[X,\Gamma,Y]/(F)$ and let
$\nu:S'\to\mathbb P^1_X\times\mathbb P^1_\Gamma$ be the normalization of
$\mathbb P^1\times\mathbb P^1$ in $K$. It is finite of degree $b$ and
separable. Let $\pi:\widetilde S\to S'$ be the minimal resolution and
$\varphi=\nu\pi$, with projections $f_X,f_\Gamma:\widetilde S\to\mathbb P^1$
and fibre classes $\Phi_X,\Phi_\Gamma$. Then
$$
\Phi_X^2=\Phi_\Gamma^2=0,\qquad \Phi_X\cdot\Phi_\Gamma=b .
$$
On $S'$ we use Mumford's rational intersection pairing of Weil divisors,
$D\cdot D'=\pi^*D\cdot\pi^*D'$. Principal divisors are numerically trivial,
effective divisors without common components have nonnegative local and
global intersection numbers, and the projection formula holds for Cartier
divisors pulled back along $\nu$.

**Hodge index.** The intersection form on
$\operatorname{NS}(\widetilde S)_{\mathbb Q}$ has signature $(1,\rho-1)$. As
$\Phi_\Gamma$ is nef with $\Phi_\Gamma^2=0$, every class $T$ with
$T\cdot\Phi_\Gamma=0$ has $T^2\le0$, and for two such classes
$(T\cdot C)^2\le T^2\,C^2$. The same holds for Mumford's pairing on $S'$,
which embeds isometrically by $\pi^*$.

**Ramification.** The Jacobian of $\varphi$ defines an effective divisor $R$
with $K_{\widetilde S}\equiv-2\Phi_X-2\Phi_\Gamma+R$. Let
$\mathrm{Br}\subset\mathbb P^1\times\mathbb P^1$ be the reduced branch curve
of $\nu$. Ramification indices are at most $b<\operatorname{char}k$, so $\nu$
is tame, its ramification divisor is $R'=\sum(e_i-1)R_i'\le\nu^*\mathrm{Br}$,
and $R=\pi^*R'-Z$ with $Z\ge0$ supported on the exceptional curves. Hence
$$
R\ \le\ \varphi^*\mathrm{Br}. \tag{1}
$$
Over a point of the affine plane where
$\operatorname{Disc}_Y(F)\ne0$ the cover is étale. The discriminant has
degree at most $(2b-2)h_\Gamma$ in $\Gamma$ and $(2b-2)a$ in $X$. Counting
the lines at infinity, the numbers $\beta_X=\mathrm{Br}\cdot(\{x\}\times\mathbb P^1)$ and
$\beta_\Gamma=\mathrm{Br}\cdot(\mathbb P^1\times\{\gamma\})$ satisfy
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
This gives uniqueness, reducedness and the two intersection numbers.

Put $w=Y-\ell_x(\Gamma)\in K$. Write its divisor on $S'$ as
$\operatorname{div}(w)=j\Lambda_x'+V-P_w$ with $j\ge1$, $V\ge0$ not
containing $\Lambda_x'$, and $P_w\ge0$ the polar divisor. Intersecting with
$\Lambda_x'$ gives $j\,a_x'=V\cdot\Lambda_x'-P_w\cdot\Lambda_x'$.

Let $\Psi(X,\Gamma)=F(X,\Gamma,\ell_x(\Gamma))=(X-x)^\mu\Psi^\circ$ with
$\Psi^\circ(x,\Gamma)\ne0$. Taylor expansion in $Y$ at $\ell_x(\Gamma)$ gives
$\Psi=-w\,E$ on $S'$ with $E=\sum_{i\ge1}F^{[i]}w^{i-1}$ and
$F^{[i]}\in k[X,\Gamma]$. On any component $T$ of $V$ over the affine plane
$w$ and $E$ are regular at the generic point, so
$\operatorname{ord}_T\Psi\ge\operatorname{ord}_Tw$. No component of $V$ lies
over $\{x\}\times\mathbb P^1$: on such a component $w=0$, so it would map onto
$L_x$ and equal $\Lambda_x'$. Thus $X-x$ is a unit along $T$ and
$V\le\nu^*Z(\Psi^\circ)$ over the affine plane.

At the point $s_\infty$ of $\Lambda_x'$ over $\Gamma=\infty$ use
$\Gamma'=1/\Gamma$, $Y'=Y/\Gamma$ and $w'=\Gamma'w=Y'-u_1(x)-u_0(x)\Gamma'$.
The polynomial $\Gamma'^hF(X,1/\Gamma',Y'/\Gamma')$ has the same shape, and
the same argument bounds the zeros of $w'$ near $s_\infty$ by the pullback of
the homogenized curve. Since
$\operatorname{div}(w)=\operatorname{div}(w')-f_\Gamma^*(\infty)+f_\Gamma^*(0)$
and $f_\Gamma^*(\infty)\cdot\Lambda_x'=1$ is supported at $s_\infty$, summing
the local contributions gives
$$
j\,a_x'\ \le\ \nu^*\overline Z\cdot\Lambda_x'-1=\overline Z\cdot(\{x\}\times\mathbb P^1)-1=h-1,
$$
where $\overline Z$ is the divisor of the bihomogeneous form of
$\Gamma$-degree $h$ defined by $\Psi^\circ$. The polar terms only decrease
the right side. $\qquad\blacksquare$

**Lemma 2 (sections).** Let $\sigma=(\gamma,P)$ be a simple section. Its
graph has a strict transform $\widetilde C_\sigma\subset\widetilde S$, a
smooth rational curve in $f_\Gamma^{-1}(\gamma)$ with
$\widetilde C_\sigma\cdot\Phi_X=1$, $\widetilde C_\sigma\cdot\Phi_\Gamma=0$
and
$$
c_\sigma:=-\widetilde C_\sigma^{\,2}=R\cdot\widetilde C_\sigma .
$$
Its image $C_\sigma'\subset S'$ satisfies $-(C'_\sigma)^2\le c_\sigma$.
Sections with different scalars are disjoint. If $x\in J(\sigma)$ then
$C_\sigma'\cdot\Lambda_x'\ge1$.

*Proof.* The graph is generically étale over the plane, so it is not in the
singular locus and has a strict transform. The restriction of $f_X$ is finite
and birational onto $\mathbb P^1$, hence an isomorphism. Adjunction gives
$-2=\widetilde C^2+K\cdot\widetilde C=\widetilde C^2-2+R\cdot\widetilde C$.
Mumford's pullback is $\pi^*C'=\widetilde C+\sum\theta_iE_i$ with
$\theta_i\ge0$, so $(C')^2=\widetilde C^2+\sum\theta_iE_i\cdot\widetilde C\ge\widetilde C^2$.
At an ordinary incidence the point $(x,\gamma,\ell_x(\gamma))$ is a smooth
point at which the surface is étale over the plane, and the two curves
project to transversal lines. $\qquad\blacksquare$

**Lemma 3 (Bessel inequality).** For a simple section $\sigma$,
$$
c_\sigma\sum_{x\in J(\sigma)}a_x'\ \ge\ \Bigl(1-\frac1b\Bigr)^2|J(\sigma)|^2,
\qquad\text{hence}\qquad
c_\sigma\ \ge\ \Bigl(1-\frac1b\Bigr)^2\frac{|J(\sigma)|}{h-1}.
$$

*Proof.* Put $T=\sum_{x\in J(\sigma)}(\Lambda_x'-\tfrac1b\Phi_X)$. Then
$T\cdot\Phi_\Gamma=0=C_\sigma'\cdot\Phi_\Gamma$,
$T^2=-\sum a_x'$ and $T\cdot C_\sigma'\ge|J(\sigma)|(1-\tfrac1b)$. Apply
$(T\cdot C')^2\le T^2(C')^2$ and Lemmas 1 and 2. $\qquad\blacksquare$

**Lemma 4 (ramification budget).** For simple sections with pairwise
distinct scalars outside $E_h$,
$$
\sum_\sigma c_\sigma\ \le\ 4\,\beta_X\,\beta_\Gamma .
$$

*Proof.* Let $q\in\widetilde C_\sigma\cap\operatorname{Supp}R$ with image
$\mathrm{pt}$ on the line $\ell_\gamma=\mathbb P^1\times\{\gamma\}$. By (1)
and the isomorphism $\widetilde C_\sigma\to\ell_\gamma$,
$(R\cdot\widetilde C_\sigma)_q\le(\mathrm{Br}\cdot\ell_\gamma)_{\mathrm{pt}}$.

This local number is at least two. Otherwise $\mathrm{Br}$ is smooth at
$\mathrm{pt}$ and transversal to $\ell_\gamma$. By purity and Abhyankar's
lemma $S'$ is regular above $\mathrm{pt}$ and $\nu$ is, in formal
coordinates, $(u,z)\mapsto(u,z^e)$ with $e\ge2$ at the image of $q$. The
preimage of a line transversal to the branch divisor is a single smooth
branch of degree $e$ over it. A component mapping isomorphically to the line
cannot pass through such a point.

Therefore
$c_\sigma\le2\sum_{\mathrm{pt}}\bigl((\mathrm{Br}\cdot\ell_\gamma)_{\mathrm{pt}}-1\bigr)
=2\bigl(\beta_\Gamma-\#(\mathrm{Br}\cap\ell_\gamma)\bigr)$. Let
$\mathrm{Br}'$ be $\mathrm{Br}$ without its horizontal lines and
$\psi:\widetilde{\mathrm{Br}'}\to\mathbb P^1_\Gamma$ the projection of its
normalization. The deficiency of a line is at most the ramification of
$\psi$ above $\gamma$ plus $\sum(\text{branches}-1)$ over the singular points
of $\mathrm{Br}'$ on the line. Summing over $\gamma$, Riemann–Hurwitz on each
component, with $\psi$ separable because its degree is below the
characteristic, and $\sum(\text{branches}-1)\le\sum\delta$ give at most
$2p_a(\mathrm{Br}')+2\beta_\Gamma-2\le2\beta_X\beta_\Gamma$, since
$p_a(\mathrm{Br}')=(\beta_X'-1)(\beta_\Gamma-1)$. Distinct scalars use
distinct lines. $\qquad\blacksquare$

*Proof of Theorem A.* By Lemmas 3 and 4,
$\bigl(1-\tfrac1b\bigr)^2\sum_\sigma|J(\sigma)|\le(h-1)\sum_\sigma c_\sigma\le4(h-1)\beta_X\beta_\Gamma$,
and (2) bounds the two branch degrees. $\qquad\blacksquare$

## Sharpness checks

On the quartic del Pezzo surface with conic bundles $|H-E_1|$ and
$|2H-E_2-E_3-E_4-E_5|$ one has $b=2$, every line and every section is a
$(-1)$-curve, $R\cdot C=R\cdot\Lambda=1$, and each section meets one line at
each of the four sites. Lemma 3 reads $1\cdot4\ge(4\cdot\tfrac12)^2$, an
equality. The probe verifies the adjunction identities, Lemma 3 for all 128
choices, the pair inequality below and the budget.

For $F=Y^2-(X-\Gamma)^2-cG(X)H(\Gamma)$ with $\deg G=\kappa$,
$\deg H=\eta\ge2$, the lines $Y=\pm(x_i-\Gamma)$ at the roots of $G$ have
$a'=\eta-1=h-1$, attaining Lemma 1, and the sections $Y=\pm(X-\gamma_j)$ at
the roots of $H$ are each incident to all $\kappa$ lines of the same sign. The
total incidence $2\eta\kappa$ is linear in $a=\kappa$, as in Theorem A.

**A pair inequality.** The same computation with
$C_\sigma'-C_\tau'+\mu\bigl(\sum_{\Delta_1}\Lambda_x'-\sum_{\Delta_2}\Lambda_x'\bigr)$
for equinumerous $\Delta_1\subseteq J(\sigma)\setminus S(\tau)$ and
$\Delta_2\subseteq J(\tau)\setminus S(\sigma)$ gives
$$
\min\bigl(|J(\sigma)\setminus S(\tau)|,\ |J(\tau)\setminus S(\sigma)|\bigr)
\le\tfrac12(h-1)(c_\sigma+c_\tau).
$$
Two sections of small defect therefore have almost the same agreement set.

## The last second-prime predecessor

Let $n=2^{30}$, $d=2^{26}-1$, $t=357913943$. The first interpolant has value
degree at most four, total $(\Gamma,Y)$-degree at most $34$ and weight below
$t$, and every factor inherits these bounds. With $a\le t-1$,
$h_\Gamma\le h\le34$ and $t-W+d\ge d+1=2^{26}$, Corollary B gives

| Value degree | Bound using $a,W\le t-1$ | Bound using the actual factor weight | Population to exclude |
|---:|---:|---:|---:|
| 3 | 887,925 | 360,973 | 1,431,655,733 |
| 4 | 1,577,981 | 734,604 | 2,147,483,615 |

The third column substitutes $a\le W\le290805098$ for the cubic and
$a\le W\le302954072$ for the quartic. These weight bounds and the populations
to exclude come from the [formal factor reduction](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeQuadraticFactor.lean).
In both columns the exceptional allowances are 341 and 477 respectively.
The site allowance is $34n$ and the division uses the integer floor.
The population estimates depend on the written geometric bounds in Lemmas 1–4.

The characteristic condition is $p>6\cdot357913942+1$, which holds for both
named primes. Factors of value degree two are covered by the elementary
discriminant count already recorded. The value-linear factors and the count
on affine heads are unchanged.

## Actual ordinary incidences at the second prime

The [actual cubic incidence theorem](../../../ArkLib/Research/ProximityGap/Frontier/ActualCubicHodgeIncidences.lean) proves the exceptional-scalar and agreement estimates for the original received rows. The resultant of the cubic and its value derivative is nonzero and has scalar degree at most 161. Remove the scalar values where its whole specialization vanishes as a polynomial in the coordinate. Every remaining cubic fiber has degree three and is separable over $k(X)$.

For each retained section, remove agreements where its value derivative vanishes. The derivative on the section has coordinate degree at most $290805098-67108863=223696235$, leaving at least $134217708$ agreements. At each noncore site the received line meets the cubic at no more than 34 scalars. Every remaining pair is an ordinary incidence as defined above. In particular, a counterexample would produce at least $1431655572$ retained sections and at least **192,153,493,012,046,960** ordinary incidence pairs.

The named threshold now follows in Lean from a strict upper bound of **192,153,493,012,046,960** on those pairs. The surface-intersection and ramification estimates in Lemmas 1–4 are the remaining geometric inputs for this route.

## Scope and what remains

1. *First-order interpolants.* Every factor has weight below $t$, so
   $t-W+d>d$ and Corollary B applies with no further input. This covers
   rate $1/16$ through about $0.677n$ errors, rate $1/8$ through $0.5625n$
   and rate $1/4$ through $5n/12$.
2. *Higher multiplicity.* A simple factor of a multiplicity-$m$ interpolant
   may carry the received lines as $m$-fold components. Sections still cross
   only reduced fibre components of $S'$, and Lemma 3 extends to them with
   weight $(1-\lambda/b)$, where $\lambda$ is the degree of the component
   over the vertical line. Sites at which the whole fibre is one reduced
   curve of degree $b$ over the received line carry no information in
   $\operatorname{NS}$. Bounding the incidences at these sites is the missing
   step for factors of weight at least $t+d$.
3. *Characteristic.* Tameness and separability are used in (1), in
   Abhyankar's lemma and in Riemann–Hurwitz. Additive constructions in
   characteristic two violate the conclusion, as they must.
