# Three collinear heads and an interpolated fourth on a smooth domain

For the second named prime at length $n=2^{30}$ the first failing error count is at most **679477249** at rate one eighth and **565631854** at rate one quarter. These improve the arbitrary-domain exceptional-head bounds by 25165823 and 38347922 errors respectively. Lean verifies both attacks on the named power domain at every positive interleaving width. The eighth-rate mass holds for dimensions 134,217,728 through 394,264,574, and the quarter-rate mass for dimensions 268,435,456 through 508,109,969. [Formal four-head attack](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeFourHeadEndpoints.lean)

## An upper bound across lengths and field budgets

Write $n=16s$ at rate one quarter and $n=32s$ at rate one eighth, with $s\ge2$. Let $B=\lfloor |F|/2^{128}\rfloor$ and assume $0<B\le4n-28s+7$ and $n\le2^{62}$. For any field with a multiplicative element $g$ of order $n$, and every nonzero coset representative $c$, use the domain $cg^i$. Set
\[
 C=\min\left(\left\lfloor\frac{n+15s-6}{4}\right\rfloor,
             \left\lfloor\frac{4n+21s-7-B}{7}\right\rfloor\right).
\]
The MCA test fails by **$n-C-1$ errors**, so the operational supremum is at most $(n-C-1)/n$, at every positive interleaving width. A single received pair supplies at least $4n+21s-7C-6$ bad labels. The formula gives the largest core that both fits this allocation and produces a count strictly above the budget. A positive budget makes the field large enough to separate all projected labels in this length range. [Uniform finite-field proof](../../../ArkLib/Research/ProximityGap/Frontier/SmoothCosetFourHeadMass.lean)

The polynomial identity behind the three fibers uses only $w^8=-1$ for a primitive sixteenth root $w$. If $L_{abc}(t)=(t-w^a)(t-w^b)(t-w^c)$, then
\[
 L_{0,1,8}(t)-w^2L_{2,9,10}(t)=(1-w^2)L_{3,5,7}(t).
\]
Consequently the three difference polynomials have exactly the prescribed roots in every eligible field. Substituting $(X/c)^s$ pulls the root sets back to the coset. [Integral identity and coset evaluation](../../../ArkLib/Research/ProximityGap/Frontier/SmoothCosetCubicSeed.lean)

## Three pairwise coincidence sets

Let $k$ be the dimension, $s=k/4$, and $D=3s$. The evaluation domain is the multiplicative group of all $n$th roots. Its image under $X\mapsto X^s$ contains the group of sixteenth roots at both rates. Let $w$ have order 16. On this group take exponent triples
\[
 A=(0,1,8),\quad B=(2,9,10),\quad C=(3,5,7).
\]
Set $g_1=0$, $g_2=L_A$, $g_3=L_B L_A(w^3)/L_B(w^3)$, where $L_A,L_B$ are the corresponding monic cubic root locators. The cubic pencil identity gives $g_2=g_3$ on $C$. Since the three exponent sets are disjoint and all difference polynomials have degree at most three, the three pairwise coincidence sets are precisely those triples and have no triple coincidence. The identity holds in the cyclotomic ring and the named prime has the required root of order 16. [Cubic identity](quarter-three-heads-32-fibers.md#attainment) · [Integral check](../../../scripts/probes/probe_quarter_three_heads_32.py)

After substituting $X^s$, each pair coincidence occupies exactly $D$ sites. Choose $G=k-2-D$ additional sites away from these three blocks, with locator $J$. Set $f_i=Jg_i(X^s)$ and use the first three heads
\[
 W_i=(X f_i,f_i).
\]
The head entries have degrees below $k$. All three coincide at the $G$ extra roots. The pair coincidences outside these roots are unchanged.

## Allocating four defining cores

Choose a target core size $C_0\ge k$ and put $S=k-2$, $p_0=C_0-G-2D$. Receive the common head at the $G$ sites and the repeated head on the $3D$ pair sites. Assign $p_0$ distinct remaining sites to each of the three heads and receive that head there. The triple-owned union then has size
\[
 U=G+3D+3p_0=3C_0-3D-2G .
\]
Each of the three defining cores has exactly $C_0$ sites. Pick $S$ sites anywhere in this union for the fourth head to match, call this set $V$, and interpolate its two entries $A_0,B_0$ there with degrees below $S$. For the locator $L$ of $V$, put
\[
 B_4=B_0+bL,\qquad A_4=A_0+L(a+cX).
\]
Every choice has degrees below $k$. Outside the triple-owned union put the received pair equal to $(A_4,B_4)$ on $q_0=C_0-S$ sites. There are $H=n-U-q_0$ leftover sites. Thus the fourth head also has a defining core of $C_0$ sites. All allocation sizes are nonnegative in the two instances below.

At a triple-owned site $x$ outside the $G$ common roots one can choose a mismatching triple head and obtain its fresh label $-x$. These $U-G$ labels are distinct.

At each of the $U-S$ triple-owned sites outside $V$, use its received triple head and make head 4 the fresh mismatching head. At each of the $q_0$ sites occupied solely by head 4, use all three triple heads as the fresh mismatching heads. At any such site the label from a pair $(4,i)$ is
\[
 z_i(x)=\frac{A_0(x)-x f_i(x)+L(x)(a+c x)}{f_i(x)-B_4(x)}.
\]
First choose $b$ so that $B_4(x)$ differs from all three $f_i(x)$ outside $V$, including at leftover sites. At most $3n$ values are excluded because $L(x)\ne0$. The coefficient pair of the displayed affine function of $(a,c)$ is a nonzero multiple of $(1,x)$. Thus functions from different sites have different coefficient pairs. At a $q_0$ site, the three $f_i(x)$ are distinct, so the three coefficient pairs at that site are also different. Each pair of functions can agree on at most one proper affine line of choices of $(a,c)$, as can a function and any of the fixed previous labels $-x$. There are fewer than $(4n)^2$ such lines, below the field size. Choose $(a,c)$ avoiding them simultaneously.

Finally, at each of the $H$ leftover sites the four second entries $f_1(x),f_2(x),f_3(x),B_4(x)$ are pairwise distinct. Take a received second entry different from all four. The four potential new labels are then affine functions of the received first entry with nonzero, pairwise distinct slopes. At most $16n+6$ choices cause a collision with each other or with an earlier label. The field size exceeds this bound, so all four fresh labels can be added at each such site.

Each selected label agrees with its folded head on its $C_0$ defining sites and at its fresh site, with a second-row mismatch at that fresh site. A joint explanation of the whole support would equal the original two polynomial entries on the defining sites, and therefore everywhere since $C_0\ge k$. Thus every label is literally MCA-bad at $e=n-C_0-1$.

## Exact counts

The single received pair has at least
\[
 M=(U-G)+(U-S)+3q_0+4H=4n-7C_0+6D+3G
\]
distinct bad labels. The packing and budget conditions give the choice
\[
 C_0=\min\!\left(\left\lfloor\frac{n+2G+3D+S}{4}\right\rfloor,
                    \left\lfloor\frac{2n+6D+3G-1}{7}\right\rfloor\right).
\]

| Rate | Core size $C_0$ | Private sites per triple head | Fourth-only sites | Leftovers | Error count | Bad labels |
|---|---:|---:|---:|---:|---:|---:|
| $1/8$ | 394264574 | 159383552 | 260046848 | 2 | 679477249 | 2239758344 |
| $1/4$ | 508109969 | 38347923 | 239674515 | 47934902 | 565631854 | 2147483651 |

The named field's bad-count budget is $2147483648$. These are upper bounds. The unrestricted first failing count at either rate and the best arbitrary four-head construction remain open. [Named arithmetic and literal small-domain verification](../../../scripts/probes/probe_smooth_four_head_attack.py) · [General four-head lower barrier](four-arbitrary-head-cap.md)
