# Rate-eighth safety at 656,056,254 errors

Let $n=2^{30}$, $k=n/8$, $d=k-1$. On any injective length-$n$ evaluation domain over a finite field of characteristic $p>3n^2$, every received pair has at most **2,058,198,009** MCA-bad labels at **656,056,254 errors**. At the second designated prime the integer budget is $2n=2,147,483,648$. Its first failing error count is consequently at least **656,056,255**. This improves the earlier written lower bound of 637,534,204 by 18,522,051 steps. The proof uses the previously written Jacobian-power interpolation argument and exact finite arithmetic. [Earlier window](rate-eighth-three-head-window.md) · [Arithmetic checker](../../../scripts/probes/probe_rate_eighth_terminal_new_floor.py)

## Interpolation and the component estimates

Set $t=417685570$, $e=n-t$. Choose a degree-at-most-$d$ witnessing polynomial $q_z$ for each bad scalar $z$. A multiplicity-$l$ interpolant of ordinate degree at most $b_0$, total scalar-ordinate degree at most $h$, and coordinate weight below $lt$ exists whenever

$$
 \sum_{j=0}^{b_0}(h-j+1)(lt-jd)_+
 > n\sum_{j=0}^{l-1}(l-j)(h-j+1).
$$

Each witness lies on this interpolant because specialization gives at least $t$ roots of multiplicity $l$ and strict degree below $lt$. The inequality holds for both $(l,b_0,h)=(3,8,4170)$ and $(4,12,63)$. Use the first interpolant for the cover. Its vertical factors contribute at most 4170 labels. Its other distinct irreducible factors have summed ordinate degree at most eight. Any such factor carrying more than $4170\cdot63$ labels also divides the second interpolant by plane Bézout over the coordinate function field. Its primitive representative then has total scalar-ordinate degree $m\le63$ and coordinate weight $bd\le W\le W_*=3t-1$, with $b$ its ordinate degree.

A value-linear factor carrying more than $4170\cdot63$ labels is a genuine affine head. Indeed select 4096 witnesses. The number of received identity sites is at least $I=(4096t-63n)/(4096-63)$, and at each such site at most 62 selected sections miss the received value. Among the 64 witnesses with the fewest misses, each misses at most $62I_{\rm actual}/(4096-63)$ identity sites. Every three therefore agree on the received affine rows at more than $d$ common sites, as $I(1-3\cdot62/(4096-63))>d$. Their three scalar and witness pairs are collinear over the coordinate function field, by the degree bound on their affine determinant. The common secant of these 64 witnesses divides the factor. Its two head polynomials have degrees at most $d$, being linear combinations of two witnesses.

For $2\le b\le8$, take the simple-section coordinate chart of the [ordinary-polar argument](second-prime-persistent-singularities.md). It puts $J=W-d$ derivative intersections on each simple section. At most $(2b-1)m-b^2$ sections are nonsimple. If the implicit scalar second derivative vanishes identically, the bounded-height constant-derivative argument forces a scalar-affine head after constant extension. Each such line can contain at most one selected point, since two selected points define it over the original coordinate function field and would contradict irreducibility with $b\ge2$. All scalar heights needed for that argument are at most $b(m+1)+bm<p$. [Vanishing Hessian](second-prime-quartic-intrinsic.md)

In the proper Hessian case write $R$ for the sum of the local orders at the received ordinates and $g$ for the generic ordinary-polar intersection sum. The previously derived inequality is

$$
 5R\le 2n+(18b-7)W-(9b^2-b)d-8g.
$$

Its branch proof extends to $b=7,8$. Every ramification index $e_P$ is at most $b<p$. At a singular branch of multiplicity $\sigma$, the first-polar order $\nu$ is at least $\sigma(\sigma-1)$. At $\sigma=2$ it is at least three, by the repeated tangent when the full point multiplicity also equals two. When $e_P=\sigma\ge2$, removing the constant and the degree-$e_P$ term gives Hessian order at least $3\nu+1-e_P\ge8\nu/3$. When $e_P>\sigma$ the bound is $3\nu+e_P-2\sigma\ge8\nu/3$, using $\nu\ge3(\sigma-1)$ if $\sigma\ge2$. The regular branches with $e_P=1$, the reciprocal-ordinate calculation at infinity, and the extra received-site charge do not depend on the upper bound six. The relevant coordinate degrees and polar intersection bounds are smaller than $p$. [Local computations](rate-eighth-three-head-window.md#large-polar-count)

For each $b$ choose Jacobian exponent $a$, received jet order $\mu$, and scalar cap $s$ from the table. The last column includes the low-population Bézout alternative and the nonsimple sections.

| $b$ | $a$ | $\mu$ | $s$ | Maximum labels |
|---:|---:|---:|---:|---:|
| 2 | 12 | 1024 | 20000000 | 40200718 |
| 3 | 7 | 256 | 8000000 | 24050148 |
| 4 | 6 | 512 | 8000000 | 32100359 |
| 5 | 7 | 128 | 18000000 | 90025074 |
| 6 | 8 | 128 | 34000000 | 204025074 |
| 7 | 10 | 128 | 81000000 | 567025074 |
| 8 | 12 | 1024 | 168000000 | 1344200718 |

The numerical tests use $\eta=(W^2/(2d)+n)/a$. If $g\ge JW/d-\eta$, then $tW/d-R$ is bounded below by the minimum $\Delta$ on $bd\le x\le W_*$ of

$$
 \frac15\left[(8-4/a)x^2/d+(5t/d-18b-1)x
             +(9b^2-b)d-(2+8/a)n\right].
$$

Let $j=\lfloor(\mu t-1)/d\rfloor$. The exact check

$$
 (s-j+1)(\mu\Delta-W_*^2/(2d))>
 j\mu bn+63n\binom{\mu+1}{2}
$$

produces a nonmultiple auxiliary of weight below $\mu t$ using received jet multipliers. Its resultant supports at most $bs+63j$ labels. This calculation minimizes the convex quadratic at its vertex clipped to the entire interval. [Jet dimension argument](rate-eighth-three-head-window.md#large-polar-count)

If $g<JW/d-\eta$, let $H=126b-b^2$, $D_*=2bW_*-b^2d-b$, $y=\lceil a(W_*-d)/d\rceil$, $v=\max(ba+b-1,y)$. The strict check $(s+1)n>aH(v+1)a(D_*+W_*)$ gives a nonmultiple auxiliary of weight below $aJ$ from the Jacobian-power matrix. Its generic codimension is at most $ag$, and the surplus before scalar interpolation exceeds $a\eta-W^2/(2d)=n$. Its simple sections number at most $bs+63y$. Adding the nonsimple exceptions gives the table. The matrix proof only requires $v\ge ba+b-1$ and the finite projective ordinate algebra has length $b$, also for $b=7,8$. [Jacobian-power matrix](second-prime-terminal-cubic.md#a-finite-polynomial-matrix-for-powers-of-the-jacobian-ideal)

## Counting the remaining affine heads

Call a head large if it carries more than $L=1+\lfloor e/512\rfloor=1281360$ selected points. Every other value-linear component carries at most $L$. A large head with core of size $c<t$ has $(L_{\rm actual}-1)(t-c)\le e$, since fresh agreement sites on distinct labels are disjoint. Thus each large core has at least $C=t-511$ sites. Any head carries at most $e+1$ bad labels.

Four heads containing a noncollinear triple have summed core size at most $n+4d$, by the four-head determinant bound. Here $4C>n+4d$. Consequently if there are $j\ge4$ large heads, all of them are collinear over the coordinate function field. If $V$ sites belong to their core union, Cauchy–Schwarz on the site occupancies and pairwise overlaps at most $d$ give $V\ge\lceil jC^2/(C+(j-1)d)\rceil$. An owned site gives at most one fresh label to the collinear group, while an unowned site gives at most $j$. Its contribution is at most $jn-(j-1)V$. For $j\le3$ allow $j(e+1)$ labels. [Four-head incidence bound](four-arbitrary-head-cap.md#core-multiplicity)

Allocate the remaining $8-j$ ordinate degree units among the nonlarge components using their individual bounds from the table and $L$ for degree one. The largest total, including the 4170 vertical labels, is 2,058,198,009 at $j=3$. All arithmetic uses exact integers or rational numbers. [Finite certificate](../../../scripts/probes/probe_rate_eighth_terminal_new_floor.py)
