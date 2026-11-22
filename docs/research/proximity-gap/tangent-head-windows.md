# Tangent-head factor caps for three second-prime MCA bounds

At length $n=2^{30}$, on every injective evaluation domain in the second named
prime field, the following error counts are safe at tolerance $2^{-128}$. The
integer budget is $2n=2{,}147{,}483{,}648$, and the statement holds at every
positive interleaving width by the MCA stability theorem.

| Rate | Safe errors | Upper bound on bad labels | Lower bound on first failing count | Previous written bound |
|---|---:|---:|---:|---:|
| $1/2$ | 306,780,000 | 2,140,552,088 | **306,780,001** | 301,600,001 |
| $1/4$ | 524,700,000 | 2,145,778,288 | **524,700,001** | 517,600,001 |
| $1/8$ | 671,088,385 | 2,047,343,878 | **671,088,386** | 667,400,001 |

**Status.** Written proof. The allocation argument is the one of the
[weighted windows](weighted-hodge-windows.md), unchanged. The single new
ingredient is the population cap for a nonlinear factor, which is Theorem D′ of
the [section-incidence note](section-incidence-hodge-index.md#a-second-route-below-the-johnson-radius-tangent-heads).
That theorem uses the normalization and the ramification budget of the same
note and does not use the Hodge index theorem. The
[exact-arithmetic certificate](../../../scripts/probes/probe_tangent_head_windows.py)
checks both interpolants, the head tests and every degree allocation in each
window, and reproduces the three committed weighted totals as a regression
test. Lean constructs both interpolants on the received rows in each window
and checks the Johnson-type conditions, the rich-head determinant tests and
every degree allocation, in
[TangentHeadWindows.lean](../../../ArkLib/Research/ProximityGap/Frontier/TangentHeadWindows.lean).
The counting half of Theorem D′ is kernel-checked in
[TangentHeadCount.lean](../../../ArkLib/Research/ProximityGap/Frontier/TangentHeadCount.lean):
from rational tangent data of total height at most $C'$ that take the received
values on the regular agreements, with at most $m$ sections on any affine
head, Lean derives $M(t^2-nd)\le2t(mn+C')+n(mn+2C')$. The geometric half,
which produces that data on the normalized cover, is a written argument. In
the window certificate the cap enters as the definition of a price.

## The cap

Use the notation of the weighted windows. Let $F$ be an irreducible factor of
value degree $b\ge2$, total scalar/value degree at most $m$ and
coordinate/value weight at most $W$, over an algebraically closed field of
characteristic zero or greater than $\max(b,B_Z)$, with
$$
B_X=(2b-2)m-b(b-1)+1,\qquad B_Z=(2b-2)W-b(b-1)d+1 .
$$
Let $M$ scalar labels carry polynomial sections of degree at most $d$ on $F$,
each agreeing with the received lines at $t$ or more of the $n$ sites. If
$t^2>nd$, then
$$
M\ \le\ B_X+\left\lfloor\frac{m\,n\,(2t+n)+2C'(t+n)}{t^2-nd}\right\rfloor,
\qquad C'=2B_XB_Z+b\bigl(W(m-b)+m(W-bd)\bigr). \tag{1}
$$

At the second-prime half- and quarter-rate Johnson comparisons the decisive Hamming counts are $g=314491699$ and $536870913$. For $t=n-g$ the two strict inequalities $(t-1)^2<nd<t^2$ put $nJ$ between $g$ and $g+1$. Safety at $g$ gives a supremum strictly above $J$, and failure puts it strictly below $J$. For any nonlinear factor $m\ge2$, the right-hand side of (1) is at least $\lfloor 2n(2t+n)/(t^2-nd)\rfloor$. The denominators are $1082833961$ and $1$, giving lower bounds on that allowance of **5140952044** and **4611686014132420608**. Both exceed the budget $2147483648$ before counting any other factor. A proof of safety using (1) alone would therefore need to exclude all such factors or sharpen the estimate for the ones that actually occur.

The proof is in the section-incidence note. Each retained section $(z,q_z)$
has a rational *tangent head* $(R_z,V_z)$ with
$V_z=-F_Z(X,z,q_z)/F_Y(X,z,q_z)$ and $R_z=q_z-zV_z$. The pair takes the
received values at every agreement where the section crosses the received line
at an étale point of the normalization, whatever the multiplicity of the
factor along that line. Its denominator has degree at most $c_z$, and
$\sum_zc_z\le C'$: the first term of $C'$ is the horizontal ramification
budget $2B_XB_Z$, and the second counts the blow-ups that make $(X,Y)$ a
morphism to the Hirzebruch surface. Two sections with different tangent heads
share at most $d+c_z+c_{z'}$ such agreements. Sections with the same tangent
head lie on one affine head, at most $m$ of them. The second-moment count over
the sites gives (1).

Inequality (1) has denominator $t^2-nd$ and numerator of order $b^2mW$. The
weighted variance cap has denominator of order $t-d$ and numerator of order
$b^3m^2W$. At the three committed weighted windows and the top value degree
$b=9,11,12$ the two caps are

| Rate | value degree | weighted variance cap | cap (1) |
|---|---:|---:|---:|
| $1/2$ | 9 | 2,128,363,411 | 26,072,926 |
| $1/4$ | 11 | 1,692,000,259 | 21,407,538 |
| $1/8$ | 12 | 494,981,025 | 8,552,097 |

## The windows

Each row lists the two mixed Hasse interpolants as $(r,v,s)$: order $r$,
value degree at most $v$, total scalar/value degree at most $s$, weight below
$rt$. The surpluses are the monomial counts minus the mixed jet conditions.
The cutoff is $\max(1+\lfloor e/256\rfloor,\,1+sv'+va)$, above which a factor
divides both interpolants.

| Rate | $e$ | First shape | Second shape | Surpluses | Cutoff |
|---|---:|---|---|---|---:|
| $1/2$ | 306,780,000 | $(14,19,238338)$ | $(27,38,412)$ | 139,540 and 634,918,502 | 9,064,673 |
| $1/4$ | 524,700,000 | $(11,22,2159)$ | $(21,42,353)$ | 86,458,493 and 5,032,628,125 | 2,049,610 |
| $1/8$ | 671,088,385 | $(6,16,335)$ | $(9,26,128)$ | 8,575,480 and 812,533,386 | 2,621,440 |

For $j$ rich affine heads and a nonlinear factor of value degree $b$ among
factors of total value degree $\ell$, the cap (1) is applied with
$W=rt-1-(\ell-b)d$ and $m=a-j$, where $a$ is the total degree of the second
shape. Rich heads are counted as before: $j(e+1)$ labels, and
$jn-(j-1)|U|$ for $j$ collinear heads whose cores cover $U$. For fixed $j$ and
fixed $\ell$ the caps depend only on $b$, so the largest allocation is found
by a dynamic programme over the remaining value degree. The certificate
checks this programme against direct enumeration on the committed windows.

| Rate | Largest allocation | Rich-head labels | Nonlinear cap | Total |
|---|---|---:|---:|---:|
| $1/2$ | four rich heads and one factor of value degree 15 | 1,227,120,004 | 913,432,084 | 2,140,552,088 |
| $1/4$ | three rich heads and one factor of value degree 19 | 1,555,640,166 | 590,138,122 | 2,145,778,288 |
| $1/8$ | three rich heads and thirteen linear factors at the cutoff | 2,013,265,158 | none | 2,047,343,878 |

Safety at a given error count gives safety at every smaller one.

## What ends each window

At half and quarter rate the binding allocation is a single nonlinear factor
of high value degree next to the rich heads. At the two windows
$t^2-nd$ is $0.0102\,n^2$ and $0.0115\,n^2$. The Johnson steps, where
$t^2\le nd$ first holds, are 314,491,700 and 536,870,914 errors. Cap (1)
grows like $b^2mW/(t^2-nd)$ while the value degree needed for an interpolant
grows, so this method stops well before those steps. The search over shapes
was a heuristic grid, and nearby shapes may certify slightly more.

At eighth rate the binding allocation is far below the budget. The window
ends because at 671,088,386 errors the test $4C>n+4d$ fails for
$C=t-255$: four rich heads need no longer contain a collinear triple, and the
head count used here does not cover that case. Extending this window needs a
label bound for four rich heads without the determinant test. The known
failure is at 679,477,249 errors.

## Reproduce

```bash
python3 -O scripts/probes/probe_tangent_head_windows.py
```
