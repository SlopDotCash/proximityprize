# Restricted second-order interpolation at half rate

Take a prescribed injection of the evaluation sites into a prime field of order
$p$. Let $n,k,A,m$ denote its length, message dimension, agreement threshold,
and interpolation multiplicity. Write $D=k-1$. Use the source columns

$$
X^aY_0^{b_0}Y_1^{b_1}Y_2^{b_2},\qquad
t=b_0+b_1+b_2,\quad a+Dt<mA,\quad j=b_1+2b_2\le W .
$$

These are precisely the canonical partition-support exponents at the real
cutoff $mA$. Translation of $X$ and $Y_0$ preserves both inequalities. Their
number is
$$
N=\sum_{t=0}^{v} P(t,W+1)(mA-Dt),\qquad v=\lfloor(mA-1)/D\rfloor ,
$$
where $P(t,L)$ counts nonnegative pairs $(u,b)$ with $u+b\le t$ and
$u+2b<L$. With a fixed $s=u+2b$, one can choose any integer
$\max(0,s-t)\le b\le\lfloor s/2\rfloor$. This yields a direct sum or a
closed prefix count. For $0\le L\le t+1$ it equals
$\lfloor(L+1)^2/4\rfloor$. For $t+1<L\le 2t$ reflect the degree triple
$(t-u-b,u,b)$ to $(b,u,t-u-b)$, which replaces the weight by $2t-s$.
This gives $P(t,L)=\binom{t+2}{2}-\lfloor(2t-L+2)^2/4\rfloor$. For $L>2t$
it is $\binom{t+2}{2}$. Use $P(t,L)=0$ for $L<0$.

## The rank of the origin matrix

At the translated origin a target monomial is
$T^hE^eY_1^{c_1}Y_2^{c_2}$. The independent homogeneous gradings give
$$
t=e+c_1+c_2,\qquad
h+e+c_1=a+2t-j.
$$
After eliminating $c_1$, its contact order is
$i=h+2e=a-j+t+c_2+2e$. The local constraints retain exactly $i<m$.
Index each block by $(t,z)$ with $z=a+W-j\ge0$ and set $s=c_2+2e$.
Every nonzero coefficient satisfies $i+W=z+t+s$, hence $z<W+m$.
With $t,z$ fixed, $(c_2,e)$ determines $c_1$ and $h$. The admissible
$s$ lie in $[W-z-t,W+m-z-t)$. There are at most
$$
R_{t,z}=P(t,W+m-z-t)-P(t,W-z-t)
$$
different target rows. Likewise $(b_1,b_2)$ determines $a=z+j-W$ and
$b_0=t-b_1-b_2$. Necessarily $W-z\le j\le W$, so there are at most
$$
S_{t,z}=P(t,W+1)-P(t,W-z)
$$
source columns. Select the smaller side of each rectangular block to cover
all nonzero entries. The rank of one local matrix is at most
$$
r_0=\sum_{t=0}^{v}\sum_{z=0}^{W+m-1}\min(R_{t,z},S_{t,z}).
$$
Translation transports this bound to all evaluation sites and all received
values. Base change to the rational-function field preserves the upper
bound. Stacking the $n$ sites costs at most $r=nr_0$. When $r<N$, the
canonical primitive interpolation construction has challenge height at most
$H=\lfloor rv/(N-r)\rfloor$ at curve degree one.

## Finite field budgets

At capacity slack $g=(A-k)/n$, the canonical order-two exceptional charge is
$n^3[H+4v^4g^{-2}(33H/g+3)]$. The origin bound, source cardinality,
height and finite-field comparisons give the following figures.

| $n$ | $k$ | $A$ | $m$ | $W$ | $N$ | $r_0$ | $v$ | $H$ | Errors |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1,024 | 512 | 700 | 112 | 49 | 2,799,856,150 | 2,732,779 | 153 | 287,261 | 324 |
| 262,144 | 131,072 | 180,224 | 54 | 23 | 41,164,959,316 | 156,586 | 74 | 25,988 | 81,920 |
| 262,144 | 131,072 | 180,160 | 58 | 25 | 55,063,229,494 | 209,400 | 79 | 25,467 | 81,984 |

All three exceptional charges times $2^{128}$ are at most the named 237-bit
witness prime. In the last row the ceiling of the required field size is
122239999054400338719359108276973937911241042922169913105319470914634302.
The absolute heights here come from the challenge-degree rank argument on the
entire prescribed domain. The first row advances the half-rate length-1024
first-order count by six errors.

Lean verifies the actual origin gradings, the exact cardinality of each
derivative-weight interval, and the corresponding bound on the full
origin matrix. An explicit injection gives the source dimensional lower
bound. Transport to the symbolic coefficient field followed by uniform
base-field recovery proves the literal worst-pair sponsor MCA bound at
all three closed radii. The integer replay independently enumerates the
same source and target slices.

[Graded matrix theorem](../../../ArkLib/Research/ProximityGap/Frontier/HigherJetBigrading.lean) ·
[Origin rank and certificates](../../../ArkLib/Research/ProximityGap/Frontier/PartitionOriginCertificate.lean) ·
[Exact interval counts](../../../ArkLib/Research/ProximityGap/Frontier/SecondOrderBlockCounts.lean) ·
[Rank and column count](../../../ArkLib/Research/ProximityGap/Frontier/SecondOrderOriginBlocks.lean) ·
[Closed sponsor MCA cutoffs](../../../ArkLib/Research/ProximityGap/Frontier/SecondOrderPrimeFieldCuts.lean) ·
[Integer replay](../../../scripts/probes/probe_second_order_mca_budgets.py)

## Four rates at every scaled block length

Using coarse degree $D=bk_0$ at $n=4096b$ gives $b$ times the original
width for every jet partition. The total rank and source dimension scale
by the same $b$, so the jet cap and height are constant. For any positive
integer $b$ the following field requirement suffices at the indicated
closed radius, for every prescribed domain and every received pair:
$p\ge 2^{128} C n^3$.

| Rate | Errors per 4096 sites | $m$ | $W$ | $v$ | $H$ | $C$ |
|---:|---:|---:|---:|---:|---:|---:|
| 1/2 | 1281 | 58 | 25 | 79 | 25,551 | 20,007,104,463,588,681 |
| 1/4 | 2203 | 51 | 31 | 94 | 15,936 | 17,198,307,386,709,643 |
| 1/8 | 2817 | 40 | 30 | 99 | 10,341 | 19,969,708,005,140,362 |
| 1/16 | 3221 | 28 | 25 | 95 | 6,080 | 18,940,036,421,599,633 |

The named 237-bit prime satisfies all four requirements through $b=64$.
The scalars, agreement sets, and worst-case sponsor errors all belong to
the same base field. [Scaled four-rate proof](../../../ArkLib/Research/ProximityGap/Frontier/ScaledSecondOrderPrimeCuts.lean)

## BLS production length

For $n=2^{30}$, $k=2^{26}$, and $A=233308160$, use $m=20$, $W=17$,
$v=69$. The origin rank is at most 10432 and there are at least
11478667313970 source columns. The challenge height is at most 2786.
In the exact dimension-sensitive regular-stage theorem choose the
intermediate agreement cutoff $L=77413220$ and Taylor exponent $2k$.
All three possible differential orders have regular-stage charge at
most 2233263588724038498968437022129007560. There are at most 69 stages
and the terminal contribution is at most 2786. Lean verifies that their
sum fits $\lfloor p/2^{128}\rfloor$ for the BLS12-381 scalar prime.
Thus the closed radius $3206/4096$ is safe on every such domain, an
increase of 1048576 errors over $3202/4096$.
[Exact production-field recovery and sponsor bound](../../../ArkLib/Research/ProximityGap/Frontier/SecondOrderSharpProduction.lean)

## Charging each differential degree once

At Taylor exponent $\tau=2k$ the jet-degree side of the mixed-degree
rectangle for a stage of positive total degree $t$ is
$1+\tau(t-1)\le\tau t$. Its challenge-degree side is at most
$1+\tau H$. In order $r$ the mixed intersection term is therefore at
most
$$
\bigl(H\tau^{r+1}+(r+1)(1+\tau H)\tau^r\bigr)t^{r+1}.
$$
The evaluation term is at most $(n-L)\tau^r t^{r+1}$ times its incidence
factor. Keep the exact two incidence products at thresholds $A$ and
$L$. Bound the resulting rational coefficients for $r=0,1,2$ by one
integer $C$. Since $t\ge1$, every stage has charge at most $Ct^3$.

The degree-charge theorem in Lean applies at every derivative order $d$. One may bound each distinct positive stage degree $t$ by $Ct^{d+1}$ with the same incidence coefficients and sum over $1\le t\le v$.

Each canonical separant step strictly lowers total jet degree. Consequently
the exceptional count is at most $H+C\sum_{t=1}^v t^3$, including the
terminal specialization. The following production profiles have this
quantity at most $\lfloor p/2^{128}\rfloor$ for the BLS scalar prime.
The height and local-rank hypotheses come from the same canonical
partition support used above.

| Rate | Errors per 4096 | $m$ | $W$ | $v$ | $H$ | $L$ | Rank per site |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1/4 | 2176 | 25 | 15 | 46 | 4619 | 277595815 | 14274 |
| 1/8 | 2800 | 26 | 19 | 65 | 4164 | 143877210 | 21972 |
| 1/16 | 3216 | 24 | 21 | 82 | 5071 | 75451334 | 21426 |

These are closed error radii on every prescribed length-$2^{30}$ domain.
The gains over the earlier first-order bounds are one, eleven, and fourteen
units of $1/4096$. [Lean exact recovery and sponsor probability](../../../ArkLib/Research/ProximityGap/Frontier/StratifiedSecondOrderProduction.lean)

## Complete lists at every interleaving width

For a constant received curve the primitive kernel certificate has
challenge height zero. A strict surplus of source columns therefore
suffices without a bound on the reciprocal surplus. The canonical
direct-jet estimate on a received word at agreement $A$ and order
two is
$$
v^2\left(\frac{n(1+2k(v-1))}{A-k+1}\right)^2.
$$
Applying it over the rational-function extension also bounds the lists
of every finite interleaving width over the original field. For each
positive $b$ and each prime field admitting the $n=4096b$ prescribed sites,
the closed balls in the following table have at most $C n^2$ codewords.

| Rate | Errors per 4096 | $m$ | $W$ | $v$ | $C$ |
|---:|---:|---:|---:|---:|---:|
| 1/2 | 1293 | 107 | 45 | 146 | 13,190,740,336 |
| 1/4 | 2220 | 107 | 67 | 196 | 8,440,423,840 |
| 1/8 | 2838 | 99 | 74 | 243 | 6,515,819,463 |
| 1/16 | 3245 | 72 | 63 | 239 | 2,395,867,711 |

Every displayed factor is less than $2^{34}$. At length $2^{30}$,
$p\ge2^{222}$ therefore ensures that the list fits the integer budget
$\lfloor p/2^{128}\rfloor$ at all four radii.
[All-width and production-budget proofs](../../../ArkLib/Research/ProximityGap/Frontier/SecondOrderAllWidthLists.lean)
