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
