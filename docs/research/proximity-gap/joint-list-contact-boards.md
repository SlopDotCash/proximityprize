# Four named list bounds from a cubic primary equation

At length $n=2^{30}$ the following closed balls obey the stated list budgets on every injective grid of the indicated field and at every positive interleaving width. The first failing error counts are at least one greater than the safe counts shown. [Exact four-row certificate](../../../scripts/probes/probe_joint_list_contact_boards.py)

| Field | Rate | Budget | Safe errors | Primary order | Primary surplus |
|:---|---:|---:|---:|---:|---:|
| First named prime | $1/16$ | $n$ | 816,806,371 | 9 | 89,642,666 |
| First named prime | $1/8$ | $n$ | 697,616,763 | 6 | 868,957,112 |
| Second named prime | $1/8$ | $2n$ | 705,616,763 | 9 | 585,544,890 |
| Second named prime | $1/4$ | $2n$ | 543,870,914 | 9 | 1,210,708,634 |

Write $d=k-1$, $t=n-e$, $s=t/n$ and $R=d/n$. Identify an interleaving with one polynomial over a finite extension. As in the [uniform quotient proof](sixteenth-list-quotient-jets.md), assign weights $1,d,d-1$ to $X,Y,V$. Write $N(w,h)$ for the dimension at strict weight cutoff $w$ and derivative cap $h$, and $C(r,h)$ for the local rank at contact order $r$. For the primary order $r_0$ in the table, put $P=r_0t$ and $b=\lfloor(P-1)/(d-1)\rfloor$. The primary surplus is $N(P,3)-nC(r_0,3)>0$. Thus one polynomial of derivative degree at most three and total jet degree at most $b$ vanishes on all candidate jets. All characteristic requirements hold on both named fields.

Assign each word to one irreducible primary factor containing its jet. Derivative-independent factors cover at most $b$ words. A group is large when it is assigned at least $L=\lfloor n/40\rfloor$ words. Let $g$ be the squarefree product of the large factors, with derivative degree $v$ and weight $D$. Small groups account for at most $3L$ words. If $v=0$ the list fits the budget. The remaining cases use two secondary interpolations.

## Products of derivative degree two or three

Use the [joint interpolation theorem and its proof](sixteenth-list-joint-quotient.md#one-assignment-of-multiplicities-for-all-large-groups). From each large group remove its at most $b^2$ singular solutions of $g=g_V=0$ and pick $t$ sites per regular solution. Choose the minimum-norm point in the convex hull of the centered site-population vectors of these groups. Write $p$ for the resulting occupancy vector after restoring the common mean $s$. Its variance $z$ is at most $V_0=R-s^2+(s-R)/(L-b^2)$. At every site put $q_x=\lfloor r+\lambda(p_x-s)\rfloor$, with $r=2000$. The minimization ensures the mean weighted agreement in **each** group is at least $(r-1)t+\lambda n z$. Every individual weighted agreement count is at most $rt+\lambda nV_0$. The weight cutoff $w=\lfloor(r-3)t+\lambda n z\rfloor$ leaves at least $2(L-b^2)t/(3t+1+\lambda nV_0)$ eligible words in each group.

Each row below gives a cutoff $c$ for excluding $D\ge c(d-1)$, with $h$ the secondary derivative cap. The two curvature bounds $b_2,j_2$ are the constants of the local inequalities in the [adaptive cost calculation](sixteenth-list-adaptive-quotient.md).

| Field and rate | $v$ | $h$ | $\lambda$ | $b_2$ | $j_2$ | $c$ |
|:---|---:|---:|---:|---:|---:|---:|
| First, $1/16$ | 2 | 600 | 7109 | 12.8 | 0.55 | 4 |
| First, $1/16$ | 3 | 700 | 6902 | 18 | 0.7 | 4 |
| First, $1/8$ | 2 | 500 | 4999 | 6.4 | 0.25 | 3 |
| First, $1/8$ | 3 | 600 | 4857 | 9 | 0.35 | 3 |
| Second, $1/8$ | 2 | 500 | 5107 | 6.65 | 0.25 | 4 |
| Second, $1/8$ | 3 | 600 | 4963 | 9.4 | 0.3 | 4 |
| Second, $1/4$ | 2 | 400 | 3650 | 3.45 | 0.15 | 3 |
| Second, $1/4$ | 3 | 500 | 3549 | 4.85 | 0.2 | 3 |

For clarity, put $B(q)=C(q,h)-C(q,h-v)$ and $J(q)=C(q,h-v)-C(q-1,h-v)$. The local checks use slope $(B(r+8)-B(r-8))/16$ for $B$ and coefficient $J(r)/s$ for the occupancy term in $J$. Every possible integer order is checked. Split $[0,V_0]$ into twelve equal intervals $[z_-,z_+]$. The source dimension modulo $g$ is bounded below using weight $\lfloor(r-3)t+\lambda n z_-\rfloor$. Division of the total local cost by $n$ gives the upper bound
$$
 B(r)+r/2+b_2r^2z_+ +
 \frac{J(r)}s\big(s+(D-d+1)/n\big)
 +(r/2+j_2r^2z_+)(D/d+v).
$$
Here $\mathbb E(p_x o_x)\le s+(D-d+1)/n$ follows from the ordinary derivative $g_V$ on each regular group, and $o_x\le D/d+v$. The verifier checks both endpoints of the interval $[c(d-1),P-1]$ by concavity. A positive surplus gives a secondary polynomial of weight below $w$ not divisible by $g$. It is coprime to at least one large factor, but its resultant bounds the eligible words of that factor by at most $v\lfloor(w-1)/d\rfloor+hb$. The certificate checks that the eligible population is strictly larger.

Consequently either $c=v$ and the case is impossible, or the surviving product has total degree $B_0\le c-1$. In the latter case the [normalized differential-curve bound](first-order-normalized-curve.md) summed over its irreducible factors bounds their population by
$$
  2B_0v-v^2+B_0+d(4B_0v-2B_0-2v^2)+v(n-d)/(t-d).
$$
Adding $3L+b$ fits the stated budget on every row.

## One large linear factor

Write $q=n/k$, $m$ for the budget multiple in the first table, and $K=1+mq/2$. If every list word lies on the large factor, it suffices to bound the factor's total degree by $K$. Its isolated polynomial solutions then number at most $K+(2K-2)d\le mn$; an integral family has at most $(n-d)/(t-d)<L$ words. When a word lies outside the equation, it suffices to bound the degree by $K-1$, since $(K-1)+(2K-4)d+3L+b\le mn$.

Both degree conclusions follow by the [coefficient intersection estimate and the exterior-word correction](quarter-list-exterior-contact.md). Use uniform secondary order $3000$. Without an exterior word, exclude $D\ge(K+1)d-1$ with the ordinary intersection bound. With an exterior word, exclude $D\ge Kd-1$ using the correction $-2(jt-D)_+$ in the bound for $2jn\overline o$. Divide each weight interval where either coefficient degree cap or the sign of $jt-D$ changes. Select one $j$ and one secondary derivative cap on each interval. Both endpoints must pass for this same choice. The quotient surplus is concave there. The $-1$ in these two weight cutoffs accounts for the possible monomial involving one derivative. The secondary Bézout bound is smaller than $L$ in each case.

For the four instances in table order the smallest verified surplus across **all** the secondary checks is respectively **30,420,863,338,064**, **28,889,261,844,644**, **45,366,005,034,097** and **20,795,214,798,145**. These written arguments establish the four safety bounds. The finite comparisons use exact rational arithmetic.
