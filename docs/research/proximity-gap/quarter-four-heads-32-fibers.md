# Exact first-prime quarter MCA threshold on the 32-site quotient

On the first named subgroup of order $n=2^{30}=32s$, the first quarter-rate MCA overrun explained by **any number of** collinear heads whose scalar differences factor through the 32-site quotient after removing a common polynomial locator occurs at **480,946,859 errors**. The received rows, the locator sites, and the number of fresh agreements per assigned scalar are arbitrary. The published three-head witness attains the bound. The unrestricted first failure is within one error of the optimum for four collinear heads on the full domain. [Three-head threshold on this quotient](quarter-three-heads-32-fibers.md) · [Unrestricted reduction](quarter-mca-four-collinear.md)

First restrict to at most four heads. The final section removes this restriction.

## The four populations

Work at the predecessor $e=480946858$, put $d=n/4-1$ and let $t=n-e$, so that $3(t-1)=53s-1$. Take $n+1$ distinct assigned labels. Each head with population $L_i$ and core size $c_i$ satisfies $L_i\max(1,t-c_i)\le n-c_i$, giving $L_i\le e+1$. A constant direction cannot suffice. Among four heads, each of the three largest populations is at least $\lceil(n+1-2(e+1))/2\rceil$. Their joint cores have sizes at least $C=t-\lfloor e/(\lceil(n+1-2(e+1))/2\rceil-1)\rfloor$. Their union leaves at most $h_0=n-3C+3d$ sites, by the pairwise degree bound. A constant direction supplies at most one fresh scalar on the union and at most four elsewhere, and $1+4h_0<n$.

The known three-head site inequality on this quotient bounds the population of **each triple** by $3n+42s-6-6(t-1)=n-4$ if its three assigned populations are at least two. When one of them is at most one, the simpler bound $2(e+1)+1\le n-4$ applies. These estimates apply to the labels previously assigned to the three heads, without reallocating any. Thus no overrun uses only three heads and all four individual populations must satisfy $L_i\ge5$. The three-head inequality uses the finite order-32 septic census at the named characteristic. [Site inequality](quarter-three-heads-32-fibers.md#counting-incidences-across-the-32-quotient-fibers) · [Finite cubic and septic facts](mu32-quarter-list-threshold.md#three-finite-fiber-facts)

Write the heads as one common polynomial pair plus $J(X) f_i(X^s)(P(X),Q(X))$, with $P,Q$ coprime and of nonconstant projective direction. Subtract $f_1$ from all four $f_i$ and absorb any common polynomial factor of the differences into $J$. Thus there is no four-way coincidence at a quotient site. Let $m=\max\deg(f_i-f_j)$ and let $\ell$ count physical grid roots of $J$. The row degree bound gives $\ell\le 8s-2-ms$, in particular $m\le7$.

At a site, let $M$ be the number of matched heads and $I$ the number of fresh incidences of the assigned labels. If a head is matched, every fresh scalar here must cancel the same primitive direction, so $I\le1$ (zero if $M=4$). At a hole, $I$ is at most the number of different head values. Write $K=\sum(2M+I)$ and $u=\sum_i(t-1-c_i)_+$. The support requirements imply
$$
          K\ge 8(t-1)+n+1+\sum_i(L_i-2)(t-1-c_i)_+
           \ge 8(t-1)+n+1+3u . \tag{1}
$$

## All 42 pair roots would have to occur

At a nonlocator site with $p$ unordered equal head pairs, $2M+I\le4+p$. This follows from the four-site partitions, including the hole option. At a locator site the local upper bound is eight, so adding four to the unperturbed quotient charge always suffices. The six base pair differences have at most $6m$ grid roots in total with pairs counted separately. Consequently
$$
           K\le4n+6ms+4\ell .
$$
For $m\le6$ the right side is at most $172s-8$, strictly below (1). For $m=7$ it is at most $174s-8$. Losing one quotient pair root would cap it at $173s-8$, still below (1). Thus **every one of the six differences has seven grid roots**.

No quotient site can have two distinct double blocks. At its nonlocator preimages $M\le2$ and a hole supplies at most two fresh scalars, so its actual charge is at most five compared with the budget $4+2=6$. Even a locator preimage costs at least one unit against its budget $4+2+4$. Such a base site would therefore lose at least $s$ units.

Let $b$ be the number of triple sites. There are $42-3b$ sites with one pair, and $2b-10$ sites with four distinct values. If there is no four-distinct site, each locator costs at most three additional units over the base charge, giving $K\le4n+42s+3\ell\le173s-6$, still too small. Hence $b\ge6$.

## The remaining thirteen units

Let $y$ count matched physical sites outside the locator which lie above four-distinct quotient sites. Each costs at least one unit against its budget of four, since $M=1$ and $I\le1$. With (1) this gives
$$
              y+3u\le 174s-8-8(t-1)-n-1=(2s-19)/3 .
$$
The total core size $E=\sum_i c_i$ is at most
$$
          (2(42-3b)+3b)s+4\ell+y
              \le (88-3b)s-8+y\le70s-8+y .
$$
The first term is the entire double or triple population before the locator. The second allows four matches at every locator root. Since $E\ge4(t-1)-u$, this requires $y+u\ge(2s+20)/3$. The two bounds differ by thirteen even at $u=0$. This rules out a quartet at the predecessor; monotonicity covers earlier errors.

The proof is written. The checker exhausts the four-head site partitions and verifies the predecessor inequalities, including the thirteen-unit contradiction. [Finite verifier](../../../scripts/probes/probe_quarter_four_heads_mu32.py)

## Any number of quotient words

Now allow a different quotient polynomial $F_z$ for every selected scalar $z$, with no bound on their number. The prescribed form of the selected witnesses is
$$
                  q_z=A+zB+J(P+zQ)F_z(X^s),
$$
where $(A,B)+JF_z(X^s)(P,Q)$ has both row degrees at most $d$. A common factor of $P,Q$ can be absorbed in $J$. Apply the published quartic classification to these particular $n+1$ supports and witnesses. It assigns all but at most 2047 labels to three or four rich collinear polynomial heads. There can be four rich heads only when they cover all labels. [Classification at the terminal predecessor](quarter-collinear-interval.md#a-single-quartic-throughout-the-bracket)

First suppose that the original projective direction belongs to $K(X^s)$, including a constant or vertical direction. If $P,Q$ are both nonzero, write their ratio with coprime numerator and denominator in $K[Y]$ and substitute $Y=X^s$. Coprimality survives substitution by Bézout. The substituted pair is consequently $(P,Q)$ up to a common scalar. The same claim holds for a coordinate-zero primitive pair, whose other entry is constant. All differences $q_z-A-zB$ thus belong to $J K[X^s]$. If $(A',B')$ is any extracted rich head, its identity with the two selected scalar words at any two of its labels gives $A'-A,B'-B\in J K[X^s]$. The common direction of the distinct extracted heads therefore takes at most 32 projective values on the domain, also after cancellation of all common factors.

Each extracted rich head has at least 2048 labels and at least $C_0=t-\lfloor e/2047\rfloor$ joint sites. The core union of three leaves at most $h_1=n-3C_0+3d$ sites uncovered. All represented fresh scalars together give at most 32 distinct labels on that union, because a fresh scalar must cancel the common extracted direction. The rich heads together supply at most $32+4h_1$ labels; even after adding 2047, this is below $n$. This excludes the first case.

In the other case $P/Q\notin K(X^s)$. Any polynomial head containing **three distinct selected labels** is one of the original quotient heads. Indeed, for its three scalar witnesses write $F_1,F_2,F_3$ for their respective quotient words. Affine interpolation of the first two at the third label, followed by subtraction of the corresponding identity for $A+zB+J(P+zQ)F_3$, gives
$$
             (P+z_1Q)(F_1-F_3)=c(P+z_2Q)(F_2-F_3)
$$
with $c\ne0$. Here each $F_i$ is evaluated at $X^s$. If either difference on one side is nonzero, both are, and $(P+z_1Q)/(P+z_2Q)\in K(X^s)$ would imply $P/Q\in K(X^s)$. Hence the three quotient words coincide. Their common polynomial head equals the extracted head by its identities at two distinct scalars.

All rich heads are therefore genuine quotient heads. Four rich heads are impossible by the preceding result. For three rich heads, the order-32 triple root bound gives their numerical three-head capacity $V\le n-4$, independent of the received rows. At least five selected labels remain outside the assigned triple. The normalized outsider counting theorem with $V\le n$ excludes three distinct additional rational functions and excludes a repeated function together with any different outsider function. Labels whose normalized word is one of the three primary words can first be absorbed into their primary assignments, whose total is still at most $n-4$. The remaining five or more labels consequently belong to one new polynomial head. This head too contains at least three selected labels, and so is one of the original quotient heads. Four such heads would cover all $n+1$ labels, the contradiction already proved. [Outsider class packing](quarter-mca-four-collinear.md#at-most-two-additional-rational-functions)

The arbitrary-population extension uses the written quartic surface classification. The four-head calculation uses its independent order-32 site and degree counts.
