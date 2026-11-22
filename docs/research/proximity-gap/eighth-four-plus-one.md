# Four collinear eighth-rate heads and one transverse head

Let $m=2^{27}$, $n=8m$, and $d=m-1$. At agreement threshold at least $3m$ (at most $5m=671088640$ errors), fix four distinct degree-at-most-$d$ polynomial heads on one polynomial line and a fifth head outside that line. On every injective evaluation domain, their union carries at most **2,058,021,547** distinct selected MCA-bad scalars. This leaves **89,462,101** labels of room below the second named prime's $2n$ budget. The bound applies to the actual selected polynomial for each scalar, so it can be used directly in a factor allocation.

## Deficits and the union of cores

Assign each scalar on the five heads to just one of the heads containing its selected polynomial. Let $C_i$ denote a cluster head's joint core, $C_z$ the outside head's core, and $x_i,x_z$ the disjoint assigned populations. Order the four cluster heads by increasing deficit $a_i=\max(1,3m-|C_i|)$, and put $z=\max(1,3m-|C_z|)$. Every assigned scalar on head $i$ requires at least $a_i$ fresh sites outside $C_i$. Indeed, the full agreement set has at least $3m$ sites. Its failure of joint agreement supplies a fresh site even if $|C_i|\ge3m$. A fixed fresh site on a fixed head serves at most one scalar. It follows that $x_i\le 5m/a_i+1$ and $x_z\le5m/z+1$.

Write the cluster heads as $A+f_iD$ with $D=(P,Q)$ a primitive polynomial direction and put $h=\max(\deg P,\deg Q)$, using natural degrees. Cluster-core pair intersections have size at most $d-h$, the maximum degree of $f_i-f_j$. A transverse head meets the union of any cluster cores on at most $d+h$ sites, since the determinant of its displacement from $A$ with $D$ is nonzero and vanishes there. These two inequalities are proved together in Lean. [Primitive overlap theorem](../../../ArkLib/Research/ProximityGap/Frontier/EighthCollinearOutlier.lean)

Let $U_j=C_1\cup\dots\cup C_j$. The first two inclusion-exclusion terms and the transverse bound yield
$$
|U_j|\ge\sum_{i\le j}|C_i|-\binom j2(d-h),\qquad
|U_j|+|C_z|\le n+d+h.
$$
For $j=3,4$, substitution gives
$$
a_1+a_2+a_3+z\ge4+2h,\qquad
a_1+a_2+a_3+a_4+z\ge7+5h.
$$

A site in any cluster core can supply at most one fresh scalar across **all** cluster heads. Every such scalar equals the slope of the primitive direction there. The primitiveness excludes a simultaneous zero of both components. Outside the union of those cores each specified head supplies at most one scalar per site. Thus for the first $j$ heads and any union $U$ of cluster cores, their total number of fresh incidences is at most $|U|+j(n-|U|)$. If all $j$ heads own a site in $U$, that site supplies no fresh incidence for these heads and can be subtracted. Disjoint assignments ensure each incidence belongs to just one scalar. [Weighted incidence theorem](../../../ArkLib/Research/ProximityGap/Frontier/CollinearFreshMultiplicity.lean)

## Bounds on the four partial sums

Set $R=1024$ and call a head active if $a_i\le R$. With at most two active cluster heads the total is at most $3(5m+1)+2(5m/(R+1)+1)<2,058,021,547$. With three or four active heads, the union bound gives $|U_3|\ge6m-3R$, and $|U_4|\ge6m-4R$ when all four are active.

If $z\ge4$, four active cluster heads supply at most $4n-3|U_4|\le14m+12R$. With three active heads they supply at most $3n-2|U_3|+5m/(R+1)+1\le14m+12R$ including the inactive fourth head. The outer head adds at most $5m/4+1$, staying below the claimed cap.

If $h=0$, the primitive scalar is constant throughout the domain. After discarding this one possible label, every active cluster head needs a fresh site outside the active cluster union. For $j=3$ or $4$ active heads its population bound is therefore $1+j(n-|U_j|)$. Adding the possible inactive head and the outer head again stays below the claimed cap.

It remains to consider $z\le3$, $h\ge1$, and at least three active cluster heads. Write $J=|C_1\cap C_2|$. The two other pair intersections in $U_3$ have size at most $d-h$ each, so
$$
7m-3R+2+2h-J\le |U_3|\le6m+z-1+h.
$$
In particular $J\ge m-3R-z$. On $U_3$ the first two heads have at most one fresh incidence per site and have none on their $J$ shared sites. Their total is at most $2n-|U_3|-J\le9m+7R$.

Put $b_i=\min(a_i,12)$ and $Y_i=b_ix_i$. The preceding bounds give
$$
Y_1\le5m+R,\qquad Y_1+Y_2\le9m+7R,\qquad
Y_1+Y_2+Y_3\le12m+6R,\qquad
Y_1+Y_2+Y_3+Y_4\le14m+16R.
$$
For the last inequality, when the fourth head is inactive its contribution is at most $12(5m/(R+1)+1)<2m$. Otherwise use $4n-3|U_4|$. All four prefix estimates therefore hold with the common additive allowance $16R$.

## Integer optimization

The clipped deficits satisfy $b_1+b_2+b_3+z\ge6$ and $b_1+b_2+b_3+b_4+z\ge12$. Since $1/b_i$ is nonincreasing, summation by parts bounds the total number of labels by
$$
m\left(\frac5{b_1}+\frac4{b_2}+\frac3{b_3}+\frac2{b_4}+\frac5z\right)+16R+1.
$$
The parenthesis is at most $46/3$. If $b_1\ge2$ or $b_2\ge2$, the corresponding sorted lower bounds already suffice. For $b_1=b_2=1$ with $z=3$, either $b_3\ge2$ or $b_4\ge6$. With $z=2$, the triple bound forces $b_3\ge2$. Finally $z=1$ gives $b_3\ge3$ and $b_3+b_4\ge9$. The maximum comes from $b_3=3$, $b_4=6$. For $b_3=4$ use $b_4\ge5$, and for $b_3\ge5$ both last terms sum to at most one. Rounding down $46m/3+16385$ gives the stated **2,058,021,547**.
