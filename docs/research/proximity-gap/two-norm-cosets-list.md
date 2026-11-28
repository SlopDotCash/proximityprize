# Exact MCA and list thresholds on 16,384 sites

For the order-16,384 subgroup of $\mathbb F_{8191^{10}}^\times$, dimension 1,024 and tolerance $2^{-128}$, the first failing counts are **3 errors for MCA** and **10,754 errors for list decoding**. The corresponding suprema are $3/16384$ and $5377/8192$. Both results hold on every coset of the subgroup and at every positive interleaving width. The field has 130 bits and its integer budget is three. [Complete construction and verifier](../../../scripts/probes/probe_norm_two_cosets_list.py) · [Exact results on the index-two subgroup](norm-one-elliptic-list.md)

## A quartet saturating all six pair bounds

Write $p=8191$, let $i^2=-1$ in $\mathbb F_{p^2}\subset\mathbb F_{p^{10}}$, and represent $a+bi$ as $(a,b)$. We give four polynomials of degree at most $d=1023$. Each pair agrees at $d$ sites, and the six sets of sites are disjoint.

To build the two base-field polynomials, start from $E':y^2=x^3+3245x+6342$ over $\mathbb F_p$. It has 8,184 rational points including infinity. Let $C$ be the set of abscissas of the seven nonidentity points in the image of multiplication by 1,023 on this group. For a rational abscissa $x$ outside $C$, define
$$
 \psi(x)=x+\sum_{a\in C}\left(
 \frac{\tau_a}{x-a}+\frac{4(a^3+3245a+6342)}{(x-a)^2}\right),
$$
where $\tau_a=2(3a^2+3245)$ except that the factor two is omitted when $a^3+3245a+6342=0$. The resulting set $K$ of distinct values has 511 elements. Put
$$
 Q(T)=\prod_{c\in K}(T-c)^2,\qquad
 P(T)=Q(T)\left[T+\sum_{c\in K}
 \left(\frac{2(3c^2+4877)}{T-c}+
 \frac{4(c^3+4877c+7687)}{(T-c)^2}\right)\right].
$$
Both are polynomials. Their degrees are 1,022 and 1,023, respectively. These definitions merely require finite arithmetic over $\mathbb F_p$. The verifier enumerates the curve, computes the multiplication images, and forms $P,Q$ by exact polynomial multiplication.

For a grid coordinate $u$ put $t=6109+121i(1+u)/(1-u)$ and set $P_*(u)=(1-u)^dP(t)$ and $Q_*(u)=(1-u)^dQ(t)$ by homogeneous substitution, also at $u=1$. The two cosets of the norm-one subgroup satisfy $u^{p+1}=1$ and $u^{p+1}=-1$. The first maps to the rational projective line. On the second the norm of $t-6109$ is $1741=-121^2\bmod p$. This second circle is also the one on which Frobenius acts by the transformation $t\mapsto6109+1741/(t-6109)$, the abscissa action of translation by the two-torsion point $(6109,0)$ on $y^2=x^3+4877x+7687$. This identifies the two sets of sites used to find the pencil. The numerical proof below evaluates the actual message polynomials throughout the subgroup.

Take the four words $a_j(P_*-z_jQ_*)$, where the coefficient pairs $(a_j,z_j)$ are
$$
 ((0,0),(0,0)),\quad ((1,0),(7491,0)),\quad
 ((7443,1965),(6189,8059)),\quad ((7443,6226),(6189,132)).
$$
In lexicographic order of word pairs, the six targets of $P_*/Q_*$ are
$$
 (7491,0),\ (6189,8059),\ (6189,132),\ (6302,6245),\ (6302,1946),\ (2150,0).
$$
The verifier expands ordinary coefficients for $P_*,Q_*$ and evaluates them at all 16,384 powers of a generator by the radix-two Fourier transform. It also evaluates $P,Q$ by Horner's rule in the projective coordinate at every site, with the homogeneous value at infinity. The results agree everywhere. There are no base points, each of the six targets has exactly 1,023 physical preimages, and all four words are different. Choosing the common value at every double site and distributing the remaining $16384-6\cdot1023=10246$ sites cyclically gives actual word agreement counts **5,631, 5,631, 5,630 and 5,630**. Thus four words are in one closed ball at 10,754 errors.

## Matching safety and the MCA count

For four distinct candidate words at arbitrary positive width, let $m_x$ be the number matching the received value at $x$. Since $m_x\le1+\binom{m_x}{2}$ and each pair differs in some row of degree at most 1,023,
$$
       \sum_x m_x\le 16384+6\cdot1023=22522<4\cdot5631.
$$
At 10,753 errors each candidate would need at least 5,631 hits. Hence the list bound of three holds through that error count. Repeating the scalar witness across rows supplies the next failure at all positive widths. Rescaling $u$ transfers both conclusions to multiplicative cosets.

For MCA the budget-three spike boundary applies. At two errors any three label supports have at least $16384-6\ge1024$ sites in common, so the three folded interpolants are on one affine head. A single head gives at most three bad labels. At three errors take a common joint core on all but four sites and assign four distinct fresh labels. The core determines both polynomials uniquely, and each fresh witness exceeds its explanation. This is also a specialization of the established general finite theorem. [Formal budget boundary and its use on the smaller domain](norm-one-elliptic-list.md#mutual-correlated-agreement-on-the-same-input)
