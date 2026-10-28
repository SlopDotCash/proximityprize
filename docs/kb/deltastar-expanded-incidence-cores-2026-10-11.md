# Expanded production incidence cores

Author: Mikhail Izhutkin (@mashingaan)

Evidence class: exact computation and algebraic derivation. The new bounds below are not Lean formalized. They strengthen the computational lane of PR 222, not its existing kernel-checked three-core consumer.

## Construction and canonical event

Let n = 2^30, d = 2^24, k = 2^29. Use the certified generator g of order n in either canonical prize field. Put omega = g^d and Z(X) = product over b = 0,...,30 of (X^d - omega^b). Partition s*t of the remaining 33 labels into s disjoint groups of size t, and give group j height j for j = 0,...,s-1. Give any remaining labels height s.

For x = g^i of label i mod 64 define u1(x) = h(x)*Z(x) and u0(x) = h(x)^2*Z(x)*x. For group j use decoded heads v1 = j*Z and v0 = j^2*X*Z. Their degrees are at most 31d and 31d+1, both strictly less than k. Each head pair agrees with the received pair on the common 31 labels and group j, a core of (31+t)d coordinates.

At any coordinate x outside that core, h(x) differs from j and Z(x) is nonzero. Set gamma = -(h(x)+j)*x. The decoded codeword v0+gamma*v1 agrees with u0+gamma*u1 on the core and x, giving support size (31+t)d+1. This meets the canonical agreement threshold at delta = ((33-t)d-1)/n.

The support is not jointly explained: if any dimension-k RS head agreed with u1 on that support, its agreement on the core of at least k distinct coordinates would force it to equal j*Z. At x it cannot equal u1 because (h(x)-j)*Z(x) is nonzero. This negates the forall-support joint-head condition in Errors.mcaEvent. The witness support need not be the full exact agreement support.

## Distinctness and exact counts

For each fixed label the eligible coefficients h+j are pairwise distinct. Every coefficient is nonzero. Across different coefficients a and b, equality of scalars implies (a/b)^n = 1. The script checks a^n != b^n modulo the exact production prime, which excludes that collision. Within a fixed coefficient, generator injectivity distinguishes coordinates. Thus all s*(33-t)*d slots give distinct canonical bad scalars, without enumerating the production domain.

First field P = n*(2^128+192)+1, budget floor(P/2^128) = n:

- s = 3, t = 11, no leftover labels
- coefficient inventory {1,2,3}
- support size 704643073
- radius 369098751/1073741824 = 11/32 - 1/n
- bad-count lower bound 1107296256 = 66d
- budget excess 33554432 = 2d

Second field P = n*(2*2^128+13)+1, budget 2n:

- s = 5, t = 6, three leftover labels of height 5
- coefficient inventory {1,...,9}
- support size 620756993
- radius 452984831/1073741824 = 27/64 - 1/n
- bad-count lower bound 2264924160 = 135d
- budget excess 117440512 = 7d

The script independently cross-multiplies count*2^128 > P. Subject to the derivation above, MCAWitnessSpread and MCAThresholdLedger.mcaDeltaStar_le_of_bad would transfer these bad radii into the corresponding upper threshold bounds. That transfer has not been implemented or newly kernel checked for these expanded cores. No exact threshold or prize closure is claimed.

## Optimization scope and reproduction

The probe enumerates equal-size designs with common 31 labels, 3 <= s <= 33, t >= 1, s*t <= 33. It maximizes t subject to a strictly over-budget count. The maximal t is 11 in the first field and 6 in the second. This is optimal only within this family, not among arbitrary RS stacks.

## Coordinate-scale strengthening

`probe_incidence_full_scale_cores.py` removes the artificial 64-label granularity. Use n labels of one coordinate each and common size c = k-2 = 536870910. Set t = floor((n-c)/s), take s consecutive disjoint groups of size t outside the common coordinates, and assign leftover coordinates height s. Define Z(X) as the product of X-g^i over the common coordinates. The construction and uniqueness argument above apply verbatim with d = 1. The maximum head degree is c+1 = k-1, still strictly less than k. Neither the common product nor the production domain is enumerated by the compressed arithmetic certificate.

First field, s = 3:

- group size 178956971, one leftover coordinate
- core size 715827881, witness support size 715827882
- radius 178956971/536870912 = 1/3 + 2/(3n)
- distinct bad scalars at least n+5 = 1073741829
- exact normalized-error excess: (n+5)*2^128-P = 1701411834604692317316873036952682627071 > 0

Second field, s = 5:

- group size 107374182, four leftover coordinates
- core size 644245092, witness support size 644245093
- radius 429496731/1073741824 = 2/5 + 7/(5n)
- distinct bad scalars at least 2n+12 = 2147483660
- exact normalized-error excess: (2n+12)*2^128-P = 4083388403051261561560495289167259893759 > 0

The script checks all coefficients 1 through 5 in the first field and 1 through 9 in the second. Their n-th powers are pairwise distinct. These inventories conservatively include every eligible h+j, including leftover coordinates. Each fixed coordinate has distinct h+j as j varies, so the full count is s*(n-c-t). The small-field independent interpolation check uses c = 62, with group size 22 for s = 3 and 13 for s = 5. It validates 132 and 265 distinct witnesses respectively.

The probe additionally checks the actual two canonical generators: g^n = 1 and g^(n/2) != 1. Since n is a power of two, these verify exact order n in the already certified prime fields.

### Exact optimization within the quadratic-height family

These radii minimize the threshold within equal-size, disjoint-group quadratic-height designs with c <= k-2 and core size c+t >= k. For a budget b*n, any s <= 2b gives count s*(n-c-t) <= s*(n-k) <= b*n, so at least 2b+1 heads are necessary. For fixed s, the largest possible core is c+floor((n-c)/s). This is nondecreasing in c because incrementing c by one decreases the floor by at most one. Therefore c=k-2 is optimal. At that c the core is nonincreasing in s, so the smallest possible number of heads gives the strongest radius. Our designs at s=3 and s=5 are strictly over budget, certifying attainment of this family optimum. This does not optimize arbitrary incidence constructions or prove a universal matching lower bound.

### Exact support boundary

For each constructed gamma and its designated head w_j = j^2*X*Z + gamma*j*Z, the full exact agreement support is precisely the core plus its chosen coordinate x. The difference from the received line factors as (h-j)*Z*((h+j)*X+gamma). Outside the common coordinates and group j the first two factors are nonzero. At a fixed coefficient h+j, the last factor has a unique root. A second coefficient giving another domain root would force equal n-th powers of two distinct coefficients, excluded by the production certificates. Thus there is no hidden additional agreement coordinate for this head. The finite independent implementation now checks equality of the full exact support with core+[i] for every witness.

Reducing the radius by one Hamming step would require one more agreement coordinate. These designated heads cannot provide it. Increasing common degree to k-1 would make their X*Z term degree k, outside the dimension-k code. This closes two immediate ways of retargeting this construction. It does not exclude an unrelated decoded head or a different stack.

Run `python scripts/probes/probe_incidence_full_scale_cores.py`. These stronger results remain exact arithmetic plus an algebraic derivation. In particular the new upper bounds near 1/3 and 2/5 have not been kernel checked, and no matching lower bound or prize solution is claimed. The small positive count margins 5 and 12 must be retained exactly.

Run `python scripts/probes/probe_incidence_expanded_cores.py`. All load-bearing arithmetic uses integers or Fraction. The script also independently reconstructs every witness over F_1409 with n = 128 and d = 2, using direct Lagrange interpolation rather than the symbolic head formula. The small instance verifies the construction implementation, while the explicit production modular-power certificates supply the production coefficient separation. Neither check replaces a Lean proof of the expanded construction.
