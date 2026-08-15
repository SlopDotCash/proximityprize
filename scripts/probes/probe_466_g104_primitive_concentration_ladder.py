#!/usr/bin/env python3
"""G104 (scoping probe): the all-depth primitive-concentration ladder.

Threshold arithmetic (exact, vs the sharp G86 envelope at (n,r) = (2^30,110)):
the (2, s-2)-split chain J_s <= maxN_s * n^s with maxN_s <= M_{s-2}^prim * n^2 + strata
needs, at EVERY depth s in [5, 110]:

    M_{s-2}^prim <= B_s / n^{s+2},   B_s = 219!! n^s / (C(110,s)^2 (110-s)!)

which stays in the band n^{0.73..0.87} for all middle depths (minimum ~2^22.16 at s=10,
rising on both sides).  So ONE uniform named family

    PrimitiveConcentration: max_a #{primitive k-tuples of mu_n summing to a} <= 4 n^{2/3}
    (primitive = no proper sub-multiset sums to zero), for all k in [3, 108]

closes the ENTIRE padded-collision lane above the landed depths (with the degenerate
strata recursing through lower orders and the antipodal stratum Z_2 = n paying a
factor ~ s^2 n per removed pair -- affordable against the Wick budget for s >= 5).

Empirics at small scale (mu_n in F_p, n ~ p^{1/4}, even n):
raw M4 ~ c*n (antipodal-degenerate), PRIMITIVE M4 measures 4!*{1,1,1,1,3,7}:
O(1)-ish genuine solutions, 2^20 headroom at production.  Z3c (primitive zero-sum
triples) measures 0..60.  See G102 (pair statistics closed at depth >= 5) and G103
(depth-5 consumer) for the landed endpoints of this programme.
"""
print(__doc__)
