"""Exact arithmetic ledger for the decoded-triple incidence floor.

Author: Mikhail Izhutkin (@mashingaan).
The strict inequality combines the triple union upper mass, the collinear
triple budget, and three repeated-index diagonals. This script checks only
arithmetic. The canonical all-bad-witness consumer passed the separate Lean
kernel check and axiom audit at commit 210cb1781.
"""

import json
from fractions import Fraction
from math import isqrt

n = 2**30
k = n // 2
m = n + 1
d = n - k
s = isqrt(3 * m)


def slack(t):
    exceptional_budget = s * m * (t + 1)**2 + 3 * m**3 + s**2 * m**2
    exceptional_budget += 3 * s * m**2
    lower = s * n**2 * (d + 1) * m**3 + s * (m * (n - t))**3
    upper = s * n**3 * m**3 + n**2 * (d + 1) * exceptional_budget
    return lower - upper


lo = 0
hi = n // 3
assert slack(lo) > 0
assert slack(hi) < 0
while hi - lo > 1:
    mid = (lo + hi) // 2
    if slack(mid) > 0:
        lo = mid
    else:
        hi = mid

assert 2 <= s <= m
assert lo < m
assert slack(lo) > 0 >= slack(lo + 1)
print(json.dumps({
    "n": n,
    "k": k,
    "witness_count": m,
    "distance_support_budget": d,
    "block_size": s,
    "candidate_error_bound": lo,
    "candidate_floor": str(Fraction(lo + 1, n)),
    "strict_integer_slack": slack(lo),
    "next_integer_slack": slack(lo + 1),
    "improvement_steps_over_average_anchor": lo + 1 - 190185818,
    "evidence": "exact arithmetic, with separately kernel-checked canonical incidence consumer",
}, indent=2))
