"""Exact arithmetic for the pair-to-triple aggregation.

For each high-union pair the per-pair completion cap leaves at least
`b - 2 - K` long completions. Summing over high pairs and dividing by three
(the number of pairs in a triple) gives a lower bound on long triples.

This probe checks the two comparisons the draft needs, with `K = 4806 + 3`
(4806 proven completions plus the two deleted heads and at most one collinear
completion).
"""

from fractions import Fraction as Q

B = 1073741825          # b = n + 1
K = 4809                # 4806 + 2 deletions + 1 collinear
PAIRS = B * (B - 1) // 2
TOTAL = B * (B - 1) * (B - 2) // 6


def main() -> int:
    # the draft's high-pair fraction, exact as 30343/100000
    high_pairs = 30343 * PAIRS // 100000
    long_lower = high_pairs * (B - 2 - K) // 3
    target = 3 * TOTAL // 10          # 30 percent of all unordered triples

    print(f"b = {B}")
    print(f"unordered pairs   = {PAIRS}")
    print(f"unordered triples = {TOTAL}")
    print(f"high pairs (30343/100000) = {high_pairs}")
    print(f"long triples lower bound  = {long_lower}")
    print(f"30 percent of triples     = {target}")
    print(f"lower bound / target      = {float(Q(long_lower, target)):.6f}")

    # the exact inequality the Lean theorem states
    lhs = 3 * target                  # 9/10 of total, cleared of the /3
    rhs = high_pairs * (B - 2 - K)
    print(f"\n3 * 30%-of-triples = {lhs}")
    print(f"highPairs * (b-2-K) = {rhs}")
    print(f"slack = {rhs - lhs}  (ratio {float(Q(rhs, lhs)):.6f})")
    assert rhs > lhs, "the aggregation does not clear 30 percent"

    # with the tighter K = 4806 (no deletions) the margin only grows
    rhs_tight = high_pairs * (B - 2 - 4806)
    print(f"tight K=4806 slack = {rhs_tight - lhs}")
    assert rhs_tight > rhs
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
