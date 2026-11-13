r"""Layer-cake budget for the pencil charge at the P1 predecessor: exact audit.

Closing probe of the pencil arc.  Per base scalar, #bad - 1 = sum of pencil
fibers; each pencil with phi riders has alignment A >= ceil((phi*T-N)/(phi-1))
(alignment ladder) and fiber <= (N-T)/(T-A) (vote bound).  Distinct pencils'
aligned regions pairwise intersect in < k coordinates, so at any alignment
level a with a^2 > N(k-1) the pencil count is Johnson-bounded:

    J(a) = floor( N*(a-(k-1)) / (a^2 - N*(k-1)) ).

This probe computes the exact layer table and settles the budget question:

  * the Johnson threshold is isqrt(N(k-1)) = 536870910; pencils aligned at or
    below it carry at most NINE riders (fiber <= 8) but their COUNT is not
    bounded by any assembled constraint -- the light side is open;
  * the heavy side does not close either: J(T-1) >= 3 and 1 + 3*(N-T) > N,
    so THREE pencils aligned at T-1 with full fibers N-T satisfy every
    counting constraint (Johnson count, aligned-region packing, vote bounds)
    while exceeding the prize budget.

Verdict: the pure counting surface (vote partition + alignment ladder +
Johnson packing of aligned regions) is EXHAUSTED; the minimal open statement
is an RS-algebraic exclusion of >= 3 near-threshold-aligned pencils through
one base point (or the structured-floor pivot).  The Lean transcription is
`_P1RateQuarterLayerCakeBudget.lean`.

Deterministic, dependency-free, runtime under a second.
"""

from __future__ import annotations

import math

N = 2**30
K = 2**28
T = 592794966
NT = N - T
P_ = K - 1  # pairwise aligned-intersection cap


def _require(condition, detail):
    """Keep the layer-cake certificate checks active under Python optimization."""
    if not condition:
        raise AssertionError(detail)


def J(a: int) -> int:
    """Exact subtracted Johnson count at alignment level a (requires gap)."""
    den = a * a - N * P_
    _require(den > 0, f"Johnson denominator is not positive at alignment {a}")
    return (N * (a - P_)) // den


def ladder_floor(phi: int) -> int:
    """Alignment forced by phi riders: ceil((phi*T - N)/(phi - 1))."""
    return -((-(phi * T - N)) // (phi - 1))


def main() -> None:
    thr = math.isqrt(N * P_)
    _require(
        thr == 536870910 and thr * thr <= N * P_ < (thr + 1) * (thr + 1),
        "Johnson threshold is not 536870910",
    )
    print(f"Johnson threshold isqrt(N(k-1)) = {thr}")

    # ladder table
    print("phi : ladder alignment floor A_phi (and whether above threshold)")
    for phi in range(2, 13):
        a = ladder_floor(phi)
        above = a > thr
        extra = f"  J(A_phi) = {J(a)}" if above else ""
        print(f"  {phi:3d} : {a}  above={above}{extra}")
    _require(
        ladder_floor(10) == 539356427 > thr,
        "10-rider alignment floor is not 539356427",
    )
    _require(
        ladder_floor(9) == 532676609 <= thr,
        "9-rider alignment floor is not 532676609",
    )

    # light side: fiber cap below the threshold
    light_fiber = NT // (T - thr)
    _require(T - thr == 55924056, "sub-Johnson gap T - threshold is not 55924056")
    _require(light_fiber == 8, "sub-Johnson fiber cap is not 8")
    print(f"sub-Johnson pencils: fiber <= {light_fiber} (riders <= 9); "
          "count unbounded by the assembled constraints")

    # heavy caps
    j10 = J(539356427)
    jT1 = J(T - 1)
    print(f"heavy-pencil count at the ten-rider floor: J = {j10}")
    print(f"pencil count at alignment T-1: J = {jT1}")
    _require(jT1 >= 3, "Johnson count at alignment T-1 is below 3")

    # the killer admissibility check: three pencils at alignment T-1
    # (1) Johnson admits three
    _require(
        3 * ((T - 1) ** 2 - N * P_) <= N * ((T - 1) - P_),
        "Johnson does not admit three pencils at alignment T-1",
    )
    # (2) aligned-region packing feasible (Bonferroni with pairwise < k)
    _require(
        3 * (T - 1) <= N + 3 * P_,
        "aligned-region packing rejects three pencils at alignment T-1",
    )
    # (3) full fibers allowed by the vote bound at T-A = 1
    _require(
        NT * (T - (T - 1)) <= NT,
        "vote bound rejects a full fiber at alignment T-1",
    )
    # (4) over-budget
    _require(N < 1 + 3 * NT, "three full fibers at alignment T-1 do not exceed N")
    print("ADMISSIBLE: three pencils at alignment T-1 with fibers N-T "
          f"give 1 + 3*(N-T) = {1 + 3 * NT} > N = {N}")

    # for the record: greedy heavy maximum under nested Johnson counts
    total = 0
    for i in range(1, j10 + 1):
        # largest alignment level at which i pencils are still admitted
        lo, hi = thr + 1, T - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if J(mid) >= i:
                lo = mid
            else:
                hi = mid - 1
        a_i = lo
        if J(a_i) < i:
            break
        total += NT // (T - a_i)
    print(f"greedy heavy-side layer-cake maximum (info only): {total} "
          f"(>> N = {N})")
    _require(total > N, "greedy heavy-side total does not exceed N")

    print("VERDICT: pure counting cannot close the predecessor budget; "
          "minimal open statement = RS exclusion of >= 3 near-threshold "
          "pencils through a base (or the structured-floor pivot)")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
