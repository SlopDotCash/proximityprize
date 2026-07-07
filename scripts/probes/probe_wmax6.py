"""
probe_wmax6.py -- CONCRETE RUNG [Wmax6] of issue #444:  Wmax(6) = 26.

CLAIM
=====
Wmax(6) := the largest sum of squares of multiplicities (Sum_i m_i^2) over signed multiplicity
patterns of six 2^M-th roots of unity that carry a GENUINE multi-root relation (>= 2 distinct
roots) and are NOT a union of antipodal pairs.  This is the elementary input pinning the r=3
RepThree char-p transfer threshold  p > (2*Wmax(6))^{n/4} = 52^{n/4}  for SixTermResultantImproved.

RESULT:  Wmax(6) = 26, attained uniquely by the partition [5,1]  (5^2 + 1^2 = 26).

This file gives TWO independent exact confirmations:
  (1) the pure combinatorial optimisation (max Sum m_i^2 over partitions of 6 into >= 2 parts);
  (2) the structural fact that makes the object well-posed: over CHAR 0 every vanishing integer
      combination of 2^M-th roots IS a union of antipodal pairs (so the non-pairable patterns
      Wmax(6) ranges over are exactly the candidate CHAR-p defects the threshold excludes).
"""

from itertools import combinations, product


# ----------------------------------------------------------------------------------------------
# (1) The combinatorial optimisation:  Wmax(6) = max Sum m_i^2 over partitions of 6 into >=2 parts.
# ----------------------------------------------------------------------------------------------
def partitions(n, minparts=1):
    """Integer partitions of n into >= minparts positive parts (as sorted-desc tuples)."""
    def rec(rem, mx):
        if rem == 0:
            yield ()
            return
        for k in range(min(rem, mx), 0, -1):
            for tail in rec(rem - k, k):
                yield (k,) + tail
    for p in rec(n, n):
        if len(p) >= minparts:
            yield p


def wmax_combinatorial(w):
    """max Sum m_i^2 over partitions of w into >= 2 parts (the GENUINE multi-root regime)."""
    best, arg = -1, None
    table = []
    for p in partitions(w, minparts=2):
        s = sum(x * x for x in p)
        table.append((p, s))
        if s > best:
            best, arg = s, p
    table.sort(key=lambda t: -t[1])
    return best, arg, table


# ----------------------------------------------------------------------------------------------
# (2) Char-0 rigidity of 2^M-th roots: NO non-antipodally-pairable vanishing sums exist.
#     Exact integer arithmetic in the cyclotomic basis  zeta^{2^{M-1}} = -1.
# ----------------------------------------------------------------------------------------------
def cyc_vec(k, N):
    """zeta_N^k as a length-(N/2) integer vector in the basis {zeta^0..zeta^{N/2-1}},
       using zeta^{N/2} = -1."""
    h = N // 2
    v = [0] * h
    kk = k % N
    if kk < h:
        v[kk] = 1
    else:
        v[kk - h] = -1
    return v


def zero_sum_exact(exps, mults, N):
    h = N // 2
    acc = [0] * h
    for k, m in zip(exps, mults):
        vk = cyc_vec(k, N)
        for i in range(h):
            acc[i] += m * vk[i]
    return all(x == 0 for x in acc)


def antipode(k, N):
    return (k + N // 2) % N


def unsigned_pairable(exps, mults, N):
    """The multiset is a union of antipodal pairs:  |m(k)| = |m(antipode k)|  for every k."""
    mp = dict(zip(exps, mults))
    for k, m in mp.items():
        if abs(mp.get(antipode(k, N), 0)) != abs(m):
            return False
    return True


def signed_pairable(exps, mults, N):
    """The signed relation lies in the antipodal Z-span:  m(k) = m(antipode k)."""
    mp = dict(zip(exps, mults))
    for k, m in mp.items():
        if mp.get(antipode(k, N), 0) != m:
            return False
    return True


def char0_rigidity_check(N, maxt, maxabs):
    """Count char-0 vanishing integer combinations of N-th roots that are NOT pairable
       (both readings). For N a power of two this is 0 (Lam-Leung / CensusTowerFinite)."""
    bad_unsigned = bad_signed = 0
    for t in range(1, maxt + 1):
        for exps in combinations(range(N), t):
            for mults in product(range(-maxabs, maxabs + 1), repeat=t):
                if any(m == 0 for m in mults):
                    continue
                if not zero_sum_exact(exps, mults, N):
                    continue
                if not unsigned_pairable(exps, mults, N):
                    bad_unsigned += 1
                if not signed_pairable(exps, mults, N):
                    bad_signed += 1
    return bad_unsigned, bad_signed


if __name__ == "__main__":
    print("=" * 78)
    print("CONCRETE RUNG [Wmax6]:  Wmax(6) = 26")
    print("=" * 78)

    best, arg, table = wmax_combinatorial(6)
    print("\n(1) Combinatorial optimisation -- max Sum m_i^2 over partitions of 6 into >= 2 parts")
    print(f"    Wmax(6) = {best}   attained at partition {arg}   (5^2 + 1^2 = 26)")
    print("    Full genuine (>=2-part) table, descending content:")
    for p, s in table:
        print(f"      {str(list(p)):<22} -> Sum m_i^2 = {s}")
    # the excluded single-root degenerate:
    deg = (6,)
    print(f"    [excluded single-root degenerate {list(deg)} -> {sum(x*x for x in deg)} "
          f"(no genuine multi-root relation; the resultant route discards R = 6*X^k)]")
    assert best == 26 and arg == (5, 1), "Wmax(6) optimisation mismatch"

    print("\n(2) Char-0 rigidity of 2^M-th roots (why the non-pairable patterns are char-p defects)")
    for M in (3, 4):
        N = 1 << M
        bu, bs = char0_rigidity_check(N, maxt=4, maxabs=3)
        print(f"    N=2^{M}={N}: non-pairable char-0 vanishing sums (support<=4, |m|<=3): "
              f"unsigned={bu}, signed={bs}")
        assert bu == 0 and bs == 0, "expected rigidity (no non-pairable char-0 2-power vanishing sums)"
    print("    => every char-0 vanishing integer combo of 2^M-th roots is a union of antipodal")
    print("       pairs; the non-pairable patterns Wmax(6) ranges over are CHAR-p defect")
    print("       candidates, excluded by the threshold p > (2*26)^{n/4} = 52^{n/4}.")

    print("\n" + "=" * 78)
    print(f"Wmax(6) = {best}    2*Wmax(6) = {2*best}    threshold exponent n/4")
    print("MATCH (= 26)" if best == 26 else "MISMATCH")
