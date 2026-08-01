#!/usr/bin/env python3
"""G316 reproducible probe: the depth-3 dyadic wall floor under the naive cap.

Extends G215 (`_G215SharpDyadicWallFloor.lean`) from depth-2 partitions
{1, 2} to depth-3 partitions {1, 2, 3} under the NAIVE cap extension:
the class count cap from G206 is still a+b+c <= m, but k values are now
in {1, 2, 3} and the partition constraint is still a+2b+3c = n-1 = 2m-1.

Maximizing sum k^2 = a + 4b + 9c under these constraints gives the closed
form (derived by the c-bound and 2-of-3 modular step):

    depth-3 floor = 6m - 5               if m mod 3 in {0, 1}
                  = 6m - 3               if m mod 3 == 2

This is strictly above G215's depth-2 floor of 4m-3 at every m >= 2
(m=2 gives 9 vs 5; m=3 gives 13 vs 9; m=160 gives 955 vs 637; etc.).

This probe is a NUMERICAL sanity check of the naive-cap extension, NOT a
Lean claim. G215 explicitly does NOT bound higher-depth S_0; this probe
only checks what the depth-3 floor would look like IF the cap and
partition machinery extend without change. The Lean side can be upgraded
later; until then, claim only the integers actually computed here.

No field data, no float, stdlib only. Reproducible: every n=2m in [4, 398]
is checked by brute-force enumeration AND by the closed form; the two
agree.
"""

def brute_force_depth3(m):
    """Brute-force max of a+4b+9c over (a,b,c) with a+2b+3c = n-1, a+b+c <= m, all >= 0.
    c range: 0..floor((2m-1)/3) (from b_max(c) = m-1 - floor(3c/2) >= 0)."""
    n = 2 * m
    target = n - 1
    c_max = (2 * m - 1) // 3
    best = -1
    best_partition = None
    for c in range(0, c_max + 1):
        for b in range(0, m + 1):
            for a in range(0, m + 1):
                if a + b + c > m:
                    continue
                if a + 2 * b + 3 * c != target:
                    continue
                val = a + 4 * b + 9 * c
                if val > best:
                    best = val
                    best_partition = (a, b, c)
    return best, best_partition


def closed_form_depth3(m):
    """Closed form: 6m - 5 + 2*(m mod 3 == 2)."""
    return 6 * m - 5 + (2 if m % 3 == 2 else 0)


def depth2_floor(m):
    """G215 depth-2 floor: 2n - 3 = 4m - 3."""
    return 4 * m - 3


def main():
    all_ok = True
    rows = []
    for m in range(2, 200):
        n = 2 * m
        bf, bf_part = brute_force_depth3(m)
        cf = closed_form_depth3(m)
        d2 = depth2_floor(m)
        if bf != cf:
            print(f"MISMATCH m={m} n={n}: brute={bf} ({bf_part}) vs closed={cf}")
            all_ok = False
        if cf <= d2:
            print(f"DEPTH3-NOT-STRICT m={m} n={n}: depth-3 {cf} <= depth-2 {d2}")
            all_ok = False
        rows.append((n, m, d2, cf, bf, cf - d2, bf_part, m % 3))
    if not all_ok:
        raise SystemExit(1)
    print(f"G316 depth-3 dyadic wall floor (naive cap): PASS for n=2m, m in [2,199].")
    print(f"  depth-3 floor = 6m - 5         if m mod 3 in {{0, 1}}")
    print(f"                = 6m - 3         if m mod 3 == 2")
    print(f"  strictly above G215's depth-2 floor of 4m-3 at every m >= 2.")
    print()
    print(f"  {'n':>4} {'m':>4} {'m%3':>4} {'depth2':>8} {'depth3':>8} {'brute':>8} {'gap':>6}  witness (a,b,c)")
    for n, m, d2, d3, bf, gap, part, mod3 in rows:
        if n in (4, 6, 8, 10, 12, 16, 20, 24, 28, 32, 48, 64, 96, 128, 192, 256, 320, 384, 398):
            print(f"  {n:>4} {m:>4} {mod3:>4} {d2:>8} {d3:>8} {bf:>8} {gap:>6}  {part}")


if __name__ == "__main__":
    main()
