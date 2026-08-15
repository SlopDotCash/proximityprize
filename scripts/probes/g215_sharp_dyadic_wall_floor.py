#!/usr/bin/env python3
"""G215 reproducible probe: the SHARP depth-2 dyadic wall floor.

Verifies, purely arithmetically (float-free), the three constants proven in
`_G215SharpDyadicWallFloor.lean`:

  1. crossOrbitTail_two_floor_sharp:  n^2*(2n-3) <= sum_gamma S_gamma^2,
     with the tight witness (flat partition [1,2,...,2]) attaining n^2*(2n-3).
  2. sharp_gt_cauchy_schwarz (tail level):  2n(n-1)^2 < n^2(2n-3)  for even n>=4.
  3. dyadic_wall_floor_two_sharp (wall level): the cross-orbit contribution
     n(2n-3) strictly exceeds G206's Cauchy-Schwarz contribution 2(n-1)^2
     for even n>=4, and the wall floor after the Parseval /n-division is
     q*(n^2 + n(2n-3)) - n^4.

No field data is needed: G215 is the pure-N partition floor wired onto the
CORE object via the mass quantisation S_gamma = n*k_gamma (G88) and the
class-count cap card <= n/2 (G206).  This probe checks the closed-form
constants and the tight witness at the extremal (flat) partition.
"""

def sumsq_flat(m):
    # flat minimiser [1, 2, 2, ..., 2]: one 1 and (m-1) twos, sum = 2m-1 = n-1
    return 1 * 1 + (m - 1) * (2 * 2)

def main():
    all_ok = True
    for m in range(2, 200):
        n = 2 * m
        # 1. flat witness attains the sharp tail floor n^2*(2n-3)?  (per-class k^2 form)
        flat = sumsq_flat(m)                 # = sum k^2
        assert flat == 2 * n - 3, (n, flat, 2 * n - 3)
        tail_sharp = n * n * (2 * n - 3)     # = n^2 * sum k^2 at the floor
        assert n * n * flat == tail_sharp
        # 2. tail-level sharp > Cauchy-Schwarz for even n>=4
        cs_tail = 2 * n * (n - 1) ** 2
        if n >= 4:
            assert cs_tail < tail_sharp, (n, cs_tail, tail_sharp)
        # 3. wall-level cross contribution: n(2n-3) (sharp) vs 2(n-1)^2 (CS)
        wall_sharp_cross = n * (2 * n - 3)
        wall_cs_cross = 2 * (n - 1) ** 2
        if n >= 4:
            assert wall_cs_cross < wall_sharp_cross, (n, wall_cs_cross, wall_sharp_cross)
        # consistency: tail/n = wall cross (the Parseval /n division)
        assert tail_sharp % n == 0
        assert tail_sharp // n == wall_sharp_cross
    print("G215 sharp dyadic wall floor: ALL constant/witness/gap checks PASS "
          "for n=2m, m in [2,199].")
    # spot table
    for m in (2, 4, 8, 16):
        n = 2 * m
        print(f"  n={n:3d}: tail_sharp=n^2(2n-3)={n*n*(2*n-3):>10d}  "
              f"cs_tail=2n(n-1)^2={2*n*(n-1)**2:>10d}  "
              f"wall_cross_sharp=n(2n-3)={n*(2*n-3):>6d}  "
              f"wall_cross_cs=2(n-1)^2={2*(n-1)**2:>6d}")
    return all_ok

if __name__ == "__main__":
    main()
