#!/usr/bin/env python3
"""Prove the affine inequalities uniformly and check all production endpoints."""

from fractions import Fraction as Q
from probe_uniform_three_head_threshold import N_MIN, check, positive_affine


def main():
    for name, degree in (("one sixteenth", lambda n: n/16-1),
                         ("one quarter", lambda n: n/4-1)):
        # Expressions below are affine in d, so checking both endpoints covers the interval.
        positive_affine(name + " linear factor", lambda n:
                        124*(185*(n/3+degree(n))-16*n)-169**2*degree(n))
        positive_affine(name + " quadratic factor", lambda n:
                        (2014-102)*(2*degree(n)-70*n/2048)-2014*degree(n))
        positive_affine(name + " small delta", lambda n: n/15+degree(n)/5-6-8304)
        positive_affine(name + " nonempty third value slot", lambda n: n/3-degree(n))
        positive_affine(name + " h at least two", lambda n:
                        (n-2*degree(n))-(n-3*degree(n)+9)/2)
        positive_affine(name + " enough defining sites", lambda n:
                        n/3+degree(n)-2-(degree(n)+1))
        positive_affine(name + " field size for fresh labels", lambda n:
                        n-2*(2*(2*n/3-degree(n)+2)-n))
    positive_affine("large delta", lambda n: 3*n/8-1-(3+3*n/10)-8304)
    outputs = []
    for den in (4, 8, 16):
        n = N_MIN
        k = n//den
        d = k-1
        E = (n-k+1)//2
        T = (n+3*d+4)//3+1
        U = n-T
        for e in (E-1, E, (E+U)//2, U-1, U):
            t = n-e
            gap = 3*t-3*d-n
            h = 1+(n-2*d)//gap
            first = sum((h+1-j)*(t-j*d) for j in range(3))-(h+1)*n
            second = sum((17-j)*(2*t-j*d) for j in range(5))-50*n
            check(gap >= 5 and first == h*gap-(n-2*d) > 0
                  and second == 150*t-140*d-50*n > 0, "interpolation")
            check(3*h+8304 < e and n-2*t+3*d+4 < t, "two-head cover")
        outputs.append((E, U, 2*(U+1)+1))
    check(outputs == [(402653184,447392426,894784855),
                      (469762048,581610154,1163220311),
                      (503316480,648719018,1297438039)], "production values")
    print("Uniform checks passed for n >= 2^30 and n/16 <= k <= n/4.")
    for den, values in zip((4, 8, 16), outputs):
        print(f"rate 1/{den}: first exact error, last exact error, last budget = {values}")


if __name__ == "__main__":
    main()
