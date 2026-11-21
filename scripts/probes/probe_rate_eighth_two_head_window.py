#!/usr/bin/env python3
"""Uniform checks for the exact two-head rate-eighth interval."""

from fractions import Fraction as Q
from probe_uniform_three_head_threshold import N_MIN, check, positive_affine


def main():
    m, s, a, mu = 11, 10_000_000, 16, 16
    positive_affine("degree-11 cubic source", lambda n: 42*11*n/24-58*(n/8-1)-12*n)
    positive_affine("high polar", lambda n: 5*126*n/100-(
        2*n+23*(11*n/24+2)-54*(n/8-1)+8*n/16))
    positive_affine("intrinsic jets", lambda n: (s-1)*(3*mu*11*n/24-3*n/8)
                    -(s+1)*mu*126*n/100-m*n*mu*(mu+1)/2)
    positive_affine("Jacobian powers", lambda n: (s+1)*(a*n/16-3*n/8)
                    -a*57*(3*a+3)*a*((Q(77,24)-Q(9,8))*n+20))
    positive_affine("cubic scalar roots", lambda n: 7*n/8-10-(3*s+22+110))
    positive_affine("quadratic factor", lambda n: (2014-102)*(2*(n/8-1)-70*n/2048)
                    -2014*(n/8-1))
    positive_affine("linear factor", lambda n: 144*(185*11*n/24-11*n)-174**2*(n/8-1))
    positive_affine("two heads with occupancy above e/3+1", lambda n:
                    (7*n/16-1)/3-1-3*4128-11)
    positive_affine("defining sites", lambda n: 11*n/24-2-n/8)
    n = N_MIN
    d = n//8-1
    t0 = (n+3*d+4)//3+1
    end = n-t0
    check(t0 == 492131670 and end == 581610154 and 2*(end+1)+1 == 1163220311,
          "production endpoints")
    print("All affine comparisons hold for 16|n, n >= 2^30.")
    print(f"n=2^30: exact numerator 2(e+1) for {7*n//16} <= e <= {end}")
    print(f"production upper budget endpoint {2*(end+1)+1}")


if __name__ == "__main__":
    main()
