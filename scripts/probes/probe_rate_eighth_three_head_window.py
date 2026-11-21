#!/usr/bin/env python3
"""Uniform affine and rational bounds for the rate-eighth three-head theorem."""

from fractions import Fraction as Q
from probe_uniform_three_head_threshold import N_MIN, check, positive_affine


def main():
    t = Q(13,32)
    w = Q(814,1000)
    z = Q(406,1000)
    a, mu, s = 16, 64, 70_000_000
    positive_affine("initial double interpolant", lambda n:
                    1008*t*n-1484*(n/8-1)-224*n)
    positive_affine("independent triple interpolant", lambda n:
                    705*t*n-975*(n/8-1)-164*n)
    positive_affine("nonempty source slots", lambda n: 2*t*n-6*(n/8-1))
    positive_affine("nonempty triple slots", lambda n: 3*t*n-9*(n/8-1))
    positive_affine("weight upper bound", lambda n: w*n-2*(t*n+5))
    positive_affine("nonhead linear component", lambda n:
                    (4096-74-3*73)*(4096*t*n-74*n)-(4096-74)**2*(n/8-1))
    positive_affine("high value degree", lambda n: 210*(n/8-1)-mu*(t*n+5))
    positive_affine("low value degree", lambda n: 90*(n/8-1)-a*(w*n-(n/8-1)))
    positive_affine("quadratic truncation loss", lambda n:
                    2*Q(27,10)*(n/8-1)-w*w*n)
    positive_affine("jet variable surplus", lambda n:
                    ((s-209)*(Q(mu,12)-Q(27,10))-210*mu*6-27*(mu*(mu+1)//2))*n)
    for b in range(2, 7):
        check(5*8*t-(2+Q(8,a))*b-1 >= Q(1,4), "positive derivative in the weight")
        margin = 5*b*t-((1+Q(4,a))*b*b+2*b)/8-(2+Q(8,a))
        check(margin > Q(5,12), "high polar endpoint")
        vmax = max((a+1)*b-1,90)
        positive_affine("low polar matrix dimensions", lambda n:
                        (s+1)*n-a*(54*b-b*b)*(vmax+1)*a*(
                            (2*b+1)*w*n-b*b*(n/8-1)-b))
        check(27*210<8500 and 27*90+400<8500 and (2*b-1)*27-b*b <400,
              "scalar resultant and simple-section exceptions")
    positive_affine("small component allowance", lambda n: (7*n/12-1)/8-s-8500)
    positive_affine("two large heads insufficient", lambda n: (7*n/12-1)/2-77)
    positive_affine("large core size", lambda n: t*n-7-z*n)
    positive_affine("small head occupancy", lambda n: Q(75,1000)*n-(1-t)*n/8-1)
    for j in range(3,7):
        coverage = max(j*z-Q(j*(j-1),16), (j*z)**2/(j*z+Q(j*(j-1),8)))
        positive_affine("collinear head coverage", lambda n:
                        (Q(7,4)-j+(j-1)*coverage-(6-j)*Q(75,1000))*n-74)
    n = N_MIN
    d = n//8-1
    first = 7*n//12+1
    last = n-((n+5*d+21)//4+1)
    check((first, last, 3*first, 3*(last+1)+2) ==
          (626349398,637534203,1879048194,1912602614), "production endpoints")
    print("Uniform integer inequalities passed for 16|n, n >= 2^30.")
    print(f"Production error interval [{first}, {last}], budget interval [{3*first}, {3*(last+1)+2}]")


if __name__ == "__main__":
    main()
