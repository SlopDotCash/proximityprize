#!/usr/bin/env python3
"""Exact positive-slope certificates for the uniform three-head theorem."""

from fractions import Fraction as Q

N_MIN = 2**30
S = 400_000_000
MU = 64
MODELS = {3: (2**25, Q(271, 1000), Q(99, 100)),
          4: (119, Q(283, 1000), Q(1319, 1000))}


def check(condition, name):
    if not condition:
        raise ArithmeticError(name)


def positive_affine(name, difference):
    # Each caller gives an explicit affine expression in the real variable n.
    intercept = difference(Q(0))
    slope = difference(Q(1)) - intercept
    check(slope >= 0 and slope*N_MIN + intercept > 0, name)
    check(difference(Q(N_MIN)) == slope*N_MIN+intercept, name + " affine formula")


def d(n):
    return n/16 - 1


def t_low(n):
    return n/3 - 2


def main():
    check(min(55*(-3-r)+320 for r in (0, 1, 2)) == 45, "first quartic surplus")
    positive_affine("value-degree support below", lambda n: t_low(n)-5*d(n))
    positive_affine("value-degree support above", lambda n: 6*d(n)-n/3)
    positive_affine("linear component", lambda n: 52*(185*t_low(n)-34*n)-151**2*d(n))
    positive_affine("quadratic component", lambda n:
                    (2014-102)*(2*d(n)-70*n/2048)-2014*d(n))
    positive_affine("at least three large heads", lambda n: 5*n/8-4*4128-34)
    positive_affine("large head core", lambda n: t_low(n)-(n-t_low(n))/512-331*n/1000)
    positive_affine("three noncollinear heads", lambda n: t_low(n)-(n-3*331*n/1000+5*d(n)))
    for j in (3, 4):
        positive_affine("collinear large heads", lambda n:
                        15*n/8+1-(j*n-(j-1)*(j*331*n/1000-(j*(j-1)//2)*d(n))+4*4128+34))
    for b, (h, w, rcap) in MODELS.items():
        population = Q(5,4) if b == 3 else Q(15,8)
        positive_affine("initial Bezout", lambda n: population*n-34-34*h)
        positive_affine("quotient has one coordinate slot", lambda n: d(n)-(n/3-w*n))
        positive_affine("quotient positive at threshold", lambda n: t_low(n)-w*n)
        positive_affine("weight comparison", lambda n:
                        (6*h-9)*t_low(n)-(15*h-40)*d(n)-(h+1)*n
                        -(h-b+1)*(t_low(n)-w*n))
        if b == 4:
            positive_affine("quartic local orders", lambda n: 7*rcap*n-(6*n+22*w*n-48*d(n)))
        else:
            positive_affine("cubic local orders", lambda n:
                            5*rcap*n-(2*n+23*w*n-54*d(n)+8*(n/90+1)))
        positive_affine("jet variables", lambda n:
                        (S-b+2)*(b*MU*t_low(n)-(b*(b-1)//2)*n/16)
                        -(S+1)*MU*rcap*n-34*n*(MU*(MU+1)//2))
        positive_affine("scalar resultant", lambda n:
                        population*n-34-(b*S+(b-1)*(34-b)))
    a = 40
    positive_affine("low polar matrix", lambda n:
                    (S+1)*n*(Q(a,90)-Q(3,16))
                    -195*a*(3*a+3)*a*(7*271*n/1000-9*n/16+6))
    positive_affine("simple-root exclusions", lambda n: 5*n/4-34-34*33-(3*S+68))
    positive_affine("new coordinates have ample witnesses", lambda n: t_low(n)-2-n/16)
    check(3*N_MIN**2 > 6*N_MIN + 102, "extra-site avoidance")
    # For n=3r+i, e_max+1=2r+i+2. Check all possible endpoint residues.
    for rem in (0, 1, 2):
        check(3*(rem+2)+2 - 2*rem == 8+rem, "budget upper endpoint")
        check(rem+9 <= 11, "at most eleven extra sites")
    print("Uniform inequalities hold for all n >= 2^30, 16 dividing n.")
    print("For k=n/16 the budget interval is [15n/8+3, 2n+8+(n mod 3)].")


if __name__ == "__main__":
    main()
