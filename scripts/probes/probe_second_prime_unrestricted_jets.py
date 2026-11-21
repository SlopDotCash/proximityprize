#!/usr/bin/env python3
"""Integer and rational checks for the ordinary-polar cubic elimination."""

from fractions import Fraction

from probe_second_prime_intrinsic_quartic import require


def main():
    n, d, t = 2**30, 2**26 - 1, 357913943
    weight_cap, minimum_labels, m = 290805098, 1342177249, 34
    polar_degree = 6*m - 9
    simple_labels = minimum_labels - (5*m - 6)
    defect = (10*weight_cap - 16*d - 6)*polar_degree // (simple_labels - polar_degree)
    require(defect == 266, "ordinary Sylvester rank loss")
    mu, s = 32, 400000000
    u = mu*t
    jmax = (u-1)//d
    slots = sum(u-d*j for j in range(jmax+1))
    require((jmax, slots) == (170, 983077772391), "available value degrees")
    require(3*s+m*jmax == 1200005780 < minimum_labels, "value resultant")
    slacks = []
    for w in (3*d, weight_cap):
        # This allows a loss of four times the pole order at value infinity.
        order_bound = Fraction(2*n+16*w-35*d+2*defect, 3)
        variables = (s+1)*Fraction(2*u*w-w*w, 2*d) - jmax*slots
        cost = (s+1-m)*((mu-1)*order_bound+n) + m*n*mu*(mu+1)//2
        slacks.append(int(variables-cost))
    require(slacks == [711166579242392977, 770819534513414215], "concave surplus endpoints")
    print(f"ordinary polar defect <= {defect}, auxiliary value degree <= {jmax}")
    print(f"endpoint dimension margins >= {slacks[0]} and {slacks[1]}")
    print(f"scalar resultant degree <= {3*s+m*jmax} < {minimum_labels} labels")


if __name__ == "__main__":
    main()
