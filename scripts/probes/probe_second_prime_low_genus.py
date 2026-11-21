#!/usr/bin/env python3
"""Terminal genus, jet and polar cutoffs for the surviving second-prime cubic."""

from probe_second_prime_intrinsic_cubic import capacity
from probe_second_prime_intrinsic_quartic import require


def main():
    n, d, t = 2**30, 2**26 - 1, 357913943
    m, h = 34, 2**25
    labels = n + t - m
    require(labels == 1431655733 > m * h, "separate head and Bezout budget")
    W = 290805098
    dim = capacity(h, t, d) - (h + 1) * n
    require(capacity(h-3, t-W-1, d) < dim <= capacity(h-3, t-W, d),
            "weighted section bound")
    mu, s = 2048, 470000000
    jet = mu * (mu+1) // 2
    variables = sum((s-j+1)*(mu*t-j*d) for j in range(3))
    rcap = (variables-1-m*n*jet) // (mu*(s+1-m))
    require(rcap == 1073564022 and 3*s+2*(m-3) < labels,
            "intrinsic terminal resultant and dimension")
    gcap = (rcap-3*W+6*d-12) // 6
    require(gcap == 100633649, "geometric genus cap")
    gcut = (2*n+47*W-78*d-5*rcap+7) // 8
    require(3*(W-d)-gcut == 19462226, "uniform polar margin")
    print(f"labels>={labels}  W<={W}  multiplicity_cap={rcap}")
    print(f"excluded_geometric_genus<={gcap}  polar_margin={3*(W-d)-gcut}")


if __name__ == "__main__":
    main()
