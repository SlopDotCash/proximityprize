#!/usr/bin/env python3
"""Check the small-component counts and terminal high-polar cutoff independently."""


def check(condition, label):
    if not condition:
        raise ArithmeticError(label)


def ceiling(a, b):
    return -(-a // b)


def capacity(h, t, d):
    return sum((h + 1 - j) * (t - j*d) for j in range(min(h, (t-1)//d)+1))


def main():
    n, d, t = 2**30, 2**26 - 1, 357913943
    e, m = n - t, 34
    check(52*(185*t-34*n) > d*151**2, "three linear-component witnesses share >d sites")
    uid = 2*d+1-ceiling(70*n, 2048)
    check(uid == 97517567 and uid*(2014-3*34) > d*2014,
          "three quadratic-component witnesses share >d sites")
    check(34+(e+1)+3*185+4*4128 < 2*n, "only smaller-degree factors")
    labels = 2*n+1-(e+1)-34
    check(labels == n+t-34 == 1431655733, "population after the one possible residual head")

    h, W = 2**25, 290805098
    low = capacity(h, t, d) - (h+1)*n
    check(34*h < labels and capacity(h-3,t-W-1,d) < low <= capacity(h-3,t-W,d),
          "whole interpolation space")
    mu, s = 2048, 470000000
    var = sum((s-j+1)*(mu*t-j*d) for j in range(3))
    A = mu*(mu+1)//2
    rcap = (var - 1 - m*n*A) // (mu*(s+1-m))
    check(rcap == 1073564022 and var-(s+1-m)*mu*rcap-m*n*A == 387914437758,
          "strict local multiplicity budget")
    check(3*s+2*(m-3) == 1410000062 < labels, "distinct scalar roots")
    gmin = ceiling(2*n+47*W-78*d-5*rcap,8)
    gap = 3*(W-d)-gmin
    check(gap == (5*rcap-2*n-23*W+54*d)//8 == 19462226, "minimum polar gap")
    check((2*n+47*W-78*d-8*gmin)//5 <= rcap, "high-polar exclusion")
    e_min, z, exceptions = 671088640, 356515842, 4*4128+34
    required = 3*(e_min+1)+1
    check(2*(e_min+1)+exceptions < required, "at least three large heads")
    check(n-e-e//512 == z and n-3*z+5*d < t, "three independent heads cover")
    for j in (3,4):
        union = j*z-j*(j-1)//2*d
        check(j*n-(j-1)*union+exceptions < required, "collinear large heads")
    min_labels = required-(e_min+1)-34
    check(required-34-144903915>268435546 and min_labels == 1342177249 > 34*h,
          "uniform quartic and cubic population")
    s2 = 440000000
    var2 = sum((s2-j+1)*(mu*t-j*d) for j in range(3))
    cap2 = (var2-1-m*n*A)//(mu*(s2+1-m))
    gmin2 = ceiling(2*n+47*W-78*d-5*cap2,8)
    check(cap2 == 1073558601 and var2-(s2+1-m)*mu*cap2-m*n*A == 694658064894,
          "uniform intrinsic dimension")
    check(3*s2+2*(m-3) < min_labels and 3*(W-d)-gmin2 == 19458838,
          "uniform scalar and polar bounds")
    print(f"small factors excluded; selected cubic labels>={labels}; W<={W}")
    print(f"multiplicity cap={rcap}; uniform polar gap={gap}")


if __name__ == "__main__":
    main()
