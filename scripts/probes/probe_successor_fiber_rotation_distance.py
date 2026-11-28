#!/usr/bin/env python3
"""Check prime-field Fourier minors, four-step losses, and an order-four matrix entry."""
from itertools import permutations, product


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def four_step_controls():
    """Test every balanced 2+2+2+2 coloring on an eight-cycle."""
    for assignment in set(permutations((0, 0, 1, 1, 2, 2, 3, 3))):
        colors = [{i for i, value in enumerate(assignment) if value == j} for j in range(4)]
        shift = lambda sites, steps: {(i+steps) % 8 for i in sites}
        losses = [len(shift(sites, 1)-colors[(j+1) % 4]) for j, sites in enumerate(colors)]
        w = len(shift(colors[2], 1) & colors[0])
        require(sum(losses) <= 3*(losses[0]+losses[1])+2*w, "single-step losses")
        require(sum(len(shift(c, 4)-c) for c in colors[:3]) <= 3*sum(losses),
                "four-step union bound")

    for coefficients in product(range(1, 6), repeat=4):
        a, b, c, d = 1, 0, 0, 1
        for z in coefficients:
            a, b, c, d = -c, -d, z*a+c, z*b+d
        require(b == coefficients[1]+coefficients[2]-1, "four-factor upper right")


def check_field(n, p, order, degree):
    require(n % order == 0 and (p-1) % n == 0, "subgroup size")
    generator = next(w for a in range(2, 100)
                     if pow(w := pow(a, (p-1)//order, p), order//2, p) != 1)
    roots = [pow(generator, i, p) for i in range(order)]
    require(len(set(roots)) == order and pow(generator, order, p) == 1, "primitive root")
    phases = [(i, (i*degree) % order) for i in range(order)]
    denominators = [(i, c, pow(roots[c]-1, -1, p)) for i, c in phases if c]
    tested = 0
    for j in range(order):
        seen = {}
        for i, c, reciprocal in denominators:
            k = (i*j) % order
            if k == 0 or k == c:
                continue
            ratio = (roots[k]-1)*reciprocal % p
            if seen.setdefault(ratio, c) != c:
                raise ArithmeticError(f"nontrivial collision for exponent {j}")
            tested += 1
    return tested


def main():
    n = 2**30
    p = n*(2**128+192)+1
    four_step_controls()
    for d, floor in ((n//4-2, 17895696), (n//4-1, 17895697)):
        q = n-4*d
        require(15*(floor-1)+3*q < d+2 <= 15*floor+3*q, "integer loss threshold")
        total = check_field(n, p, 4096, d)
        require(total == 16723968, "tested Fourier ratios")
        print(f"Degree {d:,}: {total:,} nontrivial ratios, loss floor {floor:,}.")
    require(32768*32767 <= n-1 < 32769*32768, "Sidon ceiling")


if __name__ == "__main__":
    main()
