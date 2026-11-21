#!/usr/bin/env python3
"""Verify the endpoint arithmetic and reconstruct three-head witnesses on small domains."""

from math import prod

from probe_second_prime_intrinsic_quartic import require


def check_witnesses(xs, p, k, e):
    n = len(xs)
    t = n - e
    h = max(0, (3 * (t - 1) - n + 1) // 2)
    private = t - 1 - h
    require(len(set(xs)) == n and t - 1 >= k and h + 1 < k, "core and degree")
    common = set(xs[:h])
    cores = [set(xs[h + i*private:h + (i+1)*private]) for i in range(3)]
    occupied = common.union(*cores)
    directions = (0, 1, 3)
    locator = {x: prod(x - y for y in common) % p for x in xs}

    for c in range(p):
        def heads(x):
            return tuple((locator[x] * a % p, locator[x] * b % p)
                         for a, b in zip((0, x, 2*x+c), directions))

        def label(row, head):
            return ((head[0] - row[0]) * pow(row[1] - head[1], -1, p)) % p

        rows = {x: (0, 0) for x in common}
        witness = {}
        for i, core in enumerate(cores):
            for x in core:
                rows[x] = heads(x)[i]
                for j in range(3):
                    if j != i:
                        witness[label(rows[x], heads(x)[j])] = (j, x)
        if len(witness) == 6 * private:
            break
    else:
        raise ArithmeticError("no separated private-site labels")
    for x in xs:
        if x in occupied:
            continue
        for a in range(p):
            row = (locator[x] * a % p, 2 * locator[x] % p)
            hits = [label(row, head) for head in heads(x)]
            if len(set(hits)) == 3 and witness.keys().isdisjoint(hits):
                rows[x] = row
                witness.update({z: (j, x) for j, z in enumerate(hits)})
                break
        else:
            raise ArithmeticError("no separated free row")

    for z, (i, extra) in witness.items():
        core = common | cores[i]
        require(len(core) >= k and extra not in core, "core pins both rows")
        require(all(rows[x] == heads(x)[i] for x in core), "joint core")
        require(rows[extra] != heads(extra)[i], "no joint extension")
        sites = core | {extra}
        require(len(sites) == t, "witness size")
        for x in sites:
            a, b = heads(x)[i]
            u, v = rows[x]
            require((a + z*b - u - z*v) % p == 0, "folded witness")
    require(len(witness) == 3*(e+1), "distinct witnesses")
    return len(witness)


def main():
    n, k = 2**30, 2**26
    d, t = k-1, 357913943
    p = 730750818665451459101842416358141509841924915201
    lo, hi = 2013265923, 2147483648
    require(hi-lo+1 == 134217726 and p//2**128 == hi, "budget count")
    require(3*n*n < lo*2**128 and 9*n+3 < 3*n*n, "collision exclusions")
    e0 = lo//3-1
    require(2*(e0+1)+1-34 == 1342177249, "minimum cubic population")
    require(3*(e0+1)+1-34 == 2013265890, "minimum quartic population")
    z = t-(n-t)//512
    require(n-3*z+5*d == 339738613 < t, "noncollinear heads")
    for j, expected in ((3, 1484783598), (4, 1224736726)):
        cap = j*n - (j-1)*(j*z - (j * (j-1) // 2)*d)
        require(cap == expected and cap+4*4128+34 < 3*(e0+1)+1, "collinear heads")
    for e in (lo//3, hi//3):
        t = n-e
        h = max(0, (3*(t-1)-n+1)//2)
        require(h <= k-2 and h+3*(t-1-h) <= n and k <= t-1, "locator interval")
    for size, dim, e in ((64, 4, 41), (64, 4, 42), (64, 4, 43), (128, 8, 81)):
        prime = 65537
        xs = [(x*x + 13*x + 7) % prime for x in range(size)]
        print(f"n={size} k={dim} e={e} verified_bad_labels={check_witnesses(xs, prime, dim, e)}")
    print(f"budgets={lo}..{hi} second_prime_first_bad={hi//3}")


if __name__ == "__main__":
    main()
