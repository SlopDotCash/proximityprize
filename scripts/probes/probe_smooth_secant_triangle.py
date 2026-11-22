"""Reconstruct the two received rows and every triangle label at toy dyadic lengths."""

from itertools import combinations
from math import comb, prod

from probe_many_head_locator_attack import require


def verify(n, prime, generator):
    s = n // 16
    a, residue = divmod(s, 3)
    b = residue - 1
    require(b in (0, 1), "nonzero dyadic residue")
    g = pow(generator, (prime-1)//n, prime)
    require(pow(g, n//2, prime) == prime-1, "exact subgroup order")
    points = [pow(g, i, prime) for i in range(n)]
    quotient = [pow(x, n//4, prime) for x in points]
    edges = list(combinations(quotient[:3], 2))
    cuts = [2*a, 2*a, 2*a, s, 0, 0, 0, s, 0, 0, 0, b, 0, 0, 0, 0]
    roots = [x for i, x in enumerate(points) if i//16 < cuts[i % 16]]
    require(len(roots) + n//4 + 1 < n//2, "polynomial degrees")
    locator = [prod(x-r for r in roots) % prime for x in points]
    v = [t*t % prime for t in quotient]
    u = [int(i % 4 == 3) for i in range(n)]
    heads = [[((y+z)*t-y*z) % prime for t in quotient] for y, z in edges]
    keys = []
    cores = []
    for h in heads:
        common = set()
        for i, x in enumerate(points):
            if locator[i] == 0 or (u[i] == 0 and h[i] == v[i]):
                common.add(i)
            else:
                require(h[i] != v[i], "second head misses at the fresh site")
                keys.append((len(cores), i, u[i]*pow((h[i]-v[i]) % prime, -1, prime) % prime, x))
        cores.append(common)
    expected = 3*(n//3+1)
    require(len(keys) == expected and comb(expected, 2) <= prime, "available labels")
    for slope in range(prime):
        labels = [(key-slope*x) % prime for _, _, key, x in keys]
        if len(set(labels)) == expected:
            break
    else:
        raise ArithmeticError("no separating shear")
    first = [j*(u0+slope*x*v0) % prime for x, j, u0, v0 in zip(points, locator, u, v)]
    second = [j*v0 % prime for j, v0 in zip(locator, v)]
    for (head, i, _, _), label in zip(keys, labels):
        support = cores[head] | {i}
        require(len(support) == n-n//3, "required number of agreements")
        require(locator[i]*heads[head][i] % prime != second[i], "no joint extension")
        for k in support:
            coded = locator[k]*heads[head][k]*(slope*points[k]+label)
            require((coded-first[k]-label*second[k]) % prime == 0, "combined word agrees")
    print(f"n={n} p={prime} e={n//3} roots={len(roots)} shear={slope} distinct labels={expected}")


if __name__ == "__main__":
    # Standard primitive generators of the two prime fields.
    verify(16, 193, 5)
    for length in (32, 64, 128, 256, 512, 1024):
        verify(length, 998244353, 3)
