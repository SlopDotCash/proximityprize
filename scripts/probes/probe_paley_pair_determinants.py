"""Check the pair product and the number of distinct common roots on three sites."""

from itertools import combinations
from math import comb

from probe_paley_shift_multiplicities import determinant, jet_polynomials, multiply, require, trim


def monic(poly, p):
    return [value * pow(poly[-1], -1, p) % p for value in poly]


def euler_power(u, d, p):
    return [comb(d, j) * pow(u, d-j, p) % p for j in range(d+1)]


def multiply_power(value, factor, power, p):
    while power:
        if power % 2:
            value = multiply(value, factor, p)
        power //= 2
        if power:
            factor = multiply(factor, factor, p)
    return value


def baseline(size):
    return (size // 2) * ((size - 1) // 2)


def check(p, A):
    a = len(A)
    d = (p-1)//2
    def central(D, c, width):
        return monic(determinant(jet_polynomials(A, D, width, c, p), width, p), p)
    left = multiply_power(central(d+a-2, 0, a//2), [0, p-1] + [0]*(p-2) + [1], baseline(a), p)
    right = [1]
    forms = {u: euler_power(u, d, p) for u in A}
    for u, v in combinations(A, 2):
        difference = trim([(f-g) % p for f, g in zip(forms[u], forms[v])])
        right = multiply(right, monic(difference, p), p)
    for u in A:
        right = multiply_power(right, [u, 1], (a-1)//2, p)
    require(left == right, (p, A, "central pair decomposition"))

def check_triples(p):
    d = (p-1)//2
    char = [0 if x == 0 else 1 if pow(x, d, p) == 1 else -1 for x in range(p)]
    triples = 0
    for A in combinations(range(p), 3):
        common = sum(all(char[(b+u) % p] == char[(b+A[0]) % p] != 0 for u in A)
                     for b in range(p))
        correction = 0
        for omitted in A:
            u, v = (t for t in A if t != omitted)
            correction += char[(u-omitted) % p] * char[(v-omitted) % p]
        require(4*common == p-6-correction, (p, A, "three-pair common roots"))
        triples += 1
    return triples


def main():
    families = 0
    triples = 0
    for p in (5, 7, 11, 13, 17, 19, 31):
        triples += check_triples(p)
        for size in range(2, min(6, (p+1)//2)+1):
            for index, A in enumerate(combinations(range(p), size)):
                if p > 11 and index not in (0, 1, 3, 7, 19, 53, 113):
                    if index > 113:
                        break
                    continue
                check(p, A)
                families += 1
    print(f"{families} central pair decompositions and {triples} three-coordinate common-root counts")


if __name__ == "__main__":
    main()
