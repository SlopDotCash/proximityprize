#!/usr/bin/env python3
"""Classify every prime-field failure of the unit sixth moment at order 64
and the subset passing the weak Sidon, doubled-difference, and directed triple tests.

There is no prime search limit. Every possible unpaired configuration yields
an integer cyclotomic norm. We factor all such norms, verify every factor and
test every split prime divisor on its actual subgroup. Requires GNU factor.
"""

from collections import Counter
from itertools import combinations
from functools import lru_cache
from argparse import ArgumentParser
from math import gcd, prod
from shutil import which
from subprocess import run

from verify_g139_n2e30_arithmetic_contract import is_prime_u64


def require(ok, explanation):
    if not ok:
        raise ArithmeticError(explanation)


def norm(exponents, conductor):
    degree = conductor // 2
    coeff = [0] * degree
    for e in exponents:
        coeff[e % degree] += 1 if e < degree else -1
    while degree > 1:
        half = degree // 2
        out = [0] * half
        # At a root of Y^half+1 the product with the relative conjugate
        # is E(Y)^2 - Y O(Y)^2 for A(X)=E(X^2)+X O(X^2).
        for parity in (0, 1):
            terms = [(i, c) for i, c in enumerate(coeff[parity::2]) if c]
            for i, c in terms:
                for j, d in terms:
                    k = i + j + parity
                    sign = (-1 if parity else 1) * (-1 if k >= half else 1)
                    out[k % half] += sign * c * d
        coeff, degree = out, half
    require(0 < abs(coeff[0]) <= 26**16, "unexpected norm")
    return abs(coeff[0])


@lru_cache(None)
def compositions(weight, size):
    """Positive multiplicities at the ascending exponents."""
    if size == 1:
        return [(weight,)]
    return [(a, *tail) for a in range(1, weight - size + 2)
            for tail in compositions(weight - a, size - 1)]


@lru_cache(None)
def conjugate_powers(conductor, prime):
    """Rows of powers of the odd primitive roots in an auxiliary prime field."""
    require(is_prime_u64(prime) and (prime-1) % conductor == 0, "invalid CRT field")
    for a in range(2, prime):
        root = pow(a, (prime-1)//conductor, prime)
        if pow(root, conductor//2, prime) == prime-1:
            break
    else:
        raise ArithmeticError("missing CRT root")
    return [[pow(root, i*j, prime) for i in range(conductor)]
            for j in range(1, conductor, 2)]


def verify_norm(exps, conductor, value):
    auxiliaries = (562949953423489, 998244353)
    require(prod(auxiliaries) > 26**16, "insufficient CRT range")
    for p in auxiliaries:
        product = 1
        for row in conjugate_powers(conductor, p):
            product = product * sum(row[i] for i in exps) % p
        require(product == value % p, "norm disagrees with product of conjugates")


def norm_values(check_conjugates):
    values, sparse_norms = set(), set()
    for m in (4, 8, 16, 32, 64):
        for weight in (2, 4, 6):
            visited = set()
            for size in range(2, min(weight, m//2) + 1):
                for tail in combinations(range(2, m), size - 2):
                    places = (0, 1, *tail)
                    if len({i % (m//2) for i in places}) < size:
                        continue
                    for counts in compositions(weight, size):
                        exps = tuple(x for x, c in zip(places, counts) for _ in range(c))
                        if exps in visited:
                            continue
                        value = norm(exps, m)
                        if check_conjugates:
                            verify_norm(exps, m, value)
                        values.add(value)
                        if weight == 6 and size >= 5:
                            sparse_norms.add(value)
                        # The translations and odd substitutions preserving the
                        # normalized form have the same absolute norm. Counts
                        # travel with their positions under each permutation.
                        for a in places:
                            for b in places:
                                if (b-a) % 2:
                                    u = pow((b-a) % m, -1, m)
                                    visited.add(tuple(sorted((u*(x-a)) % m for x in exps)))
    return values, sparse_norms


def candidate_primes(norms, sparse_norms):
    command = which("gfactor") or which("factor")
    require(command, "GNU factor is needed")
    raw = run([command], input="".join(f"{v}\n" for v in sorted(norms)), text=True,
              capture_output=True, check=True).stdout
    primes, covered, sparse = set(), set(), set()
    for line in raw.splitlines():
        value, factors = line.split(":")
        factors = [int(v) for v in factors.split()]
        require(prod(factors) == int(value), "incorrect factor product")
        covered.add(int(value))
        primes.update(factors)
        if int(value) in sparse_norms:
            sparse.update(factors)
    require(covered == norms, "incomplete factorization")
    @lru_cache(None)
    def certified_prime(p):
        if p < 1 << 64:
            return is_prime_u64(p)
        line = run([command, str(p-1)], text=True, capture_output=True, check=True).stdout
        fs = [int(t) for t in line.split(":")[1].split()]
        require(prod(fs) == p-1 and all(certified_prime(q) for q in fs), "bad p-1 factors")
        # Full Lucas/Pocklington factorization. Each prime divisor of p-1
        # can use its own coprimality witness.
        return all(any(pow(a, p-1, p) == 1 and gcd(pow(a, (p-1)//q, p)-1, p) == 1
                       for a in range(2, 257)) for q in set(fs))
    require(all(certified_prime(p) for p in primes), "uncertified factor")
    return sorted(p for p in primes if p % 64 == 1), {p for p in sparse if p % 64 == 1}


def subgroup(p):
    n = 64
    for a in range(2, p):
        g = pow(a, (p - 1) // n, p)
        if pow(g, n // 2, p) == p - 1:
            break
    else:
        raise ArithmeticError("missing generator")
    return [pow(g, i, p) for i in range(n)]


def quarter_and_rectangle_tests(p):
    roots = subgroup(p)
    n = len(roots)
    quarter = [pow(c + x, n, p)
               for c, omit in [(2, {n//2}), (1 + roots[n//4], {0, n//4, n//2, 3*n//4})]
               for j, x in enumerate(roots) if j not in omit]
    quarter_pass = len(set(quarter)) == 2*n-5 and not {0, 1}.intersection(quarter)
    pair_sums = {(a+b) % p for a in roots for b in roots}
    tags = {x: pow(1+x, n, p) for x in roots if x != p-1}
    occupied = set(tags.values())
    rectangles = 0
    for r in tags:
        for q in tags:
            if (q+r) % p == 0 or (q*r+1) % p == 0:
                continue
            direct = ((1+r)*(1+q)) % p in pair_sums
            projected = (tags[r]*tags[q]) % p in occupied
            require(direct == projected, "pair-sum and projective rectangle checks disagree")
            rectangles += direct
    return quarter_pass, rectangles


def energy_and_tests(p):
    roots = subgroup(p)
    n = len(roots)
    signs = {pow(x - 1, n, p) for x in roots[1:n // 2 + 1]}
    two = pow(2, n, p)
    admissible = (len(signs) == n//2 and pow(3, n, p) != 1
                  and all((s*two) % p not in signs for s in signs)
                  and all(pow(3-x, n, p) not in signs for x in roots[1:]))
    # The two free variables are symmetric. Each unequal pair occurs twice.
    profile = Counter()
    for i, x in enumerate(roots):
        for y in roots[:i]:
            profile[pow(1 + x + y, n, p)] += 2
        profile[pow(1 + 2*x, n, p)] += 1
    zero = profile.pop(0, 0)
    return n * sum(c*c for c in profile.values()) + (n*zero)**2, admissible


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--check-conjugates", action="store_true",
                        help="check each integer norm by CRT over two auxiliary fields")
    args = parser.parse_args()
    norms, sparse_norms = norm_values(args.check_conjugates)
    primes, sparse_primes = candidate_primes(norms, sparse_norms)
    exceptions, sparse_exceptions = [], []
    for p in primes:
        energy, admissible = energy_and_tests(p)
        if p * (energy - 15*64**3) > 64**6:
            exceptions.append(p)
            if admissible:
                require(p in sparse_primes, "missing sparse norm")
                sparse_exceptions.append(p)
    print(f"norms={len(norms)} split_divisors={len(primes)}")
    print(f"sparse_norms={len(sparse_norms)} sparse_split_divisors={len(sparse_primes)}")
    print(f"all_exceptions={len(exceptions)}")
    print(" ".join(map(str, exceptions)))
    print(f"exceptions_passing_sparse_tests={len(sparse_exceptions)}")
    print(" ".join(map(str, sparse_exceptions)))
    extended = {p: quarter_and_rectangle_tests(p) for p in sparse_exceptions}
    for name, passing in [
        ("quarter", [p for p, (q, _) in extended.items() if q]),
        ("rectangle", [p for p, (_, r) in extended.items() if r == 0]),
        ("quarter_and_rectangle", [p for p, (q, r) in extended.items() if q and r == 0]),
    ]:
        print(f"exceptions_passing_sparse_and_{name}={len(passing)}")
        print(" ".join(map(str, passing)))


if __name__ == "__main__":
    main()
