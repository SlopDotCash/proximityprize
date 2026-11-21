#!/usr/bin/env python3
"""Check complete character fourth moments by counting products in each translated domain."""
from collections import Counter
from itertools import combinations, product


def check_domain(p, domain):
    m = len(domain)
    energy = sum(n*n for n in Counter((u + v) % p for u, v in product(domain, repeat=2)).values())
    total = 0
    for b in range(p):
        translated = [(a+b) % p for a in domain if (a+b) % p]
        products = Counter(x*y % p for x, y in product(translated, repeat=2))
        all_characters = (p-1) * sum(n*n for n in products.values())
        total += all_characters - len(translated)**4
    main = p*(2*m*m - m) - 4*m**3 + 4*m*m - m - energy
    exact = (p-1)*main + m*(m-1)*(3*m*m - 3*m + 1)
    if total != exact or not 0 <= total <= (p-1)*p*(2*m*m - m):
        raise ArithmeticError((p, domain, total, exact))


if __name__ == "__main__":
    count = 0
    for prime in (3, 5, 7, 11):
        for size in range(1, prime+1):
            for sites in combinations(range(prime), size):
                check_domain(prime, sites)
                count += 1
    print(f"Exact nonprincipal fourth moments verified on {count} prescribed domains")
