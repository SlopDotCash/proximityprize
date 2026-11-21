#!/usr/bin/env python3
"""Check the signed cross-ratio, projective energy and chart moment formulas exactly."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations
from math import factorial, prod


def require(test, context):
    if not test:
        raise ArithmeticError(context)


def projective_entry(x, y, p, chi):
    a, b = (1, 0) if x is None else (x, 1)
    c, d = (1, 0) if y is None else (y, 1)
    return chi[(a*d-b*c) % p]


def check_gram(p, chi, domain, r):
    gram = [[sum(chi[(a-t) % p]*chi[(a-y) % p] for a in domain)
             for y in range(p)] for t in range(p)]
    direct = sum(k**(2*r) for row in gram for k in row)
    expanded = 0
    for sites in combinations_with_replacement(domain, 2*r):
        multiplicity = factorial(2*r) // prod(factorial(n) for n in Counter(sites).values())
        complete = sum(prod(chi[(a-x) % p] for a in sites) for x in range(p))
        expanded += multiplicity * complete**2
    m = len(domain)
    bound = prod(range(1, 2*r, 2))*p*p*m**r + (2*r-1)**2*p*m**(2*r)
    require(direct == expanded and direct <= bound, ("Gram expansion", p, domain, r))
    for t in range(p):
        finite = [pow((a-t) % p, -1, p) for a in domain if a != t]
        rows = [sum(chi[(x-z) % p] for x in finite) for z in range(p)]
        projective = finite + ([None] if t in domain else [])
        for z in [*range(p), None]:
            full = sum(projective_entry(x, z, p, chi) for x in projective)
            expected = len(finite)*chi[-1] if z is None else rows[z] + int(t in domain)
            require(full == expected, ("conference infinity corrections", p, domain, t, z))
        require(rows[0] == sum(chi[(a-t) % p] for a in domain)
                and abs(rows[0]) <= gram[t][t], ("zero column", p, domain, t))
        for y in range(p):
            if y != t:
                z = pow((y-t) % p, -1, p)
                require(rows[z] == chi[-1]*chi[(y-t) % p]*gram[t][y],
                        ("finite projective row", p, domain, t, y))
        require(sum(v**(2*r) for v in rows) <= sum(k**(2*r) for k in gram[t]),
                ("chart moment", p, domain, t, r))


def quartic_table(p, chi):
    cubic = [sum(chi[x*(x-1)*(x-lam) % p] for x in range(p)) for lam in range(p)]
    require(sum(cubic[2:]) == 1+chi[-1] and sum(x*x for x in cubic[2:]) == p*p-2*p-3,
            ("Legendre moments", p))
    table = {}
    for sites in combinations(range(p), 4):
        quartic = sum(chi[prod(x-s for s in sites) % p] for x in range(p))
        for a, b, c, d in permutations(sites):
            u = (b-c)*pow((b-a) % p, -1, p) % p
            lam = u*(d-a)*pow((d-c) % p, -1, p) % p
            w = chi[((b-a)*(d-c)) % p]
            require(quartic+1 == w*cubic[lam], ("quartic twist", p, a, b, c, d))
            table[a,b,c,d] = (lam, w)
    return table


def projectivities(p):
    # Unique representatives with bottom row (0,1) or (1,t).
    for s, t in [(0, 1)] + [(1, t) for t in range(p)]:
        for u in range(p):
            for v in range(p):
                if (u*t-v*s) % p:
                    images = [None if (s*x+t) % p == 0
                              else (u*x+v)*pow((s*x+t) % p, -1, p) % p
                              for x in range(p)]
                    yield s, t, images


def check_energy(p, chi, domain, table, maps):
    signed, unsigned = Counter(), Counter()
    for sites in permutations(domain, 4):
        lam, w = table[sites]
        signed[lam] += w
        unsigned[lam] += 1
    signed_energy = unsigned_energy = 0
    for s, t, images in maps:
        denominators = [chi[(s*x+t) % p] for x in domain if images[x] in domain]
        k, z = len(denominators), sum(denominators)
        signed_energy += z**4-(6*k-8)*z*z+3*k*k-6*k
        unsigned_energy += k*(k-1)*(k-2)*(k-3)
    require(signed_energy == sum(z*z for z in signed.values()), ("signed incidence", p, domain))
    require(unsigned_energy == sum(z*z for z in unsigned.values()), ("incidence", p, domain))


def main():
    gram_checks = quartics = energy_checks = 0
    for p in (3, 5, 7, 11, 13):
        chi = [0 if x == 0 else 1 if pow(x, (p-1)//2, p) == 1 else -1 for x in range(p)]
        table = quartic_table(p, chi)
        quartics += len(table)
        if p <= 7:
            maps = list(projectivities(p))
            require(len(maps) == p*(p*p-1), ("projective count", p))
            domains = [a for m in range(1, p+1) for a in combinations(range(p), m)]
        else:
            domains = [(0, 1, 2, 4, 5), tuple(range(1, p, 2))]
        for domain in domains:
            for r in (1, 2, 3):
                check_gram(p, chi, domain, r)
                gram_checks += 1
            if p <= 7:
                check_energy(p, chi, domain, table, maps)
                energy_checks += 1
    print(f"{gram_checks} exact Gram and chart moments, {quartics} ordered quartic twists, "
          f"{energy_checks} signed and unsigned projective energies")


if __name__ == "__main__":
    main()
