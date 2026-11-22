#!/usr/bin/env python3
"""Compare independent stratum selections with literal quadratic-character rectangles."""
from math import isqrt
from random import Random


def complementary(length):
    first, second = [1], [1]
    while len(first) < length:
        first, second = first + second, first + [-x for x in second]
    assert len(first) == length
    return first, second


def check_energy():
    rng = Random(281)
    for degree in range(7):
        k = 2**degree
        signs = complementary(k)
        for _ in range(8):
            v = [rng.randrange(-5, 6) for _ in range(2*k)]
            energy = sum(
                sum(row[j]*v[(d+j) % len(v)] for j in range(k))**2
                for row in signs for d in range(len(v))
            )
            assert energy == 2*k*sum(t*t for t in v)


def check_field():
    p, q, n, k = 100129, 20584, 32, 8
    assert all(p % d for d in range(2, isqrt(p)+1))
    assert pow(q, n//2, p) == p-1

    def chi(value):
        residue = pow(value % p, (p-1)//2, p)
        return -1 if residue == p-1 else residue

    assert chi(q) == -1
    powers = [pow(q, i, p) for i in range(n)]
    strata = {}
    products = {}
    for i, x in enumerate(powers):
        for j in range(i, n):
            y = powers[j]
            z = (x+y) % p
            if z:
                assert z not in products
                products[z] = (i+j) % n
                strata.setdefault((i+j) % n, set()).add(z)
    assert len(strata) == n and all(len(v) == n//2 for v in strata.values())
    rng = Random(859)
    first, second = complementary(k)
    total_checks = 0
    for _ in range(24):
        source = {}
        target = {}
        for x in sorted(strata[0]):
            keep = [rng.randrange(2) for _ in range(k//2)]
            source[x] = [keep[j//2] for j in range(k)]
        for y in sorted(strata[1]):
            row = rng.choice((first, second))
            sign = rng.choice((-1, 1))
            target[y] = [(1+sign*t)//2 for t in row]
        a = {powers[i]*x % p for x, row in source.items() for i, bit in enumerate(row) if bit}
        b = {powers[j]*y % p for y, row in target.items() for j, bit in enumerate(row) if bit}
        assert len(a) == sum(map(sum, source.values()))
        assert len(b) == sum(map(sum, target.values()))
        assert a.isdisjoint(b)
        exact = sum(chi(x-y) for x in a for y in b)
        constant = residual = 0
        for x, left in source.items():
            count = sum(left)
            for y, right in target.items():
                lag = {d: chi(x-pow(q, d, p)*y) for d in range(1-k, k)}
                base = sum(lag[k-i-1]-lag[-i-1] for i in range(0, k, 2) if left[i])
                assert abs(base) <= count
                remainder = sum(
                    (-1)**i * lag[j-i] * (2*right[j]-1)
                    for i in range(k) if left[i] for j in range(k)
                )
                assert remainder**2 <= 4*k*k*count
                constant += base
                residual += remainder
        assert 2*exact == constant+residual
        assert residual**2 <= 4*k*k*len(target)**2*len(source)*len(a)
        qa = {q*x % p for x in a}
        qb = {q*y % p for y in b}
        assert abs(exact) <= len(a)*len(b)-len(a & qa)*len(b & qb)
        total_checks += 1
    print(f"{total_checks} independent ordinary rectangles checked at p={p}, n={n}, k={k}")

    # Take one representative per antipodal pair; its full orbit is one H-coset.
    X, Y = [[x for x in sorted(strata[t]) if x < (-x) % p] for t in (0, 1)]
    for sites in (X, Y):
        assert len(sites) == n//4
        assert len({x*t % p for x in sites for t in powers}) == n*len(sites)

    def expand(rows):
        result = {z*powers[i] % p for z, row in rows.items() for i, keep in enumerate(row) if keep}
        assert len(result) == sum(map(sum, rows.values()))
        return result

    field_signs = {z: chi(z) for z in range(p)}
    signs = complementary(n)
    for _ in range(8):
        source = {x: [rng.randrange(2) for _ in powers] for x in X}
        target = {}
        for y in Y:
            sign, row = rng.choice((-1, 1)), rng.choice(signs)
            target[y] = [(1+sign*t)//2 for t in row]
        a, b = expand(source), expand(target)
        exact = sum(field_signs[(z-w) % p] for z in a for w in b)
        total_constant = total_residual = 0
        for x, left in source.items():
            imbalance = sum((-1)**i*bit for i, bit in enumerate(left))
            for y, right in target.items():
                h = [field_signs[(x-t*y) % p] for t in powers]
                total_constant += imbalance*sum(h)
                residual = sum((-1)**i*h[(j-i) % n]*(2*bit-1)
                               for i in range(n) if left[i] for j, bit in enumerate(right))
                assert residual**2 <= 2*n*n*sum(left)
                total_residual += residual
        assert total_constant+total_residual == 2*exact
        assert total_residual**2 <= 2*n*n*len(Y)**2*len(X)*len(a)
    print("Eight full-period power estimates checked on independent ordinary rectangles")

    for d in (2, 4, 8, 16):
        for _ in range(8):
            source, target = {}, {}
            for x in X:
                count = rng.randint(1, n//d)
                selected = {i for r in range(d) for i in rng.sample(range(r, n, d), count)}
                source[x] = [i in selected for i in range(n)]
            for y in Y:
                count = rng.randint(1, d//2)
                residues = set(rng.sample(range(0, d, 2), count))
                residues.update(rng.sample(range(1, d, 2), count))
                target[y] = [i % d in residues for i in range(n)]
            a, b = expand(source), expand(target)
            assert a.isdisjoint(b)
            assert sum(field_signs[(z-w) % p] for z in a for w in b) == 0
    source, target = {}, {}
    for x in X:
        selected = {r+rng.randrange(2)*(n//2) for r in range(n//2)}
        source[x] = [i in selected for i in range(n)]
    for y in Y:
        keep = rng.randrange(2)
        target[y] = [keep if i % (n//2) in (0, 1) else 0 for i in range(n)]
    a, b = expand(source), expand(target)
    assert len(a) == n*n//8 and b and b <= strata[1] | strata[3]
    assert sum(field_signs[(z-w) % p] for z in a for w in b) == 0
    print("Exact periodic cancellation checked at four divisors and on two target strata")


def check_half_density_witness():
    p = 730750818665451459101842416358141509841924915201
    q = 192152681249815148642741928588691886362054863855
    n = 2**30
    y = (pow(q, 44718, p) + pow(q, (1-44718) % n, p)) % p
    assert y == 426431179702536630437099641987827200018168889315
    a = {2*pow(q, 2*i, p) % p for i in range(8)}
    b = {y*pow(q, 2*j, p) % p for j in range(8)}
    assert len(a) == len(b) == 8 and a.isdisjoint(b)
    assert all(pow((x-z) % p, (p-1)//2, p) == p-1 for x in a for z in b)
    print("All 64 differences are nonsquares at density 1/2 on the named control")


def check_universal_masks():
    for n in (2, 4, 8):
        limit = (1 << n)-1
        even = sum(1 << j for j in range(0, n, 2))
        full = n.bit_length()-1

        def balances(mask):
            levels = 0
            for j in range(1, full+1):
                half = 1 << (j-1)
                counts = [sum((mask >> i) & 1 for i in range(t, n, 2*half))
                          for t in range(2*half)]
                if counts[:half] == counts[half:]:
                    levels |= 1 << (j-1)
            return levels

        levels = {m: balances(m) for m in range(1, limit+1)}
        minimal = n*n
        cases = 0
        for a in levels:
            for b in levels:
                cycled = b
                counts = []
                signed = []
                for _ in range(n):
                    both = a & cycled
                    counts.append(both.bit_count())
                    signed.append(2*(even & both).bit_count()-both.bit_count())
                    cycled = (cycled >> 1) | ((cycled & 1) << (n-1))
                parity = bool(levels[a] & levels[b] & 1)
                zeros = all(t == 0 for t in signed)
                assert zeros == (parity and levels[a] | levels[b] == (1 << full)-1)
                assert zeros == (parity and min(counts) == max(counts))
                if zeros:
                    product = a.bit_count()*b.bit_count()
                    assert product % (2*n) == 0
                    minimal = min(minimal, product)
                    cases += 1
        assert minimal == 2*n
        print(f"All {limit**2} nonempty mask pairs at length {n} checked; {cases} cancel")


def check_sharp_second_masks():
    r = 30
    n = 1 << r
    rng = Random(20261121)

    def tree(free_bits):
        sites = [0]
        for j in range(r):
            step = 1 << j
            if j in free_bits:
                sites += [v+step for v in sites]
            else:
                sites = [v+rng.randrange(2)*step for v in sites]
        return set(sites)

    a = tree(set(range(0, r, 2)))
    b = tree({0} | set(range(1, r, 2)))
    assert len(a) == 32768 and len(b) == 65536 and len(a)*len(b) == 2*n
    even = {i for i in a if not i % 2}
    odd = a-even
    lags = [0, 1, n-1, n//2] + [rng.randrange(n) for _ in range(48)]
    for d in lags:
        assert sum((i+d) % n in b for i in even) == 1
        assert sum((i+d) % n in b for i in odd) == 1
    print(f"Sharp period-2^30 masks retain one representation of each sign at {len(lags)} checked lags")


if __name__ == "__main__":
    check_energy()
    check_field()
    check_half_density_witness()
    check_universal_masks()
    check_sharp_second_masks()
    k = 2**20
    positive = complementary(k)[0]
    assert sum(positive) == 1024
    assert 2*10**6 < 62*(32768-1)
    assert 10000*(724+2*k) < 28*1448*((k-1024)//2)
    print("Dyadic energies and second-prime numerical margin checked")
