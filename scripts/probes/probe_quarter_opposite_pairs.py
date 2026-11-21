#!/usr/bin/env python3
"""Classify the six labelled double strata on the 16-site quarter-rate control."""
import argparse
from collections import Counter
from itertools import combinations, product
from math import prod

N = 16
FULL = (1 << N) - 1


def indices(mask):
    return tuple(i for i in range(N) if mask >> i & 1)


def subsets(mask, size):
    return tuple(sum(1 << i for i in s) for s in combinations(indices(mask), size))


def dihedral(mask):
    return {sum(1 << ((r + s*i) % N) for i in indices(mask))
            for r in range(N) for s in (1, -1)}


def census(p, generator, visit=None):
    zeta = pow(generator, (p-1)//N, p)
    assert pow(zeta, 8, p) == p-1
    x = [pow(zeta, i, p) for i in range(N)]
    neg = []
    for u in x:
        neg.append(sum(1 << j for j, v in enumerate(x)
                       if pow((u-v) % p, (p-1)//2, p) == p-1))
    pairs = {s: subsets(s, 2) for s in subsets(FULL, 4)}
    bits = {s: indices(s) for s in pairs}
    pair_sites = {s: indices(s) for s in subsets(FULL, 2)}
    first = lambda mask: (mask & -mask).bit_length()-1
    # Evaluating each monic six-root locator at the 16 roots makes exact rank tests cheap.
    val, inv = {}, {}
    for s in subsets(FULL, 6):
        roots = [x[i] for i in indices(s)]
        val[s] = tuple(prod((v-u) % p for u in roots) % p for v in x)
        inv[s] = tuple(pow(v, -1, p) if v else 0 for v in val[s])

    # A primitive fourth root identifies the multiplicative quartic character with Z/4.
    fourth_root = pow(zeta, N//4, p)
    quartic_logs = {pow(fourth_root, e, p): e for e in range(4)}

    def quartic(value):
        return quartic_logs[pow(value % p, (p-1)//4, p)]

    def value(mask, site):
        return prod((x[site]-x[j]) % p for j in indices(mask)) % p

    def check_characters(holes, blocks, positive, coeff):
        discriminant = prod(coeff) % p
        theta = quartic(discriminant) % 2
        for i, block in enumerate(blocks):
            j, k = (i+1) % 3, (i+2) % 3
            plus = quartic(-coeff[k+1]*pow(coeff[j+1], -1, p))
            minus = quartic(-coeff[i+1]*pow(coeff[0], -1, p))
            side_size = positive[i].bit_count()
            # Multiply the locator derivative formula over this whole block.
            parity_product = prod((-x[u]) % p for u in indices(block))
            parity_product *= prod(value(block, h) for h in indices(holes))
            assert quartic(parity_product) % 2 == theta*side_size % 2
            for site in indices(block):
                log_j = quartic(value(blocks[j], site))
                log_k = quartic(value(blocks[k], site))
                is_positive = positive[i] >> site & 1
                rhs = plus + log_j - log_k if is_positive else minus + log_j + log_k
                lhs = (neg[site] & (positive[j] | positive[k])).bit_count()
                assert (rhs - 2*lhs) % 4 == 0
                if theta == 0:
                    # With split discriminant this is one affine binary constraint per site.
                    r_plus, r_minus = (plus+log_j-log_k) % 4, (minus+log_j+log_k) % 4
                    assert r_plus % 2 == r_minus % 2 == 0
                    assert (lhs - r_minus//2 - is_positive*((r_plus-r_minus)//2)) % 2 == 0

    def relation(blocks, positive):
        a, b, c = positive
        aa, bb, cc = (block ^ side for block, side in zip(blocks, positive))
        faces = (a|b|c, a|bb|cc, aa|b|cc, aa|bb|c)
        lead = val[faces[0]]
        coeff = [1]
        # On each negative side only the leading face and one other face survive.
        for face, side in zip(faces[1:], (aa,bb,cc)):
            i, j = pair_sites[side]
            scalar = -lead[i]*inv[face][i] % p
            if (lead[j] + scalar*val[face][j]) % p:
                return None
            coeff.append(scalar)
        # Degree six: seven distinct evaluation sites certify the identity.
        for i in range(7):
            if sum(scalar*val[face][i] for scalar,face in zip(coeff,faces)) % p:
                return None
        return tuple(coeff)

    seen = set()
    count = Counter()
    survivor = None
    for holes in subsets(FULL, 4):
        if holes in seen:
            continue
        orbit = dihedral(holes)
        seen.update(orbit)
        mult = len(orbit)
        ordinary = FULL ^ holes
        minus = {s:sum(1 << i for i in bits[s] if (neg[i] & (ordinary ^ s)).bit_count() % 2)
                 for s in subsets(ordinary, 4)}
        for u in minus:
            if not (u >> first(ordinary) & 1):
                continue
            left = ordinary ^ u
            for v in subsets(left, 4):
                if not (v >> first(left) & 1):
                    continue
                union = (u,v,left ^ v)
                signs = tuple(minus[s] for s in union)
                count['coarse'] += mult
                if all(m in (0,s) for m,s in zip(signs,union)):
                    if sum(bool(m) for m in signs) % 2:
                        continue
                    count['split coarse'] += mult
                    options = product(*(pairs[s] for s in union))
                elif all(m.bit_count()==2 for m in signs):
                    count['nonsplit coarse'] += mult
                    options = (head for head in product(*[(m,s^m) for s,m in zip(union,signs)])
                               if sum(a == m for a,m in zip(head,signs)) % 2 == 0)
                else:
                    continue
                for head in options:
                    count['orientation tests'] += mult
                    c = relation(union, head)
                    if c is not None:
                        check_characters(holes, union, head, c)
                        if visit is not None:
                            visit(holes,union,head,c,mult)
                        count['relations'] += mult
                        if survivor is None:
                            survivor = holes,union,head,c
    assert len(seen)==1820 and count['coarse']==10510500
    print(p, dict(count), 'first survivor', survivor, flush=True)
    return count


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fields', nargs='+', default=['97', '65537'],
                        choices=['97', '65537', 'first', 'second'])
    args = parser.parse_args()
    primes = {'97': 97, '65537': 65537,
              'first': 365375409332725729550921208179070755120141565953,
              'second': 730750818665451459101842416358141509841924915201}
    for name in args.fields:
        p = primes[name]
        generator = next(a for a in range(2, 256) if pow(a, (p-1)//2, p) == p-1)
        report = census(p, generator)
        assert report['relations'] == (1792 if p == 97 else 1344)
