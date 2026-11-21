"""Exclude all four-head sixteen-fiber constructions of the stated form below 313174699 errors.

The slot bound uses exact rational dual weights. The remaining Hermite interpolation
systems are tested over the first prize field. No numerical solver is used.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement
from math import prod

from probe_rate_half_eight_fibers import G, N, P, require


OMEGA = pow(G, N//16, P)
Y = tuple(pow(OMEGA, i, P) for i in range(16))
SCALE = N//16
TARGET = 4*(N-313174699)
CLASS_TYPES = ((3, 2), (2, 2), (2, 3), (1, 4))  # largest class, number of classes


def dual_prices():
    # Intersections suffice to find the displayed dual certificates. Every pair
    # returned gives a valid inequality, independent of any optimization theorem.
    lines = {(1, 0, 0), (0, 1, 0)}
    for largest, classes in CLASS_TYPES:
        lines.update(((classes-1, 0, largest), (1, 1, 4-largest), (classes, 1, 4)))
    result = []
    for (a,b,c), (d,e,f) in combinations(sorted(lines), 2):
        det = a*e-b*d
        if det:
            label, root = Fraction(c*e-b*f, det), Fraction(a*f-d*c, det)
            if min(label, root) >= 0:
                cap = tuple(max(largest+label, classes*label, 4-root)
                            for largest, classes in CLASS_TYPES)
                result.append((label, root, cap))
    return result


def residual_counts():
    prices = dual_prices()
    residual = []
    for deg in range(8):
        for triples in range(17):
            for doubles in range(17-triples):
                for pairs in range(17-triples-doubles):
                    different = 16-triples-doubles-pairs
                    count = (triples, doubles, pairs, different)
                    if 3*triples+2*doubles+pairs > 6*deg:
                        continue
                    if doubles and triples+2 > 2*deg:
                        continue
                    max_roots = (8-deg)*SCALE-2
                    if any(SCALE*sum(a*b for a,b in zip(count,cap))
                           + root*max_roots-label*(N+1) < TARGET
                           for label,root,cap in prices):
                        continue
                    sizes = [t for t in combinations_with_replacement(range(17), 4)
                             if sum(t) == triples and t[2]+t[3] <= deg]
                    residual.extend((deg,count,part) for part in sizes)
    expected = [(6, (11,0,3,2), (2,3,3,3))]
    expected.extend((7, (13,0,i,3-i), (3,3,3,4)) for i in range(1,4))
    require(residual == expected, 'exact aggregate certificates')
    return residual


def multi_fresh_predecessor():
    errors = 313174698
    labels = N + 1
    per_head = labels - 3 * (errors + 1)
    require(per_head == 134217728 and 1 + errors // 3 < per_head, 'three fresh sites')
    require(2 * (1 + errors // 2) + 2 * (errors + 1) < labels, 'two deficient heads')
    core_lower = 4 * (N - errors - 1) - 1
    fresh_lower = labels + per_head
    degree_term = max(2 * degree - 3 * (degree % 2) for degree in range(8))
    upper = 8 * N + (32 + degree_term) * SCALE - 8 - 2 * fresh_lower
    require(degree_term == 12 and fresh_lower == 1207959553, 'fresh-incidence price')
    require(3 * core_lower == 9126805497 and upper == 9126805494, 'multi-fresh exclusion')
    return 3 * core_lower, upper


def dot(v, w):
    return sum(a*b for a,b in zip(v,w)) % P


def signature(v):
    nonzero = next((x for x in v if x), None)
    if nonzero is None:
        return None
    inv = pow(nonzero, -1, P)
    return tuple(x*inv % P for x in v)


def max_blocks(k):
    seen = set()
    for block in combinations(range(16), k):
        if block in seen:
            continue
        seen.update(tuple(sorted((sign*i+add) % 16 for i in block))
                    for sign in (-1,1) for add in range(16))
        yield block


def mask(block):
    return sum(1 << j for j in block)


def data(T, sizes):
    available = sorted(set(range(16))-set(T))
    blocks = {k: list(combinations(available,k)) for k in sizes}
    nodes = tuple(Y[i] for i in T)
    bary = tuple(pow(prod(z-b for b in nodes if b != z) % P, -1, P) for z in nodes)
    evals = {a: tuple(prod(z-Y[i] for i in a) % P for z in nodes)
             for group in blocks.values() for a in group}
    return blocks, nodes, bary, evals


def sextic_case():
    counts = Counter()
    orbits = 0
    for T in max_blocks(3):
        orbits += 1
        blocks, nodes, bary, evals = data(T, (2,3))
        for A in blocks[2]:
            # The residual polynomial alpha_A is constant. We set it to one.
            weight = tuple(pow(u,-1,P) for u in evals[A])
            weighted = tuple(u*v % P for u,v in zip(weight,bary))
            good = [B for B in blocks[3] if not mask(A)&mask(B) and dot(weighted,evals[B]) == 0]
            for B,C in combinations(good, 2):
                if mask(B)&mask(C):
                    continue
                selected = (A,B,C)
                heads = [[0]*16]
                for block in selected:
                    values = tuple(a*b % P for a,b in zip(weight,evals[block]))
                    slope = (values[1]-values[0])*pow(nodes[1]-nodes[0],-1,P) % P
                    offset = (values[0]-slope*nodes[0]) % P
                    require(all((slope*x+offset)%P == v for x,v in zip(nodes,values)),
                            'normalized residual interpolation')
                    roots = set().union(*(set(M) for M in selected if M != block))
                    heads.append([(slope*x+offset)*prod(x-Y[i] for i in roots)%P for x in Y])
                table = Counter(tuple(sorted(Counter(row).values(),reverse=True)) for row in zip(*heads))
                counts[table[(2,1,1)]] += 1
                require(table[(3,1)] == 11 and table[(2,2)] == 0 and table[(2,1,1)] < 3,
                        'sextic table excluded')
    require(orbits == 21 and counts == {0:37, 1:12}, 'complete sextic census')
    return orbits, counts


def septic_case():
    orbits = triples = plane_pairs = 0
    for T in max_blocks(4):
        orbits += 1
        blocks, nodes, bary, evals = data(T, (3,))
        all_blocks = blocks[3]
        masks = {a:mask(a) for a in all_blocks}
        for index,A in enumerate(all_blocks):
            # The projective weight lies in the plane of evaluations (u+vY)/P_A(Y).
            iA = tuple(pow(u,-1,P) for u in evals[A])
            previous = defaultdict(list)
            for B in all_blocks[index+1:]:
                if masks[A]&masks[B]:
                    continue
                coeff = tuple(u*v*w%P for u,v,w in zip(iA,bary,evals[B]))
                c0, c1, c2 = (sum(u*pow(y,j,P) for u,y in zip(coeff,nodes)) % P for j in range(3))
                if (c0*c2-c1*c1) % P:
                    continue
                plane_pairs += 1
                key = signature((c0,c1)) or signature((c1,c2))
                require(key is not None, 'no coincident constraint planes')
                triples += sum(not masks[C]&masks[B] for C in previous[key])
                previous[key].append(B)
    require(orbits == 72 and triples == 0, 'complete septic census')
    return orbits, plane_pairs, triples


if __name__ == '__main__':
    print('multi-fresh triple core lower and upper bounds', multi_fresh_predecessor())
    print('surviving incidence patterns', residual_counts())
    print('sextic distinguished-block orbits and table counts', sextic_case())
    print('septic distinguished-block orbits, intersecting pairs and triples', septic_case())
