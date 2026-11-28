#!/usr/bin/env python3
"""Test opposite differences and adjacent-root lines over both named prime fields."""

from collections import Counter
from itertools import combinations

from probe_mu128_septic_kernel import FIELDS


def diagonal_triples():
    def representative(triple):
        return min(tuple(sorted((j-h)%64 for j in triple)) for h in triple)
    return sorted({representative((0,a,b)) for a,b in combinations(range(1,64),2)
                   if 32 not in (a,b,b-a)})


def check_field(prime,generator,triples):
    root = pow(generator,(prime-1)//128,prime)
    sites = [pow(root,j,prime) for j in range(128)]
    assert len(set(sites))==128
    fourth = [sites[(4*j)%128] for j in range(32)]
    inverse_differences = [[pow((b-a)%prime,-1,prime) if b!=a else 0 for b in fourth]
                           for a in fourth]
    for phase in range(4):
        scalar = sites[32*phase]
        parity = int(phase%2==0)
        free = (2-phase)%4
        forbidden = (-phase)%4
        histogram = Counter()
        for triple in triples:
            u,v,w = [sites[2*j] for j in triple]
            diagonal = [-u*v*w,u*v+u*w+v*w,-(u+v+w),1]
            fixed = [0]*8
            for j,coefficient in enumerate(diagonal):
                k = 2*j+parity
                fixed[k] = coefficient*pow((1+scalar*sites[(32*k)%128])%prime,-1,prime)%prime
            assert all(fixed[k]==0 for k in (free,free+4,forbidden,forbidden+4))
            excluded = {j%32 for j in triple}
            candidates = [i for i in range(128) if i%32 not in excluded]
            values = {i:sum(c*sites[(i*(k-free))%128] for k,c in enumerate(fixed))%prime
                      for i in candidates}
            largest = 1
            for pos,i in enumerate(candidates):
                by_slope = {}
                for j in candidates[pos+1:]:
                    if i%32==j%32:
                        continue
                    slope = (values[j]-values[i])*inverse_differences[i%32][j%32]%prime
                    by_slope[slope] = by_slope.get(slope,0) | (1<<(j%32))
                largest = max(largest,1+max((m.bit_count() for m in by_slope.values()),default=0))
            histogram[largest] += 1
        expected = {2:114,3:58,4:448} if phase in (0,1) else {2:620}
        assert histogram==expected,(prime,phase,histogram)
        print(f'Prime {prime}, exponent {phase}, line maxima {dict(sorted(histogram.items()))}.')


if __name__=='__main__':
    triples = diagonal_triples()
    assert len(triples)==620
    for parameters in FIELDS:
        check_field(*parameters,triples)
