#!/usr/bin/env python3
# wf407w2_L4-onq_onset.py
#
# Thread L4-onq (#407). Onset lever, SHARPENED.
#
# min|N(e2(S))| over alpha!=0 is tiny ({1,2}) but those are UNITS / 2-power norms
# (harmless: no prime q=1 mod n divides them, since q=1 mod n is odd and >n).  The TRUE
# onset = the smallest GENUINE adversarial prime = smallest q=1 mod n, q>(mu-1)*n
# (post-saturation), with q | N(e2(S)) for some window set S.  Equivalently the smallest
# carrier norm with an ODD prime factor =1 mod n.
#
# We also confirm: a prime q=1 mod n is a carrier  <=>  q | N(alpha) for some alpha=e2(S),
# and we read off the smallest such q in the post-saturation regime q>(mu-1)*n.
#
# EXACT. Run: python <thisfile>

import itertools
from math import comb
from sympy import symbols, Poly, resultant, cyclotomic_poly, factorint, isprime

X = symbols('X')

def vec_e2(A, n):
    h = n//2
    v = [0]*h
    L = list(A)
    for a in range(len(L)):
        for b in range(a+1, len(L)):
            e = (L[a]+L[b]) % n
            if e < h: v[e] += 1
            else: v[e-h] -= 1
    return tuple(v)

def field_norm(v, Phi):
    a = Poly(sum(c*X**i for i, c in enumerate(v)), X)
    return int(resultant(Phi, a))

def carrier_primes(n, w):
    Phi = Poly(cyclotomic_poly(n, X), X)
    seeds = set()
    for A in itertools.combinations(range(n), w):
        v = vec_e2(A, n)
        if any(v): seeds.add(v)
    prime_carriers = set()
    norm_of_prime = {}
    for v in seeds:
        N = field_norm(list(v), Phi)
        if N == 0: continue
        for q, e in factorint(abs(N)).items():
            if q % n == 1 and q > 2:
                prime_carriers.add(q)
                norm_of_prime.setdefault(q, abs(N))
    return sorted(prime_carriers), norm_of_prime

if __name__ == "__main__":
    print("wf407-w2 / L4-onq : ONSET prime (smallest GENUINE adversarial q) — sharpened")
    print("="*78)
    for (n, w) in [(8,4),(16,4),(16,6),(16,8)]:
        mu = n.bit_length()-1
        sat = (mu-1)*n          # saturation ceiling = (mu-1)*n
        pc, nofp = carrier_primes(n, w)
        post = [q for q in pc if q > sat+1]
        smallest_carrier = pc[0] if pc else None
        onset_genuine = post[0] if post else None
        print(f"\nn={n} w={w}  (mu={mu}, saturation ceiling (mu-1)*n={sat})")
        print(f"  carrier primes (q=1 mod n, q|some N(e2)): {pc[:12]}{' ...' if len(pc)>12 else ''}")
        print(f"  smallest carrier prime              : {smallest_carrier}"
              f"{' (= q itself, SATURATED)' if smallest_carrier and smallest_carrier<=sat+1 else ''}")
        print(f"  smallest GENUINE onset prime (>sat) : {onset_genuine}"
              f"{'  norm='+str(nofp.get(onset_genuine)) if onset_genuine else ''}")
