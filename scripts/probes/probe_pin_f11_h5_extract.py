#!/usr/bin/env python3
"""Extract an explicit bad-stack certificate for the exact pin
    mcaDeltaStar(RS[F_11, H_5, 2], 1/2) = 2/5.

At delta = 2/5, n = 5, |F| = 11, find a stack (u0, u1) with >= 6 bad scalars,
and for each bad gamma dump:
  * a witness set S (|S| >= 3 = ceil((1-delta) n)),
  * an interpolating (a, b) for the LINE u0 + gamma*u1 on S (degree < 2),
  * confirmation that u1 is NOT explainable on S (so the joint pair fails).

Mirrors the certificate shape of DeltaStarExactPinF5.lean. Discovery only.
"""
from itertools import product, combinations

p, n, k = 11, 5, 2
delta_num, delta_den = 2, 5  # delta = 2/5

# smooth domain: order-5 subgroup of F_11^*
def smooth_domain(p, n):
    for cand in range(2, p):
        g = pow(cand, (p - 1) // n, p)
        if all(pow(g, d, p) != 1 for d in range(1, n)) and pow(g, n, p) == 1:
            return [pow(g, i, p) for i in range(n)]
    raise ValueError
xs = smooth_domain(p, n)
print("dom =", xs)

# line code: a + b*x evaluated on xs
def lineEval(a, b):
    return [(a + b * x) % p for x in xs]
codewords = [lineEval(a, b) for a in range(p) for b in range(p)]

# witness threshold: |S| >= (1-delta)*n.  (1-2/5)*5 = 3.
thr = ((delta_den - delta_num) * n)  # = (1-delta)*n * den ... compute as real
# (1-delta)*n = (den-num)/den * n = (3/5)*5 = 3 exactly
min_card = 3
subsets = [S for size in range(min_card, n + 1) for S in combinations(range(n), size)]

def explainable(word, S):
    return any(all(cw[i] == word[i] for i in S) for cw in codewords)

def line_explainable_cert(u0, u1, gamma, S):
    line = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
    for a in range(p):
        for b in range(p):
            cw = lineEval(a, b)
            if all(cw[i] == line[i] for i in S):
                return (a, b)
    return None

def bad_certs(u0, u1):
    """For each gamma, return (S, (a,b)) certifying badness, or None."""
    out = {}
    for gamma in range(p):
        found = None
        for S in subsets:
            if explainable(u1, S):
                continue  # need u1 NOT explainable on S
            cert = line_explainable_cert(u0, u1, gamma, S)
            if cert is not None:
                found = (S, cert)
                break
        out[gamma] = found
    return out

# search stacks for >= 6 bad scalars
best = None
import random
random.seed(1)
def rand_word():
    return [random.randrange(p) for _ in range(n)]

# deterministic-ish search: iterate small structured u0,u1 then random
candidates = []
for u0 in product(range(p), repeat=n):
    if sum(u0) == 0:  # skip a bit; just need a hit
        pass
    candidates.append(list(u0))
    if len(candidates) > 4000:
        break

found_stack = None
for u0 in candidates:
    for _ in range(60):
        u1 = rand_word()
        certs = bad_certs(u0, u1)
        nbad = sum(1 for g in certs if certs[g] is not None)
        if nbad >= 6:
            found_stack = (u0, u1, certs, nbad)
            break
    if found_stack:
        break

if not found_stack:
    print("no stack with >=6 bad found in search")
else:
    u0, u1, certs, nbad = found_stack
    print("u0 =", u0)
    print("u1 =", u1)
    print("nbad =", nbad)
    for g in range(p):
        c = certs[g]
        if c is not None:
            S, (a, b) = c
            print(f"  gamma={g}: S={S}, codeword a={a} b={b}, "
                  f"u1_explainable_on_S={explainable(u1,S)}")
