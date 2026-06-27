#!/usr/bin/env python3
"""Exact-ish mcaDeltaStar for RS[F_17, <2> order 8, deg<2] (n=8, k=2, rate 1/4).

Full syndrome sup is 17^12; infeasible. We search a STRUCTURED candidate set of
worst stacks (the families that maximize bad-scalar count in the F5/F11 pins):
 - "triangle"/boundary stacks: u0 a near-codeword (codeword + 1 sparse error),
   u1 a sparse word so each scalar gamma corrects a different small subset.
 - monomial stacks: u0, u1 evaluations of monomials X^a, X^b reduced mod the code.
For each candidate we count bad scalars at every witness threshold m and report
the max. This REFUTES upper bounds on delta*; combined with the forced-predicate
good-side bound it brackets delta*.

mcaEvent(C, delta, u0, u1, gamma): exists S, |S| >= (1-delta)*n, line=u0+gamma*u1
explainable on S, and NOT (u0 expl on S AND u1 expl on S).
"""
from itertools import product, combinations
from math import sqrt
from fractions import Fraction
import random

P, N, K = 17, 8, 2
XS = [pow(2, i, P) for i in range(N)]  # subgroup <2> order 8

def lineEval(a, b):
    return [(a + b * x) % P for x in XS]

CODEWORDS = [lineEval(a, b) for a in range(P) for b in range(P)]

# Precompute subsets of size > k
SUBSETS = []
for size in range(K+1, N+1):
    SUBSETS.extend(combinations(range(N), size))
SUB_LEN = {i: len(S) for i, S in enumerate(SUBSETS)}

_EXT_CACHE = {}
def ext_mask(word):
    """bitmask over SUBSETS: bit set iff word explainable on that subset."""
    key = tuple(w % P for w in word)
    c = _EXT_CACHE.get(key)
    if c is not None:
        return c
    mask = 0
    wm = list(key)
    for bit, S in enumerate(SUBSETS):
        # explainable iff some codeword agrees on S
        for cw in CODEWORDS:
            ok = True
            for i in S:
                if cw[i] != wm[i]:
                    ok = False; break
            if ok:
                mask |= 1 << bit; break
    _EXT_CACHE[key] = mask
    return mask

def adm_mask(m):
    mask = 0
    for bit, S in enumerate(SUBSETS):
        if len(S) >= m:
            mask |= 1 << bit
    return mask

ADM = {m: adm_mask(m) for m in range(K+1, N+1)}

def eval_stack(u0, u1):
    """return dict m -> bad count, and per-gamma badness info."""
    e0 = ext_mask(u0); e1 = ext_mask(u1)
    both = e0 & e1
    per_g = []
    for g in range(P):
        line = [(u0[i] + g*u1[i]) % P for i in range(N)]
        el = ext_mask(line)
        bad_bits = el & ~both  # explainable on S but pair fails
        per_g.append(bad_bits)
    res = {}
    for m, am in ADM.items():
        cnt = sum(1 for bb in per_g if bb & am)
        res[m] = cnt
    return res, per_g, e0, e1

def witness_for(word, S):
    for a in range(P):
        for b in range(P):
            cw = lineEval(a, b)
            if all(cw[i] == word[i] % P for i in S):
                return (a, b)
    return None

# ---- candidate families ----
best = {m: 0 for m in ADM}
best_stack = {m: None for m in ADM}

def consider(u0, u1):
    res, per_g, e0, e1 = eval_stack(u0, u1)
    for m in ADM:
        if res[m] > best[m]:
            best[m] = res[m]; best_stack[m] = (list(u0), list(u1))

# Family 1: u0 = sparse "spike" words (codeword 0 + spikes), u1 = sparse words
# Try u0 with small support not a codeword, u1 with small support.
random.seed(1)
spikes = []
# all words with support size <=3 and values in {0,1}? too many; use canonical
for supp in combinations(range(N), 1):
    w = [0]*N
    for i in supp: w[i] = 1
    spikes.append(w)
for supp in combinations(range(N), 2):
    for vals in product([1], repeat=2):
        w = [0]*N
        for i,v in zip(supp, vals): w[i] = v
        spikes.append(w)
for supp in combinations(range(N), 3):
    w = [0]*N
    for i in supp: w[i] = 1
    spikes.append(w)

# Family 2: monomial-ish: u0=X^a eval, u1=X^b eval reduced. Use raw monomials.
monomials = []
for a in range(N):
    monomials.append([pow(x, a, P) for x in XS])

cands_u0 = spikes + monomials
cands_u1 = spikes + monomials

print(f"scanning {len(cands_u0)}x{len(cands_u1)} structured stacks...")
cnt = 0
for u0 in cands_u0:
    for u1 in cands_u1:
        consider(u0, u1)
        cnt += 1
print(f"  scanned {cnt}")

# Family 3: randomized search to push the worst case
for _ in range(8000):
    u0 = [random.randrange(P) for _ in range(N)]
    u1 = [random.randrange(P) for _ in range(N)]
    consider(u0, u1)

rho = Fraction(K, N)
johnson = 1 - sqrt(float(rho))
print(f"\nRS[F_{P}, n={N}, k={K}]  rate={float(rho)}  UDR={(1-float(rho))/2:.4f}  "
      f"Johnson={johnson:.4f}  capacity={1-float(rho):.4f}")
print(f"  {'m':>3} {'delta=1-m/n':>14} {'maxbad':>7} {'eps_mca':>16}  good?(<=8)")
for m in sorted(best, reverse=True):
    delta = Fraction(N - m, N)
    b = best[m]
    good = "GOOD" if b <= 8 else "BAD"
    print(f"  {m:>3} {str(delta):>14} {b:>7}   {b}/17={float(b)/17:.4f}   {good}")

# eps_mca <= 1/2 iff bad <= 8. delta* = sup delta with bad<=8.
# the witness threshold m at radius delta is smallest m with m >= (1-delta)*n.
# For the bracket: good side needs forced witness size. Let's find the jump.
print("\n--- delta* analysis (eps* = 1/2) ---")
# Bands: at radius delta in (1-(m)/n, 1-(m-1)/n], threshold = m... careful.
# In Lean: card_cond requires |S| >= (1-delta)*n. At delta=1-m/n exactly, (1-delta)*n=m.
# So a witness set of size m is admissible at delta = 1 - m/n.
prev_good_delta = None
for m in sorted(best, reverse=True):
    delta = Fraction(N - m, N)
    if best[m] <= 8:
        prev_good_delta = delta
print(f"largest delta=1-m/n that is GOOD (maxbad<=8): {prev_good_delta} = {float(prev_good_delta) if prev_good_delta else None}")

# Find smallest m that is BAD; delta there is bad.
for m in sorted(best, reverse=True):
    delta = Fraction(N - m, N)
    if best[m] >= 9:
        print(f"first BAD: m={m}, delta={delta}={float(delta):.4f}, maxbad={best[m]}")
        print(f"  bad stack u0={best_stack[m][0]}")
        print(f"            u1={best_stack[m][1]}")
        break

# emit explicit witnesses for the chosen bad delta
def emit_witnesses(u0, u1, m):
    e0 = ext_mask(u0); e1 = ext_mask(u1); both = e0 & e1
    print(f"\n  explicit bad scalars at m={m} (delta={Fraction(N-m,N)}):")
    bad_gammas = []
    for g in range(P):
        line = [(u0[i] + g*u1[i]) % P for i in range(N)]
        el = ext_mask(line)
        bad = el & ~both
        # find an admissible witness subset
        found = None
        for bit, S in enumerate(SUBSETS):
            if (bad >> bit) & 1 and len(S) >= m:
                found = S; break
        if found is not None:
            bad_gammas.append(g)
            w = witness_for(line, found)
            print(f"    gamma={g}: S={found}, line codeword a+bX = {w}, "
                  f"u1_expl_on_S={witness_for(u1, found) is not None}")
    print(f"  total bad scalars = {len(bad_gammas)}: {bad_gammas}")
    return bad_gammas

for m in sorted(best, reverse=True):
    if best[m] >= 9:
        emit_witnesses(best_stack[m][0], best_stack[m][1], m)
        break

print(f"\nJohnson radius = {johnson:.6f}")
