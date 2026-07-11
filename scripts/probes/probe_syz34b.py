#!/usr/bin/env python3
"""SYZ34 probe B: constructed band triples with prescribed overlaps.

Reuses the RS dual-shortening model.  Directly builds cores with a common
triple T, prescribed pairwise-only overlaps, and private parts, then sweeps
the whole interior band s in (2n/3, 3n/4) and multiple fields.  Confirms:
 (1) pairwise A_i cap A_j = 0  (SYZ23) when |Ci cap Cj| <= k-1;
 (2) dim((A+B) cap C) = max(0, Sum_pair - triple - 2k)  (exact law);
 (3) deficiency 0 (generation) for every post-merge band triple.
Also drives the SYZ25 coplanar mode (C subset A+B) to check it never occurs
post-merge.
"""
import random
from probe_syz34 import dual_basis_on_support, rref_dim, intersect_dim

def build_cores(n, s, tprime, pab, pac, pbc, rng):
    """Cores of size s with triple intersection tprime, pairwise-EXTRA overlaps
    pab,pac,pbc (beyond the triple), disjoint private parts.  Returns None if
    it doesn't fit in n coords."""
    coords = list(range(n)); rng.shuffle(coords)
    pos = [0]
    def take(m):
        if pos[0]+m > len(coords): raise StopIteration
        r = set(coords[pos[0]:pos[0]+m]); pos[0]+=m; return r
    try:
        T = take(tprime)
        AB = take(pab); AC = take(pac); BC = take(pbc)
        privA = take(s - tprime - pab - pac)
        privB = take(s - tprime - pab - pbc)
        privC = take(s - tprime - pac - pbc)
    except StopIteration:
        return None
    CA = T | AB | AC | privA
    CB = T | AB | BC | privB
    CC = T | AC | BC | privC
    if len(CA)!=s or len(CB)!=s or len(CC)!=s: return None
    return CA, CB, CC

def run(n, p, trials=3000, seed=1):
    rng = random.Random(seed)
    k = n//2
    pts = rng.sample(range(p), n)
    tested=0; law_fail=0; le_fail=0; defc_max=0; pw_fail=0
    band_lo = 2*n//3 + 1
    band_hi = 3*n//4
    for _ in range(trials):
        s = rng.randint(band_lo, max(band_lo, band_hi))
        # pairwise overlap = tprime + p_ij must lie in [2s-n, k-1]
        lo_ov = max(0, 2*s-n)
        hi_ov = k-1
        if lo_ov > hi_ov: continue
        tot = rng.randint(lo_ov, hi_ov)          # target pairwise overlap (equal all pairs for simplicity? vary)
        # vary per pair
        def pick_ov(): return rng.randint(lo_ov, hi_ov)
        oab, oac, obc = pick_ov(), pick_ov(), pick_ov()
        tprime = rng.randint(0, min(oab,oac,obc))
        # ensure tprime <= each pairwise and >= feasibility (2s-n triple lower bd is auto via cores)
        tprime = min(tprime, oab, oac, obc)
        pab, pac, pbc = oab-tprime, oac-tprime, obc-tprime
        if pab<0 or pac<0 or pbc<0: continue
        res = build_cores(n, s, tprime, pab, pac, pbc, rng)
        if res is None: continue
        CA,CB,CC = res
        # recompute actual overlaps
        oab=len(CA&CB); oac=len(CA&CC); obc=len(CB&CC); trip=len(CA&CB&CC)
        if max(oab,oac,obc) > k-1: continue
        tested+=1
        A=dual_basis_on_support(pts,k,CA,p)
        B=dual_basis_on_support(pts,k,CB,p)
        C=dual_basis_on_support(pts,k,CC,p)
        # pairwise zero check
        if intersect_dim(A,B,n,p)!=0 or intersect_dim(A,C,n,p)!=0 or intersect_dim(B,C,n,p)!=0:
            pw_fail+=1
        AB=A+B
        d_int=intersect_dim(AB,C,n,p)
        pair=oab+oac+obc
        formula=max(0, pair-trip-2*k)
        if d_int!=formula: law_fail+=1
        if d_int>formula: le_fail+=1
        dAB=rref_dim(AB,n,p); dABC=dAB+rref_dim(C,n,p)-d_int
        union=len(CA|CB|CC)
        defc=(union-k)-dABC
        defc_max=max(defc_max,defc)
    print(f"n={n} k={k} p={p}: tested={tested} law!=fails={law_fail} '<='fails={le_fail} pairwise-nonzero={pw_fail} max_deficiency={defc_max}")

for p in [61,101,257]:
    for n in [16,20,24,28,32]:
        run(n,p,trials=4000,seed=p*100+n)
