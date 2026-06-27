#!/usr/bin/env python3
"""Fast exact sup search for RS[F13,<4>,2] using cached masks (/tmp/f13_masks.npy).

Reductions used (both bad-count preserving):
  * s1 up to nonzero scalar (gamma reparametrized).
  * s0 modulo span(s1): translating s0 by t*s1 shifts gamma by -t.
So for each direction rep s1, iterate s0 over the (NS/P) coset reps (s0 with a
chosen coordinate-along-s1 zeroed). ~2380 dirs * ~2197 reps = 5.2M stacks.
"""
import time, numpy as np, pickle
from fractions import Fraction
from itertools import combinations
P, N, K = 13, 6, 2
masks = np.load('/tmp/f13_masks.npy')
syn, BIG = pickle.load(open('/tmp/f13_meta.pkl', 'rb'))
NS, NB = masks.shape
weights = (1 << np.arange(NB, dtype=object))
maskint = [int(sum((1 << b) for b in range(NB) if masks[i, b])) for i in range(NS)]
ADMm = {m: int(sum((1 << bit) for bit, S in enumerate(BIG) if len(S) >= m))
        for m in range(K + 1, N + 1)}
ADM_keys = sorted(ADMm)
powP = np.array([P ** j for j in range(N - K - 1, -1, -1)], dtype=np.int64)
syn_arr = np.array(syn, dtype=np.int64)
keys = (syn_arr * powP[None, :]).sum(axis=1)
idx_map = np.empty(P ** (N - K), dtype=np.int64)
idx_map[keys] = np.arange(NS)

def isrep(s):
    for x in s:
        if x % P != 0:
            return x % P == 1
    return False
reps = [i for i, s in enumerate(syn) if isrep(s)]
print(f"NS={NS} dirs={len(reps)} NB={NB}", flush=True)

best = {m: 0 for m in ADM_keys}
best_stack = {m: None for m in ADM_keys}
gammas = np.arange(P)
maskint_arr = np.array(maskint, dtype=object)

t = time.time()
for di, j in enumerate(reps):
    s1 = syn_arr[j]
    mask1 = maskint[j]
    # pivot coordinate of s1 (first nonzero)
    piv = int(np.nonzero(s1 % P)[0][0])
    # s0 coset reps: those with s0[piv]==0
    s0_idx = [i for i in range(NS) if syn_arr[i, piv] % P == 0]
    s0sub = syn_arr[s0_idx]                       # R x (n-k)
    R = len(s0sub)
    # line indices for all reps, all gamma: R x P
    lines = (s0sub[:, None, :] + gammas[None, :, None] * s1[None, None, :]) % P
    lkeys = (lines * powP[None, None, :]).sum(axis=2)
    lidx = idx_map[lkeys]                          # R x P
    for ri in range(R):
        joint = maskint[s0_idx[ri]] & mask1
        njoint = ~joint
        row = lidx[ri]
        bbits = [maskint[r] & njoint for r in row]
        for m in ADM_keys:
            am = ADMm[m]
            c = 0
            for b in bbits:
                if b & am:
                    c += 1
            if c > best[m]:
                best[m] = c
                best_stack[m] = (syn[s0_idx[ri]], syn[j])
    if di % 300 == 0:
        print(f"  dir {di}/{len(reps)} t={time.time()-t:.0f}s best={ {m:best[m] for m in ADM_keys} }", flush=True)

print(f"TOTAL {time.time()-t:.0f}s", flush=True)
print("\nFINAL profile:")
for m in sorted(best, reverse=True):
    print(f"  m={m} delta={Fraction(N-m,N)} count={best[m]} eps={Fraction(best[m],P)} "
          f"({float(Fraction(best[m],P)):.4f}) stack={best_stack[m]}")
from math import sqrt
print(f"\nJohnson=1-sqrt(1/3)={1-sqrt(1/3):.4f}  capacity=2/3={2/3:.4f}")
print("eps*=1/2 => bad iff count>=7 (7/13>1/2>6/13)")
pickle.dump((best, best_stack), open('/tmp/f13_best.pkl', 'wb'))
print("saved /tmp/f13_best.pkl")
