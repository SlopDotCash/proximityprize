#!/usr/bin/env python3
"""
G98 addendum: sign/cancellation structure of the large-values Gram matrix, alignment
of extremal character vectors, difference-closure of the level set, and HM at the
target-level set (the set GM would actually use).
"""
import numpy as np
from math import log, sqrt
from probe_g98_gram_bootstrap import is_prime, primitive_root, Dlog

def run(n, beta=4.0):
    p = int(round(n**beta)); p += (1 - p) % n
    while not is_prime(p): p += n
    m = (p-1)//n
    g = primitive_root(p)
    gm = pow(g, m, p)
    mu = np.empty(n, dtype=np.int64); cur = 1
    for i in range(n): mu[i] = cur; cur = cur * gm % p
    ind = np.zeros(p); ind[mu] = 1.0
    eta = np.fft.fft(ind).real
    abseta = np.abs(eta)
    M = abseta[1:].max(); target = sqrt(n*log(p/n))
    dlog = Dlog(g, p)
    reps = np.empty(m, dtype=np.int64); cur = 1
    for i in range(m): reps[i] = cur; cur = cur * g % p
    ceta = abseta[reps]
    order = np.argsort(-ceta)
    print(f"\n===== n={n} p={p} m={m}: M={M:.3f} target={target:.3f} =====")
    # B = full TARGET level set (one rep per coset >= target)
    for lvl, name in ((target, "target"), (0.7*M, "0.7M")):
        sel = order[ceta[order] >= lvl]
        r = len(sel)
        if r < 2:
            print(f"  level {name}: r={r} too small"); continue
        B = reps[sel]; V = ceta[sel].min()
        D = (B[:,None] - B[None,:]) % p
        G = eta[D]
        off = G[~np.eye(r,dtype=bool)]
        pos_frac = (off > 0).mean()
        mean_signed = off.mean(); mean_abs = np.abs(off).mean()
        cancel = abs(mean_signed)/mean_abs
        ev, U = np.linalg.eigh(G)
        lam = ev[-1]; u1 = U[:,-1]
        ones = np.ones(r)/sqrt(r)
        align = abs(u1 @ ones)
        sumsq = float((eta[B]**2).sum())
        # difference-closure: fraction of B-B cosets that lie in the SAME level set
        dcos = set()
        for y in D[~np.eye(r,dtype=bool)].ravel():
            dcos.add(dlog(int(y)) % m)
        lvlset = set(int(i) for i in sel)  # coset indices (dlog of rep = index i since rep=g^i)
        # coset index of rep g^i is i; dlog(y)%m gives coset index
        inlvl = sum(1 for c in dcos if c in lvlset)
        # HM at this level set
        Mp = np.abs(off).max()
        info = V*V/(n*Mp)
        print(f"  level {name} (V>={V:.2f}): r={r}")
        print(f"    Gram off-diag: pos-frac={pos_frac:.3f}  mean(signed)={mean_signed:8.3f}  mean|.|={mean_abs:8.3f}"
              f"  cancellation |mean|/mean|.|={cancel:.3f}")
        print(f"    lam_max={lam:.2f} (r*n={r*n})  top-evec alignment |<u1,1>|={align:.4f}"
              f"   n*lam_max/sum|eta|^2 = {n*lam/sumsq:.3f}")
        print(f"    B-B cosets: {len(dcos)}  of which IN level set: {inlvl} ({inlvl/len(dcos):.2%})")
        print(f"    HM info ratio V^2/(n max|off|) = {info:.4f}  -> {'INFORMATIVE' if info>1 else 'VACUOUS'}")
        # GM-style: singular values of the RECTANGULAR extremal matrix A[x,b]=e(bx) is G's sqrt;
        # effective rank (participation) of G:
        er = (ev.sum())**2 / (ev**2).sum()
        print(f"    Gram effective rank = {er:.2f} / {r}   (trace={ev.sum():.1f}=rn, lam_max share={lam/ev.sum():.2%})")

if __name__ == "__main__":
    for n in (8, 16, 32, 64):
        run(n)
