# probe_wfS1_kappa_sample.py
# Sampler-based kappa (cross-parity) for large n where exact list is infeasible.
# Enumerates list members of a FIXED word via randomized k-subsets, classifies each
# found member by agreement-set symmetry (closed under i->i+n/2 mod n). Reports
# sym / nonsym counts -> kappa. The counts are LOWER bounds (sampling may miss
# members) but for the small lists here sampling saturates.

import sys, os, math, json, time
sys.path.insert(0, os.path.dirname(__file__))
from probe_wfS1_engine import FieldE, batch_solve, PRIMES
import numpy as np

def is_symmetric(S, n):
    h = n // 2
    return all(((i + h) % n) in S for i in S)

def kappa_sample(field, exps, k, tau, rng, batch=15000, max_batches=120, patience=20):
    n = field.n; p = field.p; P = field.P
    w = field.word_vals(exps).astype(np.int64)
    seen = set(); sym = 0; nonsym = 0; no_new = 0; total = 0
    for it in range(max_batches):
        idx = np.empty((batch, k), dtype=np.int64)
        for r in range(batch):
            idx[r] = rng.choice(n, size=k, replace=False)
        Vb = P[idx][:, :, :k]; yb = w[idx]
        coeffs, ok = batch_solve(Vb, yb, p)
        M = coeffs.shape[0]
        ev = np.zeros((M, n), dtype=np.int64)
        for j in range(k):
            ev = (ev + np.outer(coeffs[:, j] % p, P[:, j]) % p) % p
        agree = (ev == w[None, :]).sum(axis=1)
        new = 0
        sel = np.where((agree >= tau) & ok)[0]
        for bi in sel:
            key = coeffs[bi].tobytes()
            if key in seen: continue
            seen.add(key); new += 1
            S = set(int(i) for i in np.where(ev[bi] == w)[0])
            if is_symmetric(S, n): sym += 1
            else: nonsym += 1
        total += batch
        if new == 0:
            no_new += 1
            if no_new >= patience: break
        else:
            no_new = 0
    return dict(total=sym+nonsym, sym=sym, nonsym=nonsym, kappa=nonsym,
                kappa_diff=nonsym - sym, samples=total)

if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, required=True)
    ap.add_argument('--rho', type=str, required=True)
    ap.add_argument('--word', type=str, required=True)   # 'consec' or 'a,b'
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--maxb', type=int, default=120)
    args = ap.parse_args()
    num, den = args.rho.split('/'); rho = int(num)/int(den)
    n = args.n; field = FieldE(n, PRIMES[n]); k = round(rho*n)
    eta = (math.sqrt(rho)-rho)/2; delta = (1-rho)-eta
    tau = math.ceil((1-delta)*n - 1e-9)
    rng = np.random.default_rng(args.seed)
    if args.word == 'consec':
        # consecutive word x^a + x^{a-1}; pick a in the middle (a = n//2 + 1)
        a = n//2 + 1; b = a - 1; exps = [a, b]; wlabel = f"x^{a}+x^{b}"
    else:
        a, b = [int(x) for x in args.word.split(',')]; exps = [a, b]; wlabel = f"x^{a}+x^{b}"
    res = kappa_sample(field, exps, k, tau, rng, max_batches=args.maxb)
    res.update(dict(n=n, rho=args.rho, k=k, tau=tau, delta=round(delta,4), word=wlabel))
    print(json.dumps(res), flush=True)
