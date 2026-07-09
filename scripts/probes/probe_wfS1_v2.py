# probe_wfS1_v2.py -- efficient full 2-term exact scan, all etas at once.
#
# KEY OPTIMIZATION: for a fixed word, the SET of candidate codewords (interpolants
# of all k-subsets) and their agreement counts do NOT depend on tau. So we compute
# the multiset of agreement counts ONCE per word, then for every (eta->tau) just
# count how many distinct codewords have agreement >= tau. One interpolation pass
# serves all etas.
#
# We return, per word, the sorted list of agreement counts of all DISTINCT codewords
# (deg<k) that arise as interpolants of some k-subset AND agree on >= k+1 points
# (we keep everything >= some floor to size the list). Actually we keep ALL distinct
# interpolants' agreement counts (>= k by construction) -- but to bound memory we
# only retain agreement >= k+1 (codewords agreeing on exactly k pts are the trivial
# ones and never reach tau>k; if tau==k they all count but that's the degenerate
# edge, handled separately).

import sys, os, math, json, time
sys.path.insert(0, os.path.dirname(__file__))
from probe_wfS1_engine import FieldE, batch_solve, PRIMES
from itertools import combinations
from math import comb
import numpy as np

def agreement_profile(field, wvals, k, keep_floor=None, batch=40000):
    """Return dict: agreement_count -> number of DISTINCT codewords (deg<k) that
    interpolate some k-subset of points-of-w and agree with w on exactly that many
    points. Only codewords with agreement >= keep_floor retained (default k+1)."""
    n = field.n; p = field.p; P = field.P
    w = wvals.astype(np.int64)
    if keep_floor is None:
        keep_floor = k + 1
    seen = set()
    prof = {}
    buf = []
    def flush(buf):
        if not buf: return
        idx = np.array(buf, dtype=np.int64)
        Vb = P[idx][:, :, :k]
        yb = w[idx]
        coeffs, ok = batch_solve(Vb, yb, p)
        # evaluate
        M = coeffs.shape[0]
        ev = np.zeros((M, n), dtype=np.int64)
        for j in range(k):
            ev = (ev + np.outer(coeffs[:, j] % p, P[:, j]) % p) % p
        agree = (ev == w[None, :]).sum(axis=1)
        for bi in range(M):
            if not ok[bi]: continue
            if agree[bi] < keep_floor: continue
            ct = coeffs[bi].tobytes()
            if ct in seen: continue
            seen.add(ct)
            a = int(agree[bi]); prof[a] = prof.get(a, 0) + 1
    for sub in combinations(range(n), k):
        buf.append(sub)
        if len(buf) >= batch:
            flush(buf); buf = []
    flush(buf)
    return prof

def list_size_at_tau(prof, tau):
    return sum(c for a, c in prof.items() if a >= tau)

def eta_values(rho, n):
    out = {'mid': (math.sqrt(rho)-rho)/2.0}
    for c in (0.5, 1.0, 2.0):
        out[f'c={c}'] = c/math.log2(n)
    return out

def tau_of(rho, eta, n):
    delta = (1-rho)-eta
    return math.ceil((1-delta)*n - 1e-9), delta

def in_window(rho, delta):
    return (1-math.sqrt(rho)) < delta < (1-rho)

def run(ns, rhos, per_word_cap, out_path=None, family='full'):
    recs = []
    for n in ns:
        field = FieldE(n, PRIMES[n])
        for rho, rlabel in rhos:
            k = round(rho*n)
            cnk = comb(n, k)
            etas = eta_values(rho, n)
            # distinct taus
            taus = {}
            for el, eta in etas.items():
                tau, delta = tau_of(rho, eta, n)
                taus.setdefault(tau, []).append((el, eta, delta))
            if cnk > per_word_cap:
                for el, eta in etas.items():
                    tau, delta = tau_of(rho, eta, n)
                    rec = dict(n=n, rho=rlabel, k=k, eta_label=el, eta=round(eta,4),
                        delta=round(delta,4), tau=tau, in_window=in_window(rho,delta),
                        Lstar=None, worst_word=None, exact=False, mode='INFEASIBLE', Cnk=cnk)
                    recs.append(rec); print(json.dumps(rec), flush=True)
                continue
            # build word list
            if family == 'full':
                words = [(a,b) for a in range(1,n) for b in range(0,a)]
            else:
                words = [(a,b) for a in range(1,n) for b in range(0,a) if (a-b)==family]
            # per tau, track best
            best = {tau: (-1, None) for tau in taus}
            t0 = time.time()
            for (a,b) in words:
                wv = field.word_vals([a,b])
                prof = agreement_profile(field, wv, k)
                for tau in taus:
                    L = list_size_at_tau(prof, tau)
                    if L > best[tau][0]:
                        best[tau] = (L, f"x^{a}+x^{b}")
            dt = time.time()-t0
            for tau, members in taus.items():
                L, word = best[tau]
                for (el, eta, delta) in members:
                    rec = dict(n=n, rho=rlabel, k=k, eta_label=el, eta=round(eta,4),
                        delta=round(delta,4), tau=tau, in_window=in_window(rho,delta),
                        Lstar=L, worst_word=word, exact=True, mode='full2term', Cnk=cnk,
                        scan_seconds=round(dt,1))
                    recs.append(rec); print(json.dumps(rec), flush=True)
    if out_path:
        with open(out_path, 'w') as f:
            for r in recs:
                f.write(json.dumps(r)+'\n')
    return recs

if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--ns', type=str, required=True)
    ap.add_argument('--rhos', type=str, required=True)
    ap.add_argument('--per_word_cap', type=int, default=120000)
    ap.add_argument('--out', type=str, default=None)
    args = ap.parse_args()
    ns = [int(x) for x in args.ns.split(',')]
    rhos = []
    for r in args.rhos.split(','):
        a,b = r.split('/'); rhos.append((int(a)/int(b), r))
    run(ns, rhos, args.per_word_cap, args.out)
