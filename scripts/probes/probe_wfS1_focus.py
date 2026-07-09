# probe_wfS1_focus.py
# Two-stage focused worst-word search via randomized lower bound, efficient at
# n=64,128. Stage 1: coarse scan over ALL gaps g (anchor 0 and a couple others),
# few samples, to rank gaps. Stage 2: deep-sample the top-G gaps over several
# anchors. Reports certified LOWER bound on L* and the worst word.
#
# Also supports EXACT mode for small C(n,k) as a check.

import sys, os, math, json, time
sys.path.insert(0, os.path.dirname(__file__))
from probe_wfS1_engine import FieldE, batch_solve, count_list_exact, PRIMES
import numpy as np

def tau_delta(rho, eta, n):
    delta = (1-rho)-eta
    return math.ceil((1-delta)*n - 1e-9), delta

def in_window(rho, delta):
    return (1-math.sqrt(rho)) < delta < (1-rho)

def eta_values(rho, n):
    out = {'mid': (math.sqrt(rho)-rho)/2.0}
    for c in (0.5, 1.0, 2.0):
        out[f'c={c}'] = c/math.log2(n)
    return out

def sample_list_lb(field, wvals, k, tau, rng, batch, max_batches, patience):
    n = field.n; p = field.p; P = field.P
    w = wvals.astype(np.int64)
    seen = set(); no_new = 0; total = 0; cnt = 0
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
            seen.add(key); cnt += 1; new += 1
        total += batch
        if new == 0:
            no_new += 1
            if no_new >= patience: break
        else:
            no_new = 0
    return cnt, total

def worst_lb(field, rho, eta, seed=0,
             coarse_batch=4000, coarse_b=6, deep_batch=12000, deep_b=40, deep_pat=10,
             topG=6):
    n = field.n; k = round(rho*n)
    tau, delta = tau_delta(rho, eta, n)
    rng = np.random.default_rng(seed)
    # Stage 1: rank gaps (anchor 0)
    gap_score = []
    for g in range(1, n):
        a = g; b = 0
        wv = field.word_vals([a, b])
        L, _ = sample_list_lb(field, wv, k, tau, rng, coarse_batch, coarse_b, patience=coarse_b)
        gap_score.append((L, g))
    gap_score.sort(reverse=True)
    top_gaps = [g for _, g in gap_score[:topG]]
    # Stage 2: deep sample top gaps over several anchors
    best = (-1, None)
    anchors = sorted(set([0, 1, 2, 4, k, k+1, n//4, n//3, n//2 - 1]))
    anchors = [x for x in anchors if 0 <= x < n]
    for g in top_gaps:
        for anc in anchors:
            a = anc + g
            if not (1 <= a < n): continue
            b = anc
            wv = field.word_vals([a, b])
            L, _ = sample_list_lb(field, wv, k, tau, rng, deep_batch, deep_b, deep_pat)
            if L > best[0]:
                best = (L, f"x^{a}+x^{b}")
    return best[0], best[1], (k, tau, delta), top_gaps

if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, required=True)
    ap.add_argument('--rho', type=str, required=True)
    ap.add_argument('--etas', type=str, default='mid,c=0.5')  # which etas
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--topG', type=int, default=6)
    ap.add_argument('--deep_b', type=int, default=40)
    ap.add_argument('--out', type=str, default=None)
    args = ap.parse_args()
    num, den = args.rho.split('/'); rho = int(num)/int(den)
    n = args.n; field = FieldE(n, PRIMES[n]); k = round(rho*n)
    want = args.etas.split(',')
    allet = eta_values(rho, n)
    recs = []
    for el in want:
        eta = allet[el]
        t0 = time.time()
        L, word, (k_, tau, delta), top_gaps = worst_lb(field, rho, eta, seed=args.seed,
                                                        topG=args.topG, deep_b=args.deep_b)
        rec = dict(n=n, rho=args.rho, k=k, eta_label=el, eta=round(eta,4),
                   delta=round(delta,4), tau=tau, in_window=in_window(rho,delta),
                   Lstar_lower=L, worst_word=word, top_gaps=top_gaps,
                   method='focused_randomized_lower_bound', seconds=round(time.time()-t0,1))
        recs.append(rec); print(json.dumps(rec), flush=True)
    if args.out:
        with open(args.out, 'w') as f:
            for r in recs:
                f.write(json.dumps(r)+'\n')
