# probe_wfS1_sample.py
# Randomized lower bound on L(w) for a FIXED word, valid at ANY n.
#
# Each list member is the interpolant of SOME k-subset of its >=tau agreement
# points. We sample random k-subsets, interpolate, count agreements; every codeword
# found with agreement >= tau is a CERTIFIED list member (exact). Counting DISTINCT
# such codewords gives a LOWER BOUND on L(w) that converges to L* as samples grow.
#
# Crucially, a list codeword agreeing on s>=tau points is hit by a random k-subset
# with prob C(s,k)/C(n,k); since s/n ~ (1-delta) is a constant fraction, this prob
# is ~(s/n)^k, modest -> with enough samples we recover all list members of the
# worst (lacunary) word. We report the lower bound AND the # of samples, and we
# RESAMPLE until the count plateaus (no new member in `patience` consecutive
# batches) -- a heuristic stabilization, reported honestly as a lower bound.

import sys, os, math, json, time
sys.path.insert(0, os.path.dirname(__file__))
from probe_wfS1_engine import FieldE, batch_solve, PRIMES
import numpy as np

def sample_list_lb(field, wvals, k, tau, rng, batch=20000, max_batches=200,
                   patience=20):
    n = field.n; p = field.p; P = field.P
    w = wvals.astype(np.int64)
    seen = set()
    members = {}
    no_new = 0
    total = 0
    for it in range(max_batches):
        # sample `batch` random k-subsets (with replacement across batches; within a
        # batch we draw k distinct indices per row)
        idx = np.empty((batch, k), dtype=np.int64)
        for r in range(batch):
            idx[r] = rng.choice(n, size=k, replace=False)
        Vb = P[idx][:, :, :k]
        yb = w[idx]
        coeffs, ok = batch_solve(Vb, yb, p)
        M = coeffs.shape[0]
        ev = np.zeros((M, n), dtype=np.int64)
        for j in range(k):
            ev = (ev + np.outer(coeffs[:, j] % p, P[:, j]) % p) % p
        agree = (ev == w[None, :]).sum(axis=1)
        new = 0
        for bi in range(M):
            if not ok[bi]: continue
            if agree[bi] < tau: continue
            key = coeffs[bi].tobytes()
            if key in seen: continue
            seen.add(key); members[key] = int(agree[bi]); new += 1
        total += batch
        if new == 0:
            no_new += 1
            if no_new >= patience:
                break
        else:
            no_new = 0
    return len(members), total, members

def eta_values(rho, n):
    out = {'mid': (math.sqrt(rho)-rho)/2.0}
    for c in (0.5, 1.0, 2.0):
        out[f'c={c}'] = c/math.log2(n)
    return out

def tau_delta(rho, eta, n):
    delta = (1-rho)-eta
    return math.ceil((1-delta)*n - 1e-9), delta

def in_window(rho, delta):
    return (1-math.sqrt(rho)) < delta < (1-rho)

def worst_sampled(field, rho, eta, words, seed=0, batch=20000, max_batches=120, patience=15):
    n = field.n; k = round(rho*n)
    tau, delta = tau_delta(rho, eta, n)
    rng = np.random.default_rng(seed)
    best = (-1, None, 0)
    for (a,b) in words:
        wv = field.word_vals([a,b])
        L, total, members = sample_list_lb(field, wv, k, tau, rng, batch=batch,
                                            max_batches=max_batches, patience=patience)
        if L > best[0]:
            best = (L, f"x^{a}+x^{b}", total)
    return best[0], best[1], best[2], (k, tau, delta)

if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, required=True)
    ap.add_argument('--rho', type=str, required=True)
    ap.add_argument('--words', type=str, default='struct')  # 'struct' or 'all' or 'gapK'
    ap.add_argument('--batch', type=int, default=20000)
    ap.add_argument('--maxb', type=int, default=120)
    ap.add_argument('--out', type=str, default=None)
    args = ap.parse_args()
    num, den = args.rho.split('/'); rho = int(num)/int(den)
    n = args.n
    field = FieldE(n, PRIMES[n])
    k = round(rho*n)
    # candidate words: structured family extended with all gaps at a few anchors
    if args.words == 'all':
        words = [(a,b) for a in range(1,n) for b in range(0,a)]
    else:
        words = set()
        for a in range(1,n):
            words.add((a, a-1))                 # consecutive
            words.add((a, 0))                   # low anchor
        # all gaps with anchor near 0 and near n/3, plus the n=16 winner family
        for g in range(1, n):
            for anc in (0, 1, 4, n//3):
                a = anc + g
                if 1 <= a < n:
                    words.add((a, anc))
        # specifically the gap = n - 2k - 2 and symmetric gaps (empirical extremizers)
        for g in (n-2, n//2, n-6, n-2*k-2, n-k-2):
            for a in range(max(1,g), n):
                b = a-g
                if b>=0: words.add((a,b))
        words = sorted(words)
    recs = []
    for el, eta in eta_values(rho, n).items():
        L, word, total, (k_, tau, delta) = worst_sampled(field, rho, eta, words,
                                                          batch=args.batch, max_batches=args.maxb)
        rec = dict(n=n, rho=args.rho, k=k, eta_label=el, eta=round(eta,4),
                   delta=round(delta,4), tau=tau, in_window=in_window(rho,delta),
                   Lstar_lower=L, worst_word=word, samples=total,
                   method='randomized_kSubset_lower_bound')
        recs.append(rec); print(json.dumps(rec), flush=True)
    if args.out:
        with open(args.out, 'w') as f:
            for r in recs:
                f.write(json.dumps(r)+'\n')
