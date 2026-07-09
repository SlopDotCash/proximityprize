# probe_wfS1_kappa.py
# Cross-parity constant kappa(n) for the CRACK D worst word (issue #444).
#
# Negation x -> -x on mu_n: -1 = omega^{n/2} (since (omega^{n/2})^2 = 1, != 1).
# So negation acts on the exponent index i by i -> (i + n/2) mod n.
#
# For a codeword g in the list of word w, its AGREEMENT SET
#   S(g) = { i : g(pts[i]) == w[i] }
# is 'symmetric' (z->-z closed) iff S(g) is closed under i -> i + n/2 (mod n).
#
# The antipodal/dyadic tower (e_{2l}(±z)=(-1)^l e_l(z^2), e_odd=0) tracks exactly
# the codewords whose agreement set is symmetric. The NON-SYMMETRIC list members
# escape the tower. We define:
#   tower_pred(w)  = # list members with SYMMETRIC agreement set
#   nonsym(w)      = # list members with NON-symmetric agreement set
#   kappa_word(w)  = nonsym(w)                          (the "escaped" count)
# and report kappa(n) at the WORST word (the one maximizing total list L*).
#
# NOTE on the prior-finding wording: prior text said kappa = (worst non-symmetric
# list) - (tower symmetric prediction). We report BOTH the symmetric and the
# non-symmetric counts of the worst word, and kappa(n) := nonsym(worst word) which
# is "how many escape the tower". We also report nonsym - sym for completeness.

import sys, os, math, json, time
sys.path.insert(0, os.path.dirname(__file__))
from probe_wfS1_engine import FieldE, count_list_exact, batch_solve, PRIMES
import numpy as np

def agreement_set(field, coeffs, wvals):
    n = field.n; p = field.p; P = field.P
    ev = np.zeros(n, dtype=np.int64)
    cc = np.array(coeffs, dtype=np.int64) % p
    for j in range(len(cc)):
        ev = (ev + (cc[j] * P[:, j]) % p) % p
    return set(int(i) for i in np.where(ev == wvals)[0])

def is_symmetric(S, n):
    h = n // 2
    return all(((i + h) % n) in S for i in S)

def exact_list_members(field, wvals, k, tau):
    """Return dict coeff_bytes -> (coeffs_tuple, agreement_set) for all exact list members."""
    from itertools import combinations
    n = field.n; p = field.p; P = field.P
    w = wvals.astype(np.int64)
    seen = set(); out = {}
    buf = []; batch = 40000
    def flush(buf):
        if not buf: return
        idx = np.array(buf, dtype=np.int64)
        Vb = P[idx][:, :, :k]; yb = w[idx]
        coeffs, ok = batch_solve(Vb, yb, p)
        M = coeffs.shape[0]
        ev = np.zeros((M, n), dtype=np.int64)
        for j in range(k):
            ev = (ev + np.outer(coeffs[:, j] % p, P[:, j]) % p) % p
        agree = (ev == w[None, :]).sum(axis=1)
        for bi in range(M):
            if not ok[bi]: continue
            if agree[bi] < tau: continue
            key = coeffs[bi].tobytes()
            if key in seen: continue
            seen.add(key)
            S = set(int(i) for i in np.where(ev[bi] == w)[0])
            out[key] = (tuple(int(x) for x in coeffs[bi]), S)
    for sub in combinations(range(n), k):
        buf.append(sub)
        if len(buf) >= batch:
            flush(buf); buf = []
    flush(buf)
    return out

def kappa_for_word(field, exps, k, tau):
    wv = field.word_vals(exps)
    members = exact_list_members(field, wv, k, tau)
    n = field.n
    sym = 0; nonsym = 0
    for key, (coeffs, S) in members.items():
        if is_symmetric(S, n):
            sym += 1
        else:
            nonsym += 1
    return dict(total=len(members), sym=sym, nonsym=nonsym, kappa=nonsym,
                kappa_diff=nonsym - sym)

def find_worst_and_kappa(field, rho, eta, words):
    n = field.n; k = round(rho*n)
    delta = (1-rho)-eta
    tau = math.ceil((1-delta)*n - 1e-9)
    best = None
    for (a,b) in words:
        wv = field.word_vals([a,b])
        L, _ = count_list_exact(field, wv, k, tau)
        if best is None or L > best[0]:
            best = (L, (a,b))
    a,b = best[1]
    kk = kappa_for_word(field, [a,b], k, tau)
    kk.update(dict(n=n, rho_k=k, tau=tau, delta=round(delta,4),
                   worst_word=f"x^{a}+x^{b}", Lstar=best[0]))
    return kk
