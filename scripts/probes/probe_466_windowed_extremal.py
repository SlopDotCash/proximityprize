#!/usr/bin/env python3
"""probe_466_windowed_extremal.py -- LANE P5: windowed SumsetExtremal at small n (#466).

QUESTION (dossier v3 sec 6 Tier-1 item 1): in the PRIZE WINDOW
delta in (1-sqrt(rho), 1-rho), q >= n^4, does some >=2-Fourier-component
(spread) direction u1 beat every monomial direction in worst-case bad-scalar
count, or do monomials dominate?  (Guard-free version is FALSE below window.)

MAIN SETTING: n=8, k=2 (rho=1/4) => window delta in (0.5, 0.75)
  => agreement a = (1-delta)*8 in (2,4): a=3 is the strict interior level,
     a=4 is the Johnson boundary delta = 1-sqrt(rho) = 0.5 (reported, flagged).
  q1 = least prime == 1 mod 8 with q >= n^4 = 4096; q2 = least such >= 2*q1.
COARSE REPEAT: n=16, k=4, q=65537 (>= 16^4), window same, a in {5,6,7} interior.

BAD-SCALAR COUNT for a stack (u0,u1) at agreement a:
  #{gamma in F_q : exists codeword c in RS_k agreeing with u0+gamma*u1
    on >= a positions of mu_n}.
EXACT computation (interpolation trick): any deg<k codeword agreeing on
>= a >= k positions is the Lagrange interpolant of one of the C(n,k)
k-subsets.  For subset p, agreement at position l is the linear-in-gamma
condition A_l + gamma*B_l = 0 with A_l = u0_l - P0_p(x_l) (P0_p = interpolant
of u0 on p), B_l = u1_l - P1_p(x_l).  So per (u0,u1,p): positions with
A=B=0 agree for ALL gamma (count 'base', always >= k), positions with B!=0
agree exactly at gamma_l = -A_l/B_l.  gamma is bad via p iff
base_p + mult_p(gamma) >= a.  Bad set = union over p; count = q iff some
base_p >= a iff u1 is a-close to the code (degenerate direction; proven both
ways below and ASSERTED at runtime).

WORST-u0 SEARCH (heuristic, stated honestly in output): monomials, far-coset
family w_g = x^{3n/4} + g x^{n/2}, piecewise-codeword words, >=2000 random
words, per-u1 CHAINED interpolation-adversarial words (blocks u0 = c_t - g_t*u1
glued on k-point overlaps -- the sumset mechanism), plus hill-climb refinement
on the decision-critical directions.  Exact per candidate; max is a lower
bound on the true worst case.

Independent verification: brute force over ALL gamma in F_q (separate code
path) asserted equal on random pairs and on every decision-critical witness.
"""
import argparse
import itertools
import sys
import time

import numpy as np


# ----------------------------------------------------------------------
# primes / field utilities
# ----------------------------------------------------------------------
def is_prime(m: int) -> bool:
    if m < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if m % p == 0:
            return m == p
    d, r = m - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in small:
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(r - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def least_prime_1mod(n: int, lo: int) -> int:
    m = lo + ((1 - lo) % n)
    while not is_prime(m):
        m += n
    return m


def mu_generator(q: int, n: int) -> int:
    # n is a power of 2 here, so order-n check is x^(n/2) != 1.
    for g in range(2, q):
        x = pow(g, (q - 1) // n, q)
        if pow(x, n // 2, q) != 1:
            return x
    raise RuntimeError("no order-n element")


def inv_table(q: int) -> np.ndarray:
    inv = np.zeros(q, dtype=np.int64)
    inv[1] = 1
    for i in range(2, q):
        inv[i] = (q - (q // i) * inv[q % i]) % q
    return inv


# ----------------------------------------------------------------------
# small polynomial helpers (coeffs low->high, mod q)
# ----------------------------------------------------------------------
def poly_mul_lin(c, r, q):
    out = [0] * (len(c) + 1)
    for i, ci in enumerate(c):
        out[i + 1] = (out[i + 1] + ci) % q
        out[i] = (out[i] - ci * r) % q
    return out


def interp_poly(xp, yp, q):
    m = len(xp)
    coeffs = [0] * m
    for t in range(m):
        num = [1]
        den = 1
        for s in range(m):
            if s == t:
                continue
            num = poly_mul_lin(num, xp[s], q)
            den = den * (xp[t] - xp[s]) % q
        w = yp[t] * pow(int(den % q), q - 2, q) % q
        for i in range(len(num)):
            coeffs[i] = (coeffs[i] + w * num[i]) % q
    return coeffs


def poly_eval_vec(coeffs, xs, q):
    r = np.zeros(len(xs), dtype=np.int64)
    for c in reversed(coeffs):
        r = (r * xs + c) % q
    return r


# ----------------------------------------------------------------------
# the exact bad-scalar-count engine
# ----------------------------------------------------------------------
class Setting:
    def __init__(self, n, k, q):
        self.n, self.k, self.q = n, k, q
        self.om = mu_generator(q, n)
        xs = np.array([pow(self.om, l, q) for l in range(n)], dtype=np.int64)
        assert len(set(xs.tolist())) == n, "mu_n not of full order"
        self.xs = xs
        subsets = list(itertools.combinations(range(n), k))
        self.P = len(subsets)
        self.Tidx = np.array(subsets, dtype=np.int64)
        C = np.zeros((self.P, k, n), dtype=np.int64)
        for pi_, T in enumerate(subsets):
            for ti, t in enumerate(T):
                den = 1
                for s in T:
                    if s != t:
                        den = den * int(xs[t] - xs[s]) % q
                dinv = pow(den % q, q - 2, q)
                for l in range(n):
                    num = 1
                    for s in T:
                        if s != t:
                            num = num * int(xs[l] - xs[s]) % q
                    C[pi_, ti, l] = num * dinv % q
        self.C = C
        self.inv = inv_table(q)

    def mono(self, j):
        return np.array([pow(int(x), j, self.q) for x in self.xs], dtype=np.int64)

    def pack(self, u1):
        q = self.q
        u1 = np.asarray(u1, dtype=np.int64) % q
        u1T = u1[self.Tidx]
        B = (u1[None, :] - np.einsum('ptl,pt->pl', self.C, u1T)) % q
        agreemax = int((B == 0).sum(axis=1).max())
        return dict(u1=u1, B=B, valid=(B != 0), Binv=self.inv[B], agreemax=agreemax)

    def badcounts(self, U, pack, a_list, chunk=512):
        """Exact bad-scalar counts for each row u0 of U, at each level in a_list."""
        q, n, P = self.q, self.n, self.P
        U = np.asarray(U, dtype=np.int64) % q
        out = {a: np.zeros(len(U), dtype=np.int64) for a in a_list}
        Bz = (pack['B'] == 0)[None]
        for s in range(0, len(U), chunk):
            Uc = U[s:s + chunk]
            N = len(Uc)
            UT = Uc[:, self.Tidx]
            Pv = np.einsum('ptl,npt->npl', self.C, UT) % q
            A = (Uc[:, None, :] - Pv) % q
            base = ((A == 0) & Bz).sum(axis=2)                       # (N,P), >= k
            prod = ((q - A) % q) * pack['Binv'][None] % q
            gamma = np.where(pack['valid'][None], prod, q)           # sentinel q
            gs = np.sort(gamma, axis=2)
            for a in a_list:
                t = a - base
                full = (t <= 0).any(axis=1)
                qual = np.zeros(gs.shape, dtype=bool)
                tpos = t[t > 0]
                tmax = int(tpos.max()) if tpos.size else 0
                for tv in range(1, min(tmax, n) + 1):
                    rows = (t == tv)
                    if not rows.any():
                        continue
                    if tv == 1:
                        mark = gs < q
                    else:
                        mark = np.zeros(gs.shape, dtype=bool)
                        mark[:, :, :n - (tv - 1)] = (
                            (gs[:, :, tv - 1:] == gs[:, :, :n - (tv - 1)])
                            & (gs[:, :, :n - (tv - 1)] < q))
                    qual |= rows[:, :, None] & mark
                badv = np.where(qual, gs, q).reshape(N, P * n)
                badv.sort(axis=1)
                d = (badv[:, 0] < q).astype(np.int64)
                d += ((badv[:, 1:] != badv[:, :-1]) & (badv[:, 1:] < q)).sum(axis=1)
                d[full] = q
                out[a][s:s + N] = d
        return out

    def brute_count(self, u0, u1, a, gchunk=4096):
        """Independent checker: enumerate ALL gamma in F_q."""
        q = self.q
        u0 = np.asarray(u0, dtype=np.int64) % q
        u1 = np.asarray(u1, dtype=np.int64) % q
        tot = 0
        for s in range(0, q, gchunk):
            G = np.arange(s, min(s + gchunk, q), dtype=np.int64)
            W = (u0[None, :] + G[:, None] * u1[None, :]) % q
            WT = W[:, self.Tidx]
            V = np.einsum('ptl,gpt->gpl', self.C, WT) % q
            agree = (V == W[:, None, :]).sum(axis=2)
            tot += int((agree >= a).any(axis=1).sum())
        return tot


# ----------------------------------------------------------------------
# u0 candidate builders
# ----------------------------------------------------------------------
def chained_u0(st, u1, a, rng):
    """Interpolation-adversarial: blocks u0 = c_t(x) - g_t*u1 glued on k-point
    overlaps with the PREVIOUS block (c_{t+1} = c_t + (g_{t+1}-g_t)*interp(u1|O)).
    Yields 1 + floor((n-a)/(a-k)) bad gammas by construction (the sumset mechanism)."""
    n, k, q, xs = st.n, st.k, st.q, st.xs
    perm = rng.permutation(n)
    S1 = [int(x) for x in perm[:a]]
    rest = [int(x) for x in perm[a:]]
    g = int(rng.integers(1, q))
    c = [int(rng.integers(q)) for _ in range(k)]
    u0 = np.full(n, -1, dtype=np.int64)
    cv = poly_eval_vec(c, xs, q)
    u0[S1] = (cv[S1] - g * u1[S1]) % q
    prev = list(S1)
    i = 0
    while a > k and i + (a - k) <= len(rest):
        O = [int(x) for x in rng.choice(np.array(prev), size=k, replace=False)]
        h = interp_poly([int(xs[o]) for o in O], [int(u1[o]) for o in O], q)
        gn = int(rng.integers(1, q))
        while gn == g:
            gn = int(rng.integers(1, q))
        c = [(c[j] + (gn - g) * h[j]) % q for j in range(k)]
        g = gn
        Nt = rest[i:i + (a - k)]
        cv = poly_eval_vec(c, xs, q)
        u0[Nt] = (cv[Nt] - g * u1[Nt]) % q
        prev = O + Nt
        i += (a - k)
    m = (u0 < 0)
    if m.any():
        u0[m] = rng.integers(0, q, size=int(m.sum()))
    return u0 % q


def shared_u0_pool(st, rng, n_far, n_piece, n_rand):
    n, k, q, xs = st.n, st.k, st.q, st.xs
    pool = [np.zeros(n, dtype=np.int64)]
    for j in range(n):
        pool.append(st.mono(j))
    # far-coset family w_g = x^{3n/4} + g x^{n/2}
    m34, m2 = st.mono(3 * n // 4), st.mono(n // 2)
    gvals = [1, 2, 3, q - 1] + [int(rng.integers(2, q)) for _ in range(max(0, n_far - 4))]
    for g in gvals[:n_far]:
        pool.append((m34 + g * m2) % q)
    # piecewise-codeword words
    for _ in range(n_piece):
        perm = rng.permutation(n)
        nb = int(rng.integers(2, 5))
        cuts = sorted(rng.choice(np.arange(1, n), size=nb - 1, replace=False).tolist())
        blocks = np.split(perm, cuts)
        u0 = np.zeros(n, dtype=np.int64)
        for b in blocks:
            c = [int(rng.integers(q)) for _ in range(k)]
            u0[b] = poly_eval_vec(c, xs, q)[b]
        pool.append(u0)
    for _ in range(n_rand):
        pool.append(rng.integers(0, q, size=n).astype(np.int64))
    return np.array(pool)


# ----------------------------------------------------------------------
# direction builders
# ----------------------------------------------------------------------
def build_directions(st, rng, sparse_pairs, cvals, n_rand):
    n, q = st.n, st.q
    dirs = []
    for j in range(n):
        dirs.append((f"mono_j{j}", "monomial", st.mono(j)))
    for (i, j) in sparse_pairs:
        mi, mj = st.mono(i), st.mono(j)
        for c in cvals:
            dirs.append((f"sp2_{i}_{j}_c{c}", "spread2", (mi + c * mj) % q))
    for aexp in range(n):
        dirs.append((f"twist_{aexp}", "twisted", st.mono(aexp) * (st.xs + 1) % q))
    for r in range(n_rand):
        dirs.append((f"rand{r}", "randdense", rng.integers(0, q, size=n).astype(np.int64)))
    return dirs


# ----------------------------------------------------------------------
# refinement (hill climb + fresh chains) on decision-critical directions
# ----------------------------------------------------------------------
def refine_dir(st, pack, a, seed_u0, seed_count, rng, rounds=6, batch=192, nchain=64):
    best_u, best_c = seed_u0.copy(), int(seed_count)
    stall = 0
    for _ in range(rounds):
        cands = [best_u]
        for _ in range(batch):
            m = best_u.copy()
            for _ in range(int(rng.integers(1, 3))):
                m[int(rng.integers(st.n))] = int(rng.integers(st.q))
            cands.append(m)
        for _ in range(nchain):
            cands.append(chained_u0(st, pack['u1'], a, rng))
        cnt = st.badcounts(np.array(cands), pack, [a])[a]
        i = int(cnt.argmax())
        if int(cnt[i]) > best_c:
            best_c, best_u = int(cnt[i]), cands[i].copy()
            stall = 0
        else:
            stall += 1
            if stall >= 2:
                break
    return best_c, best_u


# ----------------------------------------------------------------------
# one full experiment at (n, k, q)
# ----------------------------------------------------------------------
def run_setting(n, k, q, a_list, interior_as, rng, cfg):
    t0 = time.time()
    st = Setting(n, k, q)
    print(f"\n{'='*78}\nSETTING n={n} k={k} rho={k}/{n} q={q} (q>=n^4={n**4}: {q >= n**4}) "
          f"omega={st.om}  C(n,k)={st.P} interpolants", flush=True)
    print(f"window delta in (0.5,0.75) => agreement a interior={interior_as} "
          f"boundary={[a for a in a_list if a not in interior_as]}", flush=True)

    dirs = build_directions(st, rng, cfg['sparse_pairs'], cfg['cvals'], cfg['n_rand_dirs'])
    U_shared = shared_u0_pool(st, rng, cfg['n_far'], cfg['n_piece'], cfg['n_rand_u0'])
    print(f"{len(dirs)} directions, {len(U_shared)} shared u0 candidates "
          f"+ {cfg['n_chain']}*{len(a_list)} per-u1 chained adversarial", flush=True)

    rec = {}   # label -> dict(class, agreemax, per-a (count, u0))
    for di, (lab, cls, u1) in enumerate(dirs):
        pack = st.pack(u1)
        extra = [chained_u0(st, u1, a, rng) for a in a_list for _ in range(cfg['n_chain'])]
        U = np.vstack([U_shared, np.array(extra)])
        counts = st.badcounts(U, pack, a_list, chunk=cfg['chunk'])
        r = dict(cls=cls, agreemax=pack['agreemax'], pack=pack)
        for a in a_list:
            i = int(counts[a].argmax())
            worst = int(counts[a][i])
            # invariant: worst == q  <=>  direction is a-close to code
            assert (worst == q) == (pack['agreemax'] >= a), \
                f"degeneracy invariant broken at {lab} a={a}: worst={worst} agreemax={pack['agreemax']}"
            r[a] = (worst, U[i].copy())
        rec[lab] = r
        if (di + 1) % 50 == 0:
            print(f"  ..{di+1}/{len(dirs)} dirs  [{time.time()-t0:.0f}s]", flush=True)

    # random consistency checks vs brute force (independent code path)
    print("consistency spot-checks vs brute force over ALL gamma:", flush=True)
    labs = list(rec.keys())
    for _ in range(cfg['n_spot']):
        lab = labs[int(rng.integers(len(labs)))]
        a = a_list[int(rng.integers(len(a_list)))]
        u0 = rng.integers(0, q, size=n).astype(np.int64)
        fast = int(st.badcounts(u0[None, :], rec[lab]['pack'], [a])[a][0])
        brute = st.brute_count(u0, rec[lab]['pack']['u1'], a, gchunk=cfg['gchunk'])
        assert fast == brute, f"MISMATCH {lab} a={a}: fast={fast} brute={brute}"
        print(f"  OK {lab} a={a}: fast==brute=={fast}", flush=True)

    verdicts = {}
    for a in a_list:
        tag = "INTERIOR" if a in interior_as else "JOHNSON-BOUNDARY"
        print(f"\n--- level a={a} (delta={1-a/n:.3f}) [{tag}] q={q} ---", flush=True)
        monos = [(lab, r) for lab, r in rec.items() if r['cls'] == 'monomial']
        deg_m = [(lab, r['agreemax']) for lab, r in monos if r['agreemax'] >= a]
        elig_m = [(lab, r) for lab, r in monos if r['agreemax'] < a]
        print(f"  monomials degenerate at a={a} (a-close to code, worst=q trivially): "
              f"{deg_m if deg_m else 'none'}", flush=True)
        spreads = [(lab, r) for lab, r in rec.items()
                   if r['cls'] != 'monomial' and r['agreemax'] < a]
        n_deg_s = sum(1 for lab, r in rec.items()
                      if r['cls'] != 'monomial' and r['agreemax'] >= a)
        print(f"  eligible: {len(elig_m)} monomials, {len(spreads)} spread "
              f"({n_deg_s} spread degenerate, excluded)", flush=True)

        # refine decision-critical directions
        elig_m.sort(key=lambda x: -x[1][a][0])
        spreads.sort(key=lambda x: -x[1][a][0])
        crit = elig_m[:cfg['n_ref_m']] + spreads[:cfg['n_ref_s']]
        for lab, r in crit:
            c0, u0 = r[a]
            c1, u1best = refine_dir(st, r['pack'], a, u0, c0, rng,
                                    rounds=cfg['ref_rounds'], batch=cfg['ref_batch'],
                                    nchain=cfg['ref_chain'])
            if c1 > c0:
                r[a] = (c1, u1best)

        elig_m.sort(key=lambda x: -x[1][a][0])
        spreads.sort(key=lambda x: -x[1][a][0])
        print("  monomial worst-u0 bad counts (post-refine):", flush=True)
        for lab, r in elig_m:
            print(f"    {lab:24s} agreemax={r['agreemax']}  worst={r[a][0]}", flush=True)
        best_m_lab, best_m = elig_m[0][0], int(elig_m[0][1][a][0])
        print("  top-12 spread worst-u0 bad counts:", flush=True)
        for lab, r in spreads[:12]:
            print(f"    {lab:24s} agreemax={r['agreemax']}  worst={r[a][0]}", flush=True)
        best_s_lab, best_s = spreads[0][0], int(spreads[0][1][a][0])

        winners = [(lab, int(r[a][0])) for lab, r in spreads if int(r[a][0]) > best_m]
        # brute-verify the decision-critical witnesses
        for lab, r in [(best_m_lab, rec[best_m_lab]), (best_s_lab, rec[best_s_lab])]:
            cfast, u0w = r[a]
            br = st.brute_count(u0w, r['pack']['u1'], a, gchunk=cfg['gchunk'])
            assert br == cfast, f"witness MISMATCH {lab} a={a}: fast={cfast} brute={br}"
        print(f"  [witnesses brute-verified: {best_m_lab}={best_m}, {best_s_lab}={best_s}]",
              flush=True)

        if winners:
            v = "REFUTED-candidate"
            print(f"  >>> a={a}: SPREAD BEATS EVERY MONOMIAL: {winners[:8]} "
                  f"vs best monomial {best_m_lab}={best_m}", flush=True)
        elif best_s == best_m:
            v = "TIE"
            print(f"  >>> a={a}: TIE at {best_m} ({best_s_lab} vs {best_m_lab}) "
                  f"-- monomials NOT strictly beaten", flush=True)
        else:
            v = "MONOMIALS-DOMINATE"
            print(f"  >>> a={a}: monomials dominate: best mono {best_m_lab}={best_m} "
                  f">= best spread {best_s_lab}={best_s}", flush=True)
        verdicts[a] = dict(verdict=v, best_mono=(best_m_lab, best_m),
                           best_spread=(best_s_lab, best_s),
                           interior=(a in interior_as),
                           degenerate_monos=deg_m)
    print(f"[setting done in {time.time()-t0:.0f}s]", flush=True)
    return verdicts


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--stage', choices=['n8', 'n16', 'all'], default='all')
    ap.add_argument('--q16', type=int, default=65537,
                    help='prime for the n16 stage (default 65537 = Fermat; use generic '
                         'primes 65617 (v2=4) / 65633 (v2=5) for the structured-prime '
                         'replication check)')
    args = ap.parse_args()
    rng = np.random.default_rng(46605)
    allv = {}

    if args.stage in ('n8', 'all'):
        n, k = 8, 2
        q1 = least_prime_1mod(n, n ** 4)
        q2 = least_prime_1mod(n, 2 * q1)
        print(f"n=8 primes: q1={q1}, q2={q2} (both ==1 mod 8, >= n^4)", flush=True)
        cfg8 = dict(sparse_pairs=list(itertools.combinations(range(8), 2)),
                    cvals=None, n_rand_dirs=200,
                    n_far=40, n_piece=50, n_rand_u0=2000, n_chain=12,
                    chunk=512, gchunk=8192, n_spot=6,
                    n_ref_m=3, n_ref_s=6, ref_rounds=6, ref_batch=192, ref_chain=64)
        for q in (q1, q2):
            cfg = dict(cfg8)
            cfg['cvals'] = [1, 2, q - 2] + [int(rng.integers(3, q)) for _ in range(3)]
            allv[f"n8_q{q}"] = run_setting(8, 2, q, a_list=[3, 4], interior_as=[3],
                                           rng=rng, cfg=cfg)

    if args.stage in ('n16', 'all'):
        n, k, q = 16, 4, args.q16
        assert q % n == 1 and q >= n ** 4 - 1 and is_prime(q)
        pairs_all = list(itertools.combinations(range(16), 2))
        sel = [pairs_all[int(i)] for i in
               np.random.default_rng(7).choice(len(pairs_all), size=20, replace=False)]
        # always include the Fermat-run winners for the cross-prime replication check
        for forced in ((7, 13), (4, 8), (4, 14)):
            if forced not in sel:
                sel.append(forced)
        cfg16 = dict(sparse_pairs=sel,
                     cvals=[1, int(np.random.default_rng(9).integers(3, q))],
                     n_rand_dirs=20,
                     n_far=12, n_piece=20, n_rand_u0=160, n_chain=8,
                     chunk=96, gchunk=512, n_spot=1,
                     n_ref_m=2, n_ref_s=4, ref_rounds=3, ref_batch=96, ref_chain=32)
        allv[f"n16_q{q}"] = run_setting(16, 4, q, a_list=[5, 6, 7], interior_as=[5, 6, 7],
                                        rng=rng, cfg=cfg16)

    print("\n" + "=" * 78)
    print("FINAL SUMMARY (windowed SumsetExtremal, worst-u0 search is heuristic/"
          "lower-bound; witnesses brute-verified):", flush=True)
    for key, vs in allv.items():
        for a, v in vs.items():
            print(f"  {key} a={a} {'INTERIOR' if v['interior'] else 'BOUNDARY'}: "
                  f"{v['verdict']}  best_mono={v['best_mono']} best_spread={v['best_spread']}",
                  flush=True)


if __name__ == '__main__':
    main()
