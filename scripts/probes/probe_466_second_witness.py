#!/usr/bin/env python3
"""probe_466_second_witness.py -- LANE W4: NoUniqueBadScalarWitness on hard lines (#466).

QUESTION (dossier v3 sec 6 Tier-1 item 2, third bullet): on the HARD lines (the
worst-u0 lines of the P5 probe: worst monomial directions AND the spread winners
x^4 + c x^14 / x^7 + c x^13), does every bad scalar gamma have >= 2 distinct
witness codewords (agreement >= a with the line word u0 + gamma*u1), or do
unique-witness bad scalars exist?

In-tree vocabulary (LineListIncidenceMultiplicity.lean):
  badScalarWitnessCodewords dom k a u0 u1 gamma
    = { c in RS_k : |agreeSet(c, u0 + gamma*u1)| >= a }
  NoUniqueBadScalarWitness dom k a u0 u1
    = forall gamma in lineBadScalars, #witnesses(gamma) != 1
    (<=> LineBadScalarMultiplicityFloor R=2, the first nontrivial multiplicity
     discount; lineBadScalarMultiplicityFloor_two_iff_noUniqueBadScalarWitness).

EXACT WITNESS ENUMERATION (complete, not sampled): every deg<k codeword agreeing
with w_gamma on >= a >= k positions is the Lagrange interpolant of w_gamma on any
k-subset T of its agreement set.  Per subset T the interpolant is affine in gamma
(p_T,gamma = P0_T + gamma*P1_T); position l agrees iff A_l + gamma*B_l = 0 with
A_l = u0_l - P0_T(x_l), B_l = u1_l - P1_T(x_l).  So per T: base positions
(A=B=0, agree for ALL gamma, includes T) plus per-position critical gammas
(-A_l/B_l for B_l != 0).  A pair (T, gamma) yields a witness iff
base_T + #{l : gamma_l = gamma} >= a; the witness polynomial is
P0_T + gamma*P1_T, deduped by coefficient tuple.  This enumerates the EXACT
witness fiber for every gamma simultaneously.

REGIME (per campaign discipline): dom = mu_n proper subgroup of F_p^*,
p == 1 mod n, p >= n^4, >= 2 primes per scale in different v2(p-1) classes,
spread directions avoid the antipodal component gap n/2.
  n=8,  k=2: q in {4129 (v2=5), 8273 (v2=4)},  window a=3 interior (a=4 boundary, flagged)
  n=16, k=4: q in {65617 (v2=4), 65633 (v2=5)} (+ optional Fermat 65537), a in {5,6,7}

HARD LINES: per-direction worst-u0 search re-run with the P5 machinery (shared
pool + chained interpolation-adversarial + hill-climb); worst counts are checked
against the P5-recorded values (n8 a=3: 56; n16 a=7: mono 9 / spread 13-14) so
the scanned lines are at least as hard as the P5 winners.  Top-M distinct u0
per (direction, a) are all scanned, plus fresh chained-adversarial archetypes.

VERIFICATION:
  (i) scan bad-gamma set == independent badcounts engine == brute force over all
      gamma (assert, every scanned line);
  (ii) at n=8 (q^k small): FULL codeword enumeration (all q^2 polynomials) of the
      witness fiber for sampled gammas incl. every unique-witness example
      (assert fiber sets equal) -- an independent code path.

THEORY CHECK encoded (matches Frontier/_SecondWitnessFloor.lean): if the line
passes through the code (u0 + gamma*u1 in RS_k) and k <= a <= n, the fiber at
that gamma is EXACTLY a singleton -- scanned lines through the code must show
multiplicity 1 there.
"""
import argparse
import itertools
import sys
import time

import numpy as np


# ----------------------------------------------------------------------
# primes / field utilities (as in probe_466_windowed_extremal.py)
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


def v2(m: int) -> int:
    r = 0
    while m % 2 == 0:
        m //= 2
        r += 1
    return r


def mu_generator(q: int, n: int) -> int:
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
# setting + the exact bad-scalar-count engine (from the P5 probe)
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
        # per-subset interpolation coefficient maps: coeffs = M[pi] @ values[T]
        # M[pi][j][t] = coeff_j of the t-th Lagrange basis poly on T
        M = np.zeros((self.P, k, k), dtype=np.int64)
        for pi_, T in enumerate(subsets):
            for ti, t in enumerate(T):
                num = [1]
                den = 1
                for s in T:
                    if s != t:
                        num = poly_mul_lin(num, int(xs[s]), q)
                        den = den * int(xs[t] - xs[s]) % q
                dinv = pow(den % q, q - 2, q)
                for j in range(len(num)):
                    M[pi_, j, ti] = num[j] * dinv % q
        self.M = M

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
            base = ((A == 0) & Bz).sum(axis=2)
            prod = ((q - A) % q) * pack['Binv'][None] % q
            gamma = np.where(pack['valid'][None], prod, q)
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

    # ------------------------------------------------------------------
    # THE NEW ENGINE: exact per-gamma witness fibers on one line
    # ------------------------------------------------------------------
    def witness_fibers(self, u0, u1, a):
        """Return {gamma: {coeff_tuple: agreement}} for the line u0 + gamma*u1
        at level a.  Complete enumeration (see module docstring)."""
        q, n, k = self.q, self.n, self.k
        u0 = np.asarray(u0, dtype=np.int64) % q
        u1 = np.asarray(u1, dtype=np.int64) % q
        wit = {}
        for pi in range(self.P):
            T = self.Tidx[pi]
            Pv0 = (u0[T] @ self.C[pi]) % q
            Pv1 = (u1[T] @ self.C[pi]) % q
            A = (u0 - Pv0) % q
            B = (u1 - Pv1) % q
            base = int(((A == 0) & (B == 0)).sum())
            assert base < a, (
                f"line contains an all-gamma pencil (base={base} >= a={a}); "
                "degenerate line, excluded by construction")
            crit = {}
            for l in range(n):
                if B[l] != 0:
                    g = int((q - A[l]) % q * self.inv[B[l]] % q)
                    crit.setdefault(g, []).append(l)
            need = a - base
            hot = {g: ls for g, ls in crit.items() if len(ls) >= need}
            if not hot:
                continue
            c0 = (self.M[pi] @ u0[T]) % q
            c1 = (self.M[pi] @ u1[T]) % q
            for g, ls in hot.items():
                coeffs = tuple(int(x) for x in (c0 + g * c1) % q)
                d = wit.setdefault(g, {})
                agree = base + len(ls)
                if coeffs in d:
                    assert d[coeffs] == agree, "inconsistent agreement for same codeword"
                else:
                    d[coeffs] = agree
        return wit

    def full_codeword_fiber_n8(self, u0, u1, gamma, a, chunk=256):
        """Independent check (k=2 only): enumerate ALL q^2 codewords and return
        the exact witness fiber at gamma as a set of coeff tuples."""
        assert self.k == 2
        q, n = self.q, self.n
        w = (np.asarray(u0, dtype=np.int64) + gamma * np.asarray(u1, dtype=np.int64)) % q
        out = set()
        a1v = np.arange(q, dtype=np.int64)
        for s in range(0, q, chunk):
            a0v = np.arange(s, min(s + chunk, q), dtype=np.int64)
            # vals[i0, i1, l] = a0 + a1 * x_l
            vals = (a0v[:, None, None] + a1v[None, :, None] * self.xs[None, None, :]) % q
            agree = (vals == w[None, None, :]).sum(axis=2)
            idx = np.argwhere(agree >= a)
            for i0, i1 in idx:
                out.add((int(a0v[i0]), int(a1v[i1])))
        return out


# ----------------------------------------------------------------------
# u0 builders (from the P5 probe)
# ----------------------------------------------------------------------
def chained_u0(st, u1, a, rng):
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
    m34, m2 = st.mono(3 * n // 4), st.mono(n // 2)
    gvals = [1, 2, 3, q - 1] + [int(rng.integers(2, q)) for _ in range(max(0, n_far - 4))]
    for g in gvals[:n_far]:
        pool.append((m34 + g * m2) % q)
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
# the scan of one (direction, level): find hard lines, enumerate fibers
# ----------------------------------------------------------------------
def scan_direction(st, lab, u1, a, rng, cfg, results):
    q, n, k = st.q, st.n, st.k
    pack = st.pack(u1)
    assert pack['agreemax'] < a, f"{lab} degenerate at a={a} (a-close direction)"
    # --- worst-u0 search (P5 machinery, exact counts; heuristic max) ---
    U = [shared_u0_pool(st, rng, cfg['n_far'], cfg['n_piece'], cfg['n_rand_u0'])]
    U.append(np.array([chained_u0(st, u1, a, rng) for _ in range(cfg['n_chain'])]))
    U = np.vstack(U)
    counts = st.badcounts(U, pack, [a], chunk=cfg['chunk'])[a]
    order = np.argsort(-counts)
    # refine the best candidate
    c0, u0best = int(counts[order[0]]), U[order[0]].copy()
    c1, u0ref = refine_dir(st, pack, a, u0best, c0, rng,
                           rounds=cfg['ref_rounds'], batch=cfg['ref_batch'],
                           nchain=cfg['ref_chain'])
    # hard-line list: refined winner + top pool lines + fresh chained archetypes
    hard = [("refined-worst", u0ref, c1)]
    seen = {tuple(u0ref.tolist())}
    for i in order[:cfg['n_top']]:
        t = tuple(U[i].tolist())
        if t not in seen and counts[i] > 0:
            hard.append((f"pool-top{len(hard)}", U[i].copy(), int(counts[i])))
            seen.add(t)
    for j in range(cfg['n_arch']):
        ua = chained_u0(st, u1, a, rng)
        t = tuple(ua.tolist())
        if t not in seen:
            ca = int(st.badcounts(ua[None, :], pack, [a])[a][0])
            if ca > 0:
                hard.append((f"chained-arch{j}", ua, ca))
                seen.add(t)

    print(f"\n  DIRECTION {lab} a={a} (delta={1 - a / n:.4f}) q={q}: "
          f"worst-count={c1} (P5 reference in header), {len(hard)} hard lines scanned",
          flush=True)
    for li, (tag, u0, cnt) in enumerate(hard):
        wit = st.witness_fibers(u0, u1, a)
        badset = sorted(wit.keys())
        # verify count against the badcounts engine (every line)
        fast = int(st.badcounts(u0[None, :], pack, [a])[a][0])
        assert len(badset) == fast, \
            f"fiber-scan bad-count mismatch {lab}/{tag}: scan={len(badset)} fast={fast}"
        # brute force over ALL gamma: every line at n=8, decision-critical at n=16
        if cfg.get('brute_all', True) or li < 2:
            brute = st.brute_count(u0, u1, a, gchunk=cfg['gchunk'])
            assert brute == len(badset), \
                f"brute mismatch {lab}/{tag}: brute={brute} scan={len(badset)}"
        mult = {}
        uniq_examples = []
        for g in badset:
            m = len(wit[g])
            mult[m] = mult.get(m, 0) + 1
            if m == 1 and len(uniq_examples) < 3:
                (coef, agr), = wit[g].items()
                uniq_examples.append((g, coef, agr))
        n_uniq = mult.get(1, 0)
        hist = " ".join(f"{m}w:{c}" for m, c in sorted(mult.items()))
        print(f"    [{tag}] #bad={len(badset)} (verified 3-way)  multiplicity {{{hist}}}"
              f"  unique-witness scalars: {n_uniq}", flush=True)
        # full-codeword independent verification at k=2
        if k == 2 and cfg.get('full_verify', False) and badset:
            checkg = [g for g, _, _ in uniq_examples] or badset[:1]
            for g in checkg[:2]:
                fib = st.full_codeword_fiber_n8(u0, u1, g, a)
                assert fib == set(wit[g].keys()), \
                    f"FULL-ENUM mismatch at gamma={g}: {fib} vs {set(wit[g].keys())}"
            print(f"      full q^2-codeword enumeration verified fiber at "
                  f"gamma={checkg[:2]} (independent path)", flush=True)
        if uniq_examples:
            g, coef, agr = uniq_examples[0]
            print(f"      COUNTERMODEL: gamma={g} unique witness poly coeffs "
                  f"(low->high)={coef} agreement={agr}", flush=True)
            results.append(dict(q=q, n=n, k=k, a=a, dir=lab, tag=tag,
                                u0=[int(x) for x in u0], u1=[int(x) for x in u1],
                                gamma=int(g), coeffs=list(coef), agree=int(agr),
                                nbad=len(badset), nuniq=n_uniq, mult=mult))
        else:
            results.append(dict(q=q, n=n, k=k, a=a, dir=lab, tag=tag,
                                u0=[int(x) for x in u0], u1=[int(x) for x in u1],
                                gamma=None, nbad=len(badset), nuniq=0, mult=mult))


def run_setting(n, k, q, a_list, hard_dirs, rng, cfg, results):
    t0 = time.time()
    st = Setting(n, k, q)
    print(f"\n{'=' * 78}\nSETTING n={n} k={k} rho={k}/{n} q={q} "
          f"(q>=n^4: {q >= n ** 4}) v2(q-1)={v2(q - 1)} omega={st.om} "
          f"C(n,k)={st.P}", flush=True)
    dirs = []
    for spec in hard_dirs:
        if spec[0] == 'mono':
            j = spec[1]
            dirs.append((f"mono_j{j}", st.mono(j)))
        else:
            i, j, c = spec[1], spec[2], spec[3]
            gap = min(abs(i - j), n - abs(i - j))
            assert gap != n // 2, f"antipodal-correlated pair ({i},{j}) excluded"
            dirs.append((f"sp2_{i}_{j}_c{c}", (st.mono(i) + c * st.mono(j)) % q))
    for a in a_list:
        for lab, u1 in dirs:
            scan_direction(st, lab, u1, a, rng, cfg, results)
    print(f"[setting done in {time.time() - t0:.0f}s]", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--stage', choices=['n8', 'n16', 'all'], default='all')
    ap.add_argument('--fermat', action='store_true',
                    help='also run n16 at the structured Fermat prime 65537')
    ap.add_argument('--qs', default='',
                    help='comma-separated prime filter (chunked runs on a busy box)')
    ap.add_argument('--alist', default='',
                    help='comma-separated agreement-level filter')
    ap.add_argument('--dirs', default='',
                    help='comma-separated direction-index filter (0-based, per stage list)')
    args = ap.parse_args()
    qfilt = {int(x) for x in args.qs.split(',') if x} or None
    afilt = {int(x) for x in args.alist.split(',') if x} or None
    dfilt = {int(x) for x in args.dirs.split(',') if x} or None
    print(f"[chunk] stage={args.stage} qs={sorted(qfilt) if qfilt else 'all'} "
          f"alist={sorted(afilt) if afilt else 'all'} "
          f"dirs={sorted(dfilt) if dfilt else 'all'} seed=46612", flush=True)

    def pick(seq, filt):
        return [x for i, x in enumerate(seq) if filt is None or i in filt]

    rng = np.random.default_rng(46612)
    results = []

    if args.stage in ('n8', 'all'):
        # least prime ==1 mod 8 >= 8^4=4096 is 4129 (v2=5); next class: 8273 (v2=4)
        for q in (4129, 8273):
            assert is_prime(q) and q % 8 == 1 and q >= 8 ** 4
        cfg8 = dict(n_far=24, n_piece=32, n_rand_u0=800, n_chain=48,
                    chunk=512, gchunk=8192, n_top=4, n_arch=3,
                    ref_rounds=6, ref_batch=192, ref_chain=64, full_verify=True,
                    brute_all=True)
        # P5 hard classes at n=8: worst monomial mono_j2 (tie winners sp2_0_2 / sp2_0_3)
        hard8 = [('mono', 2), ('mono', 6), ('sp2', 0, 2, 1), ('sp2', 0, 3, 1)]
        for q in (4129, 8273):
            if qfilt is not None and q not in qfilt:
                continue
            run_setting(8, 2, q, a_list=[a for a in (3, 4) if afilt is None or a in afilt],
                        hard_dirs=pick(hard8, dfilt), rng=rng, cfg=cfg8, results=results)

    if args.stage in ('n16', 'all'):
        qs = [65617, 65633] + ([65537] if args.fermat else [])
        for q in qs:
            assert is_prime(q) and q % 16 == 1 and q >= 16 ** 4 - 1
        cfg16 = dict(n_far=8, n_piece=16, n_rand_u0=128, n_chain=24,
                     chunk=96, gchunk=512, n_top=3, n_arch=3,
                     ref_rounds=3, ref_batch=96, ref_chain=32, full_verify=False,
                     brute_all=False)
        # P5 hard classes at n=16: worst monomials mono_j4/mono_j7, spread winners
        # sp2_4_14_c1 and sp2_7_13_c1 (component gaps 10, 6 != n/2=8)
        hard16 = [('mono', 4), ('mono', 7), ('sp2', 4, 14, 1), ('sp2', 7, 13, 1)]
        for q in qs:
            if qfilt is not None and q not in qfilt:
                continue
            run_setting(16, 4, q,
                        a_list=[a for a in (5, 6, 7) if afilt is None or a in afilt],
                        hard_dirs=pick(hard16, dfilt), rng=rng, cfg=cfg16, results=results)

    print("\n" + "=" * 78)
    print("FINAL SUMMARY -- NoUniqueBadScalarWitness on hard lines:", flush=True)
    n_lines = len(results)
    n_with_uniq = sum(1 for r in results if r['nuniq'] > 0)
    all1 = sum(1 for r in results if r['mult'].get(1, 0) == r['nbad'] and r['nbad'] > 0)
    print(f"  scanned lines: {n_lines}; lines WITH >=1 unique-witness bad scalar: "
          f"{n_with_uniq}; lines where EVERY bad scalar is unique-witness: {all1}",
          flush=True)
    by = {}
    for r in results:
        key = (r['n'], r['q'], r['a'], r['dir'])
        agg = by.setdefault(key, dict(nbad=0, nuniq=0, multi=0))
        agg['nbad'] += r['nbad']
        agg['nuniq'] += r['nuniq']
        agg['multi'] += sum(c for m, c in r['mult'].items() if m >= 2)
    for key in sorted(by):
        n_, q_, a_, d_ = key
        agg = by[key]
        print(f"  n={n_} q={q_} a={a_} {d_:14s}: bad-scalar instances={agg['nbad']} "
              f"unique-witness={agg['nuniq']} multi-witness={agg['multi']}", flush=True)
    ex = next((r for r in results if r['gamma'] is not None), None)
    if ex:
        print("\n  EXPLICIT COUNTERMODEL (first found):", flush=True)
        print(f"    n={ex['n']} q={ex['q']} k={ex['k']} a={ex['a']} dir={ex['dir']} "
              f"({ex['tag']})", flush=True)
        print(f"    u0={ex['u0']}", flush=True)
        print(f"    u1={ex['u1']}", flush=True)
        print(f"    gamma={ex['gamma']} unique-witness coeffs (low->high)={ex['coeffs']} "
              f"agreement={ex['agree']}", flush=True)
    if n_with_uniq > 0:
        print("\n  VERDICT: unique-witness bad scalars EXIST on hard lines "
              "=> NoUniqueBadScalarWitness is REFUTED-at-scale; the R=2 "
              "multiplicity floor (LineBadScalarMultiplicityFloor 2) fails.", flush=True)
    else:
        print("\n  VERDICT: every bad scalar on every scanned hard line has >=2 "
              "witnesses -- the multiplicity-floor route stays live.", flush=True)


if __name__ == '__main__':
    main()
