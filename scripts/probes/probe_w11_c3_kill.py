#!/usr/bin/env python3
"""probe_w11_c3_kill.py -- LANE W11 (#466): refute-first attack on SpreadExcessLaw C=3.

TARGET (committed lane Frontier/_SpreadExcessLaw.lean):
  SpreadExcessLaw C: for far 2-component directions in the window (k+2 <= a,
  a^2 <= n*k), worstBad(spread) <= C * monoBaseline.  C=2 is DEAD (referee,
  ratio >= 21/9 at n=16); C=3 is the live candidate.

MECHANISM (this probe's new weapon -- the MULTI-PENCIL LOCK):
  The referee's constructive floor (kb deltastar-466b-p5-referee-2026-07-01.md)
  uses ONE elevated pencil (codeword h with agreement s = a-1 on set S): every
  coordinate l not in S yields one bad gamma.  NEW OBSERVATION: locking a pencil
  is a LINEAR condition on u0 (u0|S must extend to a codeword: codim |S|-k), so
  MANY elevated pencils can be locked SIMULTANEOUSLY by solving a linear system;
  each locked pencil i and each l not in S_i yields bad gamma
      gamma_{i,l} = (c_i(x_l) - u0_l) / (u1_l - h_i(x_l)),
  giving up to sum_i (n - s) bad scalars, i.e. ~m*(n-a+1) for m locked pencils.
  Analytic pencil census for even directions on mu_n (y = x^2 substitution):
    * n=16: u1 = x^4 + c*x^14, c in mu_8: pencils <-> 3-subsets Y of mu_8 with
      prod(Y) = -c (times parity): 7 pencils, s = 6 = a-1 at a = 7.
    * n=32: u1 = x^4 + c*x^30, c in mu_16: pencils <-> 3-subsets Y of mu_16
      with e3(Y) = -c: ~35 pencils, s = 6 = a-1 at a = 7.
    * n=32: u1 = x^6 - z*x^4, z in mu_16: pencils <-> {s,-s,z}: 7 pencils.
  agreemax = 6 is EXACT and provable (u1 - codeword is a monic sextic: <= 6
  roots on an injective domain), so these directions are 7-FAR unconditionally.

KILL CONDITIONS:
  (K1) certified spread bad-count > 3 * (hardest-pushed monomial baseline) at a
       single (n,k,a,q) -> C=3 refuted in evidence (same standard as the C=2
       kill: spread side is certificate-verified, baseline is a search plateau).
  (K2) spread/mono ratio grows n=16 -> n=32 -> the law dies at EVERY constant C
       (the floor sum_i (n-s) grows ~ m*n vs baseline ~ n/(a-k-1)).

All spread counts are EXACT per candidate (interpolation-trick engine) and the
decision witnesses are re-verified through per-gamma certificates (an explicit
codeword agreeing on >= a points -- engine-independent lower bound).  Monomial
baseline gets a SYMMETRIC-OR-BETTER budget: shared pool + chained adversarial
seeds + planted single-pencil block seeds + hill climb.

Output: scripts/probes/_out_w11_c3_kill_<stage>.txt
"""
import argparse
import itertools
import sys
import time

import numpy as np

sys.path.insert(0, 'scripts/probes')
from probe_466_windowed_extremal import (Setting, chained_u0, interp_poly,
                                         is_prime, least_prime_1mod,
                                         poly_eval_vec, shared_u0_pool)


def v2(m):
    r = 0
    while m % 2 == 0:
        m //= 2
        r += 1
    return r


def is_gen_fermat(q):
    m = q - 1
    for s in range(1, 40):
        e = 1 << s
        if 2 ** e > m:
            break
        b = round(m ** (1.0 / e))
        for bb in (b - 1, b, b + 1):
            if bb >= 2 and bb ** e == m:
                return True
    return False


def primes_two_v2(n, lo):
    out, m, seen = [], lo, set()
    while len(out) < 2:
        p = least_prime_1mod(n, m)
        m = p + 1
        if is_gen_fermat(p):
            continue
        if v2(p - 1) in seen:
            continue
        seen.add(v2(p - 1))
        out.append(p)
    return out


# ----------------------------------------------------------------------
# modular linear algebra (small systems)
# ----------------------------------------------------------------------
def mod_rref(M, q):
    """Row-reduce M (copy) mod q; returns (R, pivots)."""
    R = M.copy() % q
    rows, cols = R.shape
    piv = []
    r = 0
    for c in range(cols):
        pr = None
        for rr in range(r, rows):
            if R[rr, c] % q:
                pr = rr
                break
        if pr is None:
            continue
        R[[r, pr]] = R[[pr, r]]
        inv = pow(int(R[r, c]), q - 2, q)
        R[r] = R[r] * inv % q
        for rr in range(rows):
            if rr != r and R[rr, c]:
                R[rr] = (R[rr] - R[rr, c] * R[r]) % q
        piv.append(c)
        r += 1
        if r == rows:
            break
    return R, piv


def mod_nullspace(M, q):
    """Basis (rows) of the right nullspace of M mod q."""
    rows, cols = M.shape
    if rows == 0:
        return np.eye(cols, dtype=np.int64)
    R, piv = mod_rref(M.astype(np.int64), q)
    free = [c for c in range(cols) if c not in piv]
    basis = []
    for f in free:
        v = np.zeros(cols, dtype=np.int64)
        v[f] = 1
        for i, p in enumerate(piv):
            v[p] = (-R[i, f]) % q
        basis.append(v)
    return np.array(basis, dtype=np.int64) if basis else np.zeros((0, cols), dtype=np.int64)


def rs_restriction_conditions(st, S):
    """Left-nullspace rows of the |S| x k Vandermonde on xs[S]: the linear
    conditions 'w|S extends to a codeword' (codim |S|-k)."""
    q, k = st.q, st.k
    xs = st.xs[np.array(sorted(S), dtype=np.int64)]
    V = np.zeros((len(S), k), dtype=np.int64)
    for i, x in enumerate(xs):
        V[i] = [pow(int(x), t, q) for t in range(k)]
    N = mod_nullspace(V.T, q)  # rows w with w @ V = 0  (nullspace of V^T)
    return np.array(sorted(S), dtype=np.int64), N


# ----------------------------------------------------------------------
# elevated-pencil extraction (exact)
# ----------------------------------------------------------------------
def elevated_pencils(st, pack):
    """All distinct (S, h) with |agreeSet(h,u1)| = agreemax, from the exact
    per-subset residuals."""
    B = pack['B']
    base = (B == 0).sum(axis=1)
    smax = int(base.max())
    pencils = {}
    for p in np.where(base == smax)[0]:
        S = frozenset(np.where(B[p] == 0)[0].tolist())
        if S not in pencils:
            pencils[S] = (st.q + pack['u1'] - B[p]) % st.q  # h = u1 - B
    return smax, [(np.array(sorted(S), dtype=np.int64), h)
                  for S, h in pencils.items()]


def codeword_through(st, w, S):
    """The unique codeword agreeing with w on S (|S| >= k, assumes w|S is in
    RS|S); returns its evaluation vector, or None if it does not extend."""
    q, k = st.q, st.k
    idx = [int(i) for i in S[:k]]
    coeffs = interp_poly([int(st.xs[i]) for i in idx], [int(w[i]) for i in idx], q)
    cv = poly_eval_vec(coeffs, st.xs, q)
    if all(int(cv[i]) == int(w[i]) % q for i in S):
        return cv
    return None


def lock_and_sample(st, pack, pencil_subset, rng, nsamp):
    """Solve the joint lock for the given pencils; sample u0 candidates from
    the solution space."""
    q, n = st.q, st.n
    rows = []
    for (S, _h) in pencil_subset:
        Sarr, N = rs_restriction_conditions(st, S)
        for w in N:
            row = np.zeros(n, dtype=np.int64)
            row[Sarr] = w
            rows.append(row)
    M = np.array(rows, dtype=np.int64) if rows else np.zeros((0, n), dtype=np.int64)
    Z = mod_nullspace(M, q)
    d = len(Z)
    if d == 0:
        return None, 0
    C = rng.integers(1, q, size=(nsamp, d)).astype(np.int64)
    return (C @ Z) % q, d


# ----------------------------------------------------------------------
# per-gamma certificate verification (engine-independent)
# ----------------------------------------------------------------------
def certified_bad_count(st, u0, pack, a):
    """Exact bad set via the engine's dissection, then re-verify EVERY gamma
    with an explicit codeword certificate. Returns (count, sorted gammas)."""
    q = st.q
    u0 = np.asarray(u0, dtype=np.int64) % q
    UT = u0[None, :][:, st.Tidx]
    Pv = np.einsum('ptl,npt->npl', st.C, UT) % q
    A = (u0[None, None, :] - Pv) % q
    Bz = (pack['B'] == 0)[None]
    base = ((A == 0) & Bz).sum(axis=2)[0]
    prod = ((q - A) % q) * pack['Binv'][None] % q
    gamma = np.where(pack['valid'][None], prod, q)[0]
    hits = {}
    for p in range(st.P):
        need = a - int(base[p])
        if need <= 0:
            raise RuntimeError('degenerate direction')
        g = gamma[p][gamma[p] < q]
        vals, cnts = np.unique(g, return_counts=True)
        for vv, cc in zip(vals, cnts):
            if cc >= need:
                hits.setdefault(int(vv), []).append(p)
    # certificate check: for each gamma, take one firing subset, interpolate,
    # verify agreement >= a directly
    ok = {}
    for g, plist in hits.items():
        p = plist[0]
        w = (u0 + g * pack['u1']) % q
        T = [int(t) for t in st.Tidx[p]]
        coeffs = interp_poly([int(st.xs[t]) for t in T], [int(w[t]) for t in T], q)
        cv = poly_eval_vec(coeffs, st.xs, q)
        agr = int((cv == w).sum())
        assert agr >= a, f'CERTIFICATE FAILED gamma={g}: agreement {agr} < {a}'
        ok[g] = agr
    return len(ok), sorted(ok.keys())


# ----------------------------------------------------------------------
# planted single-pencil block seed (works for ANY direction incl. monomials)
# ----------------------------------------------------------------------
def planted_u0(st, pack, a, rng):
    q, n, k = st.q, st.n, st.k
    u1 = pack['u1']
    B = pack['B']
    base = (B == 0).sum(axis=1)
    # pick a random subset among those with maximal base (best pencil)
    smax = int(base.max())
    cand = np.where(base == smax)[0]
    p = int(cand[rng.integers(len(cand))])
    S = np.where(B[p] == 0)[0]
    h = (q + u1 - B[p]) % q
    s = len(S)
    w = a - s
    if w <= 0:
        raise RuntimeError('direction not far')
    rest = np.array([l for l in range(n) if l not in set(S.tolist())])
    rng.shuffle(rest)
    m = len(rest) // w
    # c0 random codeword
    coeffs = [int(rng.integers(q)) for _ in range(k)]
    c0 = poly_eval_vec(coeffs, st.xs, q)
    u0 = c0.copy()
    gammas = rng.permutation(q - 1)[:m] + 1
    for b in range(m):
        blk = rest[b * w:(b + 1) * w]
        u0[blk] = (c0[blk] - int(gammas[b]) * ((u1[blk] - h[blk]) % q)) % q
    return u0 % q


# ----------------------------------------------------------------------
# hill climb (exact counts)
# ----------------------------------------------------------------------
def climb(st, pack, a, u0, c0, rng, rounds, batch, nchain, chunk):
    best_u, best_c = u0.copy(), int(c0)
    stall = 0
    for _ in range(rounds):
        cands = [best_u]
        for _ in range(batch):
            m = best_u.copy()
            for _ in range(int(rng.integers(1, 4))):
                m[int(rng.integers(st.n))] = int(rng.integers(st.q))
            cands.append(m)
        for _ in range(nchain):
            cands.append(chained_u0(st, pack['u1'], a, rng))
        cnt = st.badcounts(np.array(cands, dtype=np.int64), pack, [a], chunk=chunk)[a]
        i = int(cnt.argmax())
        if int(cnt[i]) > best_c:
            best_c, best_u = int(cnt[i]), cands[i].copy()
            stall = 0
        else:
            stall += 1
            if stall >= 3:
                break
    return best_c, best_u


# ----------------------------------------------------------------------
# the spread-side multi-lock attack for one direction
# ----------------------------------------------------------------------
def attack_direction(st, u1, a, rng, budget, label):
    q, n = st.q, st.n
    pack = st.pack(u1)
    if pack['agreemax'] >= a:
        print(f'  [{label}] DEGENERATE (agreemax={pack["agreemax"]} >= a={a}) -- skip',
              flush=True)
        return None
    smax, pencils = elevated_pencils(st, pack)
    print(f'  [{label}] agreemax={smax} ({a}-far), elevated pencils: {len(pencils)}',
          flush=True)
    best = (0, None)
    t0 = time.time()
    # lock-subset scan: full set, then random subsets of every size
    sizes = sorted({len(pencils)} | {max(1, len(pencils) - d) for d in (1, 2, 3)}
                   | set(range(1, min(len(pencils), 17))))
    for msz in sorted(sizes, reverse=True):
        tries = budget['lock_tries'] if msz < len(pencils) else 1
        for _ in range(tries):
            idx = rng.choice(len(pencils), size=msz, replace=False)
            sub = [pencils[i] for i in idx]
            U, d = lock_and_sample(st, pack, sub, rng, budget['nsamp'])
            if U is None:
                continue
            cnt = st.badcounts(U, pack, [a], chunk=budget['chunk'])[a]
            i = int(cnt.argmax())
            if int(cnt[i]) > best[0]:
                best = (int(cnt[i]), U[i].copy())
                print(f'    lock m={msz} (dim={d}): new best exact count {best[0]} '
                      f'[{time.time()-t0:.0f}s]', flush=True)
    # generic seeds too (pool + chained + planted)
    seeds = [planted_u0(st, pack, a, rng) for _ in range(budget['nplant'])]
    seeds += [chained_u0(st, u1, a, rng) for _ in range(budget['nchainseed'])]
    U = np.array(seeds, dtype=np.int64)
    cnt = st.badcounts(U, pack, [a], chunk=budget['chunk'])[a]
    i = int(cnt.argmax())
    if int(cnt[i]) > best[0]:
        best = (int(cnt[i]), U[i].copy())
    # climb on the best
    c1, u1b = climb(st, pack, a, best[1], best[0], rng,
                    budget['rounds'], budget['batch'], budget['nchain'],
                    budget['chunk'])
    if c1 > best[0]:
        best = (c1, u1b)
    # certify
    ccount, gammas = certified_bad_count(st, best[1], pack, a)
    assert ccount == best[0], f'engine {best[0]} != certified {ccount}'
    print(f'  [{label}] FINAL certified worstBad >= {ccount} '
          f'(every gamma certificate-verified) [{time.time()-t0:.0f}s]', flush=True)
    return dict(label=label, count=ccount, u0=best[1].tolist(), gammas=gammas,
                agreemax=smax, npencils=len(pencils))


# ----------------------------------------------------------------------
# monomial baseline (symmetric-or-better effort)
# ----------------------------------------------------------------------
def mono_baseline(st, a, rng, budget):
    q, n = st.q, st.n
    results = {}
    U_shared = shared_u0_pool(st, rng, budget['n_far'], budget['n_piece'],
                              budget['n_rand_u0'])
    for j in range(n):
        u1 = st.mono(j)
        pack = st.pack(u1)
        if pack['agreemax'] >= a:
            results[j] = ('close', pack['agreemax'])
            continue
        seeds = [planted_u0(st, pack, a, rng) for _ in range(budget['nplant'])]
        seeds += [chained_u0(st, u1, a, rng)
                  for _ in range(budget['nchainseed'])]
        U = np.vstack([U_shared, np.array(seeds, dtype=np.int64)])
        cnt = st.badcounts(U, pack, [a], chunk=budget['chunk'])[a]
        i = int(cnt.argmax())
        c0, u0 = int(cnt[i]), U[i].copy()
        c1, u0b = climb(st, pack, a, u0, c0, rng, budget['rounds'],
                        budget['batch'], budget['nchain'], budget['chunk'])
        # certify the per-direction winner
        cc, _ = certified_bad_count(st, u0b if c1 > c0 else u0, pack, a)
        assert cc == max(c1, c0)
        results[j] = ('far', pack['agreemax'], cc)
        print(f'    mono j={j}: agreemax={pack["agreemax"]} worst={cc}', flush=True)
    far = {j: r[2] for j, r in results.items() if r[0] == 'far'}
    bl = max(far.values()) if far else 0
    print(f'  monomial baseline (certified search max) = {bl}  '
          f'far-monos={sorted(far.items())}', flush=True)
    return bl, results


# ----------------------------------------------------------------------
# stages
# ----------------------------------------------------------------------
def stage_n16(rng):
    n, k, a = 16, 4, 7
    print(f'\n{"#"*78}\nSTAGE n={n} k={k} a={a} (window: k+2={k+2}<=a, '
          f'a^2={a*a}<=nk={n*k})', flush=True)
    out = {}
    for q in (65617, 65633):
        assert is_prime(q) and q % n == 1 and q >= n ** 4
        st = Setting(n, k, q)
        print(f'\n== q={q} v2={v2(q-1)} omega={st.om} C(n,k)={st.P}', flush=True)
        mu8 = sorted({pow(int(x), 2, q) for x in st.xs})
        bud = dict(lock_tries=6, nsamp=320, chunk=64, nplant=64, nchainseed=64,
                   rounds=10, batch=160, nchain=48)
        best = (0, None)
        dirs = []
        dirs.append((f'x4+x14', (st.mono(4) + st.mono(14)) % q))
        dirs.append((f'x4+{mu8[1]}x14', (st.mono(4) + mu8[1] * st.mono(14)) % q))
        dirs.append((f'x6-{mu8[1]}x4', (st.mono(6) + (q - mu8[1]) * st.mono(4)) % q))
        for lab, u1 in dirs:
            r = attack_direction(st, u1, a, rng, bud, lab)
            if r and r['count'] > best[0]:
                best = (r['count'], r)
        mb_bud = dict(n_far=24, n_piece=40, n_rand_u0=300, nplant=48,
                      nchainseed=48, chunk=64, rounds=8, batch=128, nchain=32)
        print(f'\n-- monomial baseline q={q}:', flush=True)
        bl, _ = mono_baseline(st, a, rng, mb_bud)
        ratio = best[0] / bl if bl else float('inf')
        verdict = 'C=3 KILLED (in evidence)' if best[0] > 3 * bl else 'C=3 SURVIVES here'
        print(f'\n>>> n={n} q={q}: best spread (certified) = {best[0]} '
              f'[{best[1]["label"]}], mono baseline = {bl}, RATIO = {ratio:.3f} '
              f'-> {verdict}', flush=True)
        out[q] = dict(spread=best[0], spread_label=best[1]['label'],
                      spread_u0=best[1]['u0'], spread_gammas=best[1]['gammas'],
                      baseline=bl, ratio=ratio)
    return out


def stage_n32(rng, heavy_baseline=True):
    n, k, a = 32, 4, 7
    print(f'\n{"#"*78}\nSTAGE n={n} k={k} a={a} (window: k+2={k+2}<=a, '
          f'a^2={a*a}<=nk={n*k})', flush=True)
    qs = primes_two_v2(n, n ** 4)
    print(f'primes: {qs} (v2 = {[v2(p-1) for p in qs]})', flush=True)
    out = {}
    for q in qs:
        t0 = time.time()
        st = Setting(n, k, q)
        print(f'\n== q={q} v2={v2(q-1)} omega={st.om} C(n,k)={st.P} '
              f'[setup {time.time()-t0:.0f}s]', flush=True)
        mu16 = sorted({pow(int(x), 2, q) for x in st.xs})
        bud = dict(lock_tries=4, nsamp=96, chunk=8, nplant=24, nchainseed=24,
                   rounds=8, batch=48, nchain=16)
        best = (0, None)
        dirs = []
        # the 35-pencil family x^4 + c*x^30, c in mu_16
        for c in (mu16[1], mu16[len(mu16) // 3]):
            dirs.append((f'x4+{c}x30', (st.mono(4) + c * st.mono(30)) % q))
        # the 7-pencil family x^6 - z*x^4, z in mu_16
        z = mu16[1]
        dirs.append((f'x6-{z}x4', (st.mono(6) + (q - z) * st.mono(4)) % q))
        for lab, u1 in dirs:
            r = attack_direction(st, u1, a, rng, bud, lab)
            if r and r['count'] > best[0]:
                best = (r['count'], r)
        if heavy_baseline:
            mb_bud = dict(n_far=12, n_piece=24, n_rand_u0=80, nplant=32,
                          nchainseed=32, chunk=8, rounds=6, batch=48, nchain=16)
            print(f'\n-- monomial baseline q={q}:', flush=True)
            bl, _ = mono_baseline(st, a, rng, mb_bud)
        else:
            bl = None
        ratio = best[0] / bl if bl else float('nan')
        verdict = ('C=3 KILLED (in evidence)' if bl and best[0] > 3 * bl
                   else 'C=3 SURVIVES here' if bl else 'no baseline run')
        print(f'\n>>> n={n} q={q}: best spread (certified) = {best[0]} '
              f'[{best[1]["label"]}], mono baseline = {bl}, RATIO = {ratio} '
              f'-> {verdict}', flush=True)
        out[q] = dict(spread=best[0], spread_label=best[1]['label'],
                      spread_u0=best[1]['u0'], spread_gammas=best[1]['gammas'],
                      baseline=bl, ratio=ratio)
        break  # second prime only if first is decisive-marginal; keep runtime sane
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--stage', choices=['n16', 'n32', 'all'], default='all')
    args = ap.parse_args()
    rng = np.random.default_rng(46711)
    res = {}
    if args.stage in ('n16', 'all'):
        res['n16'] = stage_n16(rng)
    if args.stage in ('n32', 'all'):
        res['n32'] = stage_n32(rng)
    print('\n' + '=' * 78)
    print('W11 C=3 KILL SUMMARY (spread counts certificate-verified; baseline = '
          'hardest-pushed search plateau, honest lower bound):', flush=True)
    for stage, d in res.items():
        for q, v in d.items():
            print(f'  {stage} q={q}: spread={v["spread"]} [{v["spread_label"]}] '
                  f'baseline={v["baseline"]} ratio={v["ratio"]}', flush=True)


if __name__ == '__main__':
    main()
