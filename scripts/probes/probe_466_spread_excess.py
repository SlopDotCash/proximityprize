#!/usr/bin/env python3
"""probe_466_spread_excess.py -- LANE W1 (#466): the bounded spread-excess law.

Successor to the REFUTED windowed SumsetExtremal (tag
466-r1-windowed-extremal-spread-beats, note
docs/kb/deltastar-466-p5-replication-2026-07-01.md).

CONJECTURE UNDER TEST (spread-excess law): for RS[F_q, mu_n, k] with in-window
agreement a >= k+2, the worst-offset bad-scalar count over 2-Fourier-component
directions is <= C * (worst over monomial directions), absolute constant C <= 2.

TASK 1 -- SYMMETRIC EFFORT.  The original probe (probe_466_windowed_extremal.py)
gave the spread class more refinement rounds than the monomial class
(n_ref_m=2 vs n_ref_s=4 at n16), an asymmetry a skeptic flagged.  Here EVERY
direction -- monomial or spread -- receives an IDENTICAL search budget:
  * the same shared u0 candidate pool,
  * the same number of per-direction chained adversarial seeds,
  * the same refinement schedule (restarts x rounds x batch x chains),
so the measured max per class is search-effort-comparable.  All worst-count
values remain TRUE LOWER BOUNDS (exact interpolation-trick engine); the
decision-critical witnesses are re-verified by brute force over ALL gamma.

TASK 2 -- STRUCTURE OF THE WINNERS (pencil decomposition).  Every bad scalar
gamma is explained through at least one k-subset p: the witness codeword is
  c_{gamma,p} = I_p(u0) + gamma * I_p(u1)      (I_p = interpolation on p),
i.e. for FIXED p the witnesses form a PENCIL c0 + gamma*c1 in RS_k.  We
extract, for each decision-critical (direction, worst-u0):
  * the bad gammas + all firing subsets and distinct witness codewords,
  * the distinct pencils (c0, c1) they induce,
  * the exact minimum pencil cover of the bad set,
  * the per-pencil provable cap  #covered <= supp(u1-c1) / (a - z),
    z = #{l : (u1-c1)(x_l) = 0 and (u0-c0)(x_l) = 0}  (the Lean lemma
    pencil_heavy_scalar_card_le in Frontier/_SpreadExcessLaw.lean).
If the winners decompose into FEW pencils each obeying the cap, the excess is
"pencil concentration" (a bounded mechanism); if the cover is large/unstructured
the law has no visible mechanism.

SETTINGS (regime discipline: proper subgroup mu_n of F_p^*, p == 1 mod n,
p >= n^4, >=2 primes in different v2(p-1) classes, spread pairs with component
gap n/2 excluded as antipodally-correlated):
  * n=8,  k=2 (rho=1/4): a=4 = k+2 (= Johnson boundary delta=1/2, flagged);
        a=3 = k+1 reported but direction-blind (round-1 (D)).
  * n=16, k=4 (rho=1/4): a in {6,7} (window-interior, the discriminating levels).
  * n=16, k=2 (rho=1/8): window (1-sqrt(1/8), 7/8) => a in {3,4,5};
        a in {4,5} (>= k+2, interior; a=3 = k+1 blind, skipped).

Output: scripts/probes/_out_466_spread_excess.txt
KILL CONDITION for the law: max ratio grows with n or q (law false).
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


def v2(m: int) -> int:
    r = 0
    while m % 2 == 0:
        m //= 2
        r += 1
    return r


def primes_two_v2_classes(n: int, lo: int):
    """First two primes == 1 mod n, >= lo, with distinct v2(p-1)."""
    q1 = least_prime_1mod(n, lo)
    q = q1
    while True:
        q = least_prime_1mod(n, q + 1)
        if v2(q - 1) != v2(q1 - 1):
            return q1, q


# ----------------------------------------------------------------------
# symmetric-effort search: IDENTICAL budget for every direction
# ----------------------------------------------------------------------
def symmetric_search(st, pack, a_list, U_shared, rng, budget):
    """One direction: pool + equal chains, then per-level equal refinement.
    Returns {a: (worst_count, worst_u0)}. Exact counts (true lower bounds)."""
    nchain, restarts, max_rounds, batch, rchain, stall_lim = (
        budget['nchain'], budget['restarts'], budget['rounds'],
        budget['batch'], budget['rchain'], budget['stall'])
    extra = [chained_u0(st, pack['u1'], a, rng)
             for a in a_list for _ in range(nchain)]
    U = np.vstack([U_shared, np.array(extra)])
    counts = st.badcounts(U, pack, a_list, chunk=budget['chunk'])
    out = {}
    for a in a_list:
        i = int(counts[a].argmax())
        best_c, best_u = int(counts[a][i]), U[i].copy()
        for rs in range(restarts):
            if rs == 0:
                u, c = best_u.copy(), best_c
            else:  # fresh chain seed, same for every direction
                u = chained_u0(st, pack['u1'], a, rng)
                c = int(st.badcounts(u[None, :], pack, [a])[a][0])
            stall = 0
            for _ in range(max_rounds):
                cands = [u]
                for _ in range(batch):
                    m = u.copy()
                    for _ in range(int(rng.integers(1, 3))):
                        m[int(rng.integers(st.n))] = int(rng.integers(st.q))
                    cands.append(m)
                for _ in range(rchain):
                    cands.append(chained_u0(st, pack['u1'], a, rng))
                cnt = st.badcounts(np.array(cands), pack, [a],
                                   chunk=budget['chunk'])[a]
                j = int(cnt.argmax())
                if int(cnt[j]) > c:
                    c, u = int(cnt[j]), cands[j].copy()
                    stall = 0
                else:
                    stall += 1
                    if stall >= stall_lim:
                        break
            if c > best_c:
                best_c, best_u = c, u.copy()
        out[a] = (best_c, best_u)
    return out


# ----------------------------------------------------------------------
# task 2: bad-gamma extraction + pencil decomposition
# ----------------------------------------------------------------------
def bad_gamma_witnesses(st, u0, pack, a):
    """{gamma: [(subset_tuple, witness_coeff_tuple), ...]} for all bad gamma."""
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
            raise RuntimeError("degenerate direction reached dissection")
        vals, cnts = np.unique(gamma[p][gamma[p] < q], return_counts=True)
        for v, c in zip(vals, cnts):
            if c >= need:
                hits.setdefault(int(v), []).append(tuple(int(x)
                                                         for x in st.Tidx[p]))
    out = {}
    for g, subsets in hits.items():
        wit = []
        w = (u0 + g * pack['u1']) % q
        for T in subsets:
            coeffs = tuple(interp_poly([int(st.xs[t]) for t in T],
                                       [int(w[t]) for t in T], q))
            wit.append((T, coeffs))
        out[g] = wit
    return out


def pencil_of_subset(st, u0, u1, T):
    """(c0, c1) coefficient tuples: the pencil I_T(u0) + gamma*I_T(u1)."""
    xs = [int(st.xs[t]) for t in T]
    c0 = tuple(interp_poly(xs, [int(u0[t]) for t in T], st.q))
    c1 = tuple(interp_poly(xs, [int(u1[t]) for t in T], st.q))
    return c0, c1


def pencil_cover(st, u0, u1, a, bw):
    """Exact minimum pencil cover of the bad set + per-pencil caps.
    Pencils considered: those induced by firing subsets (complete for the
    engine's bad set: every bad gamma fires through >= 1 subset)."""
    q, n = st.q, st.n
    u0 = np.asarray(u0, dtype=np.int64) % q
    u1 = np.asarray(u1, dtype=np.int64) % q
    gam_list = sorted(bw.keys())
    pencils = {}   # (c0,c1) -> set of covered bad gammas
    for g, wit in bw.items():
        for (T, _c) in wit:
            key = pencil_of_subset(st, u0, u1, T)
            pencils.setdefault(key, set()).add(g)
    # per-pencil provable cap: supp(u1-c1)/(a-z)
    info = []
    for (c0, c1), cov in pencils.items():
        d = (u1 - poly_eval_vec(list(c1), st.xs, q)) % q
        e = (u0 - poly_eval_vec(list(c0), st.xs, q)) % q
        z = int(((d == 0) & (e == 0)).sum())
        supp = int((d != 0).sum())
        cap = supp // (a - z) if a > z else q
        assert len(cov) <= cap, \
            f"pencil cap VIOLATED: |cov|={len(cov)} > cap={cap} (z={z}, supp={supp})"
        info.append(dict(c0=c0, c1=c1, cov=frozenset(cov), z=z, supp=supp,
                         cap=cap))
    # exact min cover (bad sets here are <= ~14, pencil families small)
    universe = frozenset(gam_list)
    covsets = sorted({p['cov'] for p in info}, key=lambda s: -len(s))
    best = None
    import itertools as it
    for r in range(1, min(len(covsets), 8) + 1):
        for combo in it.combinations(covsets, r):
            un = frozenset().union(*combo)
            if un == universe:
                best = combo
                break
        if best is not None:
            break
    return dict(n_bad=len(gam_list), n_pencils=len(pencils),
                n_distinct_covs=len(covsets),
                min_cover=len(best) if best else None,
                max_single=max(len(s) for s in covsets),
                caps=sorted([(len(p['cov']), p['cap'], p['z'], p['supp'])
                             for p in info], reverse=True)[:12],
                bad_gammas=gam_list)


# ----------------------------------------------------------------------
# one full symmetric-effort experiment
# ----------------------------------------------------------------------
def build_dirs(st, rng, pairs, cvals):
    dirs = []
    for j in range(st.n):
        dirs.append((f"mono_j{j}", "monomial", st.mono(j)))
    for (i, j) in pairs:
        mi, mj = st.mono(i), st.mono(j)
        for c in cvals:
            dirs.append((f"sp2_{i}_{j}_c{c}", "spread2", (mi + c * mj) % st.q))
    return dirs


def run_setting(n, k, q, a_list, blind_as, pairs, rng, budget, dissect_at=()):
    t0 = time.time()
    st = Setting(n, k, q)
    print(f"\n{'='*78}\nSETTING n={n} k={k} rho={k}/{n} q={q} v2(q-1)={v2(q-1)} "
          f"(q>=n^4: {q >= n**4})  C(n,k)={st.P}", flush=True)
    print(f"levels a={a_list} (direction-blind flagged: {blind_as}); "
          f"spread pairs (gap n/2={n//2} excluded): {pairs}", flush=True)
    cvals = [1, int(rng.integers(3, q))]
    dirs = build_dirs(st, rng, pairs, cvals)
    U_shared = shared_u0_pool(st, rng, budget['n_far'], budget['n_piece'],
                              budget['n_rand_u0'])
    n_mono = sum(1 for d in dirs if d[1] == 'monomial')
    print(f"{len(dirs)} directions ({n_mono} monomial, {len(dirs)-n_mono} "
          f"spread2), shared pool {len(U_shared)}, EQUAL budget/direction: "
          f"{budget['nchain']}x{len(a_list)} chains + {budget['restarts']} "
          f"restarts x <= {budget['rounds']} rounds x ({budget['batch']} mut + "
          f"{budget['rchain']} chains)", flush=True)

    rec = {}
    for di, (lab, cls, u1) in enumerate(dirs):
        pack = st.pack(u1)
        elig = [a for a in a_list if pack['agreemax'] < a]
        if not elig:
            rec[lab] = dict(cls=cls, agreemax=pack['agreemax'], pack=pack)
            continue
        res = symmetric_search(st, pack, elig, U_shared, rng, budget)
        r = dict(cls=cls, agreemax=pack['agreemax'], pack=pack)
        r.update(res)
        rec[lab] = r
        if (di + 1) % 10 == 0:
            print(f"  ..{di+1}/{len(dirs)} dirs [{time.time()-t0:.0f}s]",
                  flush=True)

    results = {}
    for a in a_list:
        elig_m = [(lab, r) for lab, r in rec.items()
                  if r['cls'] == 'monomial' and r['agreemax'] < a]
        elig_s = [(lab, r) for lab, r in rec.items()
                  if r['cls'] == 'spread2' and r['agreemax'] < a]
        elig_m.sort(key=lambda x: -x[1][a][0])
        elig_s.sort(key=lambda x: -x[1][a][0])
        bm_lab, bm = elig_m[0][0], int(elig_m[0][1][a][0])
        bs_lab, bs = elig_s[0][0], int(elig_s[0][1][a][0])
        # brute-verify both decision-critical witnesses
        for lab, r in ((bm_lab, rec[bm_lab]), (bs_lab, rec[bs_lab])):
            cf, u0w = r[a]
            br = st.brute_count(u0w, r['pack']['u1'], a,
                                gchunk=budget['gchunk'])
            assert br == cf, f"witness MISMATCH {lab} a={a}: {cf} vs {br}"
        ratio = bs / bm
        tag = 'DIRECTION-BLIND' if a in blind_as else (
            'BOUNDARY' if abs((1 - a / n) - (1 - (k / n) ** 0.5)) < 1e-9
            else 'INTERIOR')
        print(f"\n--- a={a} delta={1-a/n:.4f} [{tag}] q={q} ---", flush=True)
        print("  monomial worst counts: "
              + " ".join(f"{lab}={int(r[a][0])}" for lab, r in elig_m),
              flush=True)
        print("  spread2 top-8 worst counts: "
              + " ".join(f"{lab}={int(r[a][0])}" for lab, r in elig_s[:8]),
              flush=True)
        print(f"  >>> best_mono {bm_lab}={bm}  best_spread {bs_lab}={bs}  "
              f"RATIO={ratio:.4f}  [witnesses brute-verified]", flush=True)
        results[a] = dict(best_mono=(bm_lab, bm), best_spread=(bs_lab, bs),
                          ratio=ratio, tag=tag)
        if a in dissect_at:
            for who, lab in (('spread', bs_lab), ('mono', bm_lab)):
                r = rec[lab]
                cnt, u0w = r[a]
                bw = bad_gamma_witnesses(st, u0w, r['pack'], a)
                assert len(bw) == cnt, f"dissect count {len(bw)} != {cnt}"
                pc = pencil_cover(st, u0w, r['pack']['u1'], a, bw)
                print(f"  [dissect {who} {lab} a={a} count={cnt}] "
                      f"n_pencils={pc['n_pencils']} distinct_covs="
                      f"{pc['n_distinct_covs']} MIN_COVER={pc['min_cover']} "
                      f"max_single_pencil={pc['max_single']}", flush=True)
                print(f"    per-pencil (covered, provable_cap, z, supp) top: "
                      f"{pc['caps']}", flush=True)
                print(f"    bad gammas: {pc['bad_gammas']}", flush=True)
                results[a][f'dissect_{who}'] = pc
    print(f"[setting done in {time.time()-t0:.0f}s]", flush=True)
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--stage', choices=['n8', 'n16k4', 'n16k2', 'all'],
                    default='all')
    args = ap.parse_args()
    rng = np.random.default_rng(46611)
    summary = []

    def antipodal_free_pairs(n, forced, extra, rng):
        allp = [p for p in itertools.combinations(range(n), 2)
                if (p[1] - p[0]) % n != n // 2 and (p[0] - p[1]) % n != n // 2]
        sel = list(forced)
        pool = [p for p in allp if p not in sel]
        idx = rng.choice(len(pool), size=min(extra, len(pool)), replace=False)
        sel += [pool[int(i)] for i in idx]
        return sel

    if args.stage in ('n8', 'all'):
        n, k = 8, 2
        q1, q2 = primes_two_v2_classes(n, n ** 4)
        print(f"n=8 primes: {q1} (v2={v2(q1-1)}), {q2} (v2={v2(q2-1)})",
              flush=True)
        pairs = [p for p in itertools.combinations(range(8), 2)
                 if (p[1] - p[0]) % 8 != 4]
        bud = dict(nchain=12, restarts=3, rounds=6, batch=192, rchain=64,
                   stall=2, chunk=512, gchunk=8192,
                   n_far=40, n_piece=50, n_rand_u0=1500)
        for q in (q1, q2):
            res = run_setting(8, 2, q, a_list=[3, 4], blind_as=[3],
                              pairs=pairs, rng=rng, budget=bud,
                              dissect_at=(4,))
            summary.append(('n8k2', q, res))

    if args.stage in ('n16k4', 'all'):
        n, k = 16, 4
        for q in (65617, 65633):
            assert is_prime(q) and q % n == 1 and q >= n ** 4
            pairs = antipodal_free_pairs(
                16, [(4, 14), (7, 13), (4, 8)], 9,
                np.random.default_rng(11))
            bud = dict(nchain=8, restarts=2, rounds=4, batch=96, rchain=32,
                       stall=2, chunk=96, gchunk=512,
                       n_far=12, n_piece=20, n_rand_u0=120)
            res = run_setting(16, 4, q, a_list=[6, 7], blind_as=[],
                              pairs=pairs, rng=rng, budget=bud,
                              dissect_at=(7,))
            summary.append(('n16k4', q, res))

    if args.stage in ('n16k2', 'all'):
        n, k = 16, 2
        for q in (65617, 65633):
            pairs = antipodal_free_pairs(
                16, [(4, 14), (7, 13), (4, 8)], 9,
                np.random.default_rng(13))
            bud = dict(nchain=10, restarts=3, rounds=5, batch=128, rchain=48,
                       stall=2, chunk=256, gchunk=2048,
                       n_far=20, n_piece=30, n_rand_u0=400)
            res = run_setting(16, 2, q, a_list=[4, 5], blind_as=[],
                              pairs=pairs, rng=rng, budget=bud,
                              dissect_at=(5,))
            summary.append(('n16k2', q, res))

    print("\n" + "=" * 78)
    print("SPREAD-EXCESS SUMMARY (symmetric effort; all values exact "
          "lower bounds; decision witnesses brute-verified):", flush=True)
    mx = 0.0
    for key, q, res in summary:
        for a, v in res.items():
            print(f"  {key} q={q} a={a} [{v['tag']}]: mono={v['best_mono']} "
                  f"spread={v['best_spread']} RATIO={v['ratio']:.4f}",
                  flush=True)
            if v['tag'] != 'DIRECTION-BLIND':
                mx = max(mx, v['ratio'])
    print(f"\nMAX RATIO over honest (non-blind) levels: {mx:.4f} "
          f"(law claims <= 2)", flush=True)


if __name__ == '__main__':
    main()
