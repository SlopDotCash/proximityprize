#!/usr/bin/env python3
"""probe_g101f_monomial_baseline.py -- #466 lane G101F: the monomial-baseline
growth law at Johnson-boundary cells (successor to G92).

QUESTION (G92 residue): near the Johnson boundary (k+2 <= a, a^2 <= n*k,
a ~ sqrt(nk)), what is the TRUE growth of
    worst_mono(n,k,a) := max over a-far monomial directions x^j of
                         worstBad (the worst-offset bad-scalar count)?
G92's search data suggested collapse to O(1) (6 at n=32,k=4,a=11), which would
kill SpreadExcessLaw C for every C via the floor n-(a-1).

HEADLINE MECHANISM (this lane): the *generalized pencil floor*.  For ANY
codeword h agreeing with the direction u1 on exactly z < a points, splitting
the n-z off-agreement points into B = (n-z)//(a-z) blocks and giving block r
its own scalar gamma_r yields B distinct bad scalars for one explicit u0:
    worstBad(u1, a) >= (n - z) // (a - z).
For a monomial x^j over the smooth domain mu_n, h = x^d (d < k) agrees with
x^j exactly on the kernel-coset {x : x^(j-d) = 1} of size z = gcd(j-d, n).
So for j in [k, a) (far by pure degree count) the baseline is CERTIFIED
    worst_mono >= max_{k<=j<a, d<k} (n - gcd(j-d,n)) // (a - gcd(j-d,n)).
At fixed k this grows like ~ n/a ~ sqrt(n/k): the O(1)-collapse premise is
FALSE.  In particular at G92's kill cell (n=32,k=4,a=11): j=8,d=0 gives
z=8, B = 24//3 = 8 > 7, so the planned "certify monoBaseline <= 7" step of
the C=3 refutation is IMPOSSIBLE, and the in-evidence ratio drops to
23/8 = 2.875 < 3 (until the spread side is pushed past 24).

Stages:
  stage1 (seconds): certified pencil table, n in {16,...,256}, k in {2,4},
    all window levels a, 1-2 primes; every claimed bad gamma is verified by
    exhibiting the witness codeword and counting agreement >= a directly.
  stage2 (search): symmetric-effort search (G92 engine) WITH pencil seeds on
    representative far monomials at feasible cells, to measure how far above
    the pencil floor the true baseline sits; witness page diagnostics.
    Also a spread re-search at the G92 kill cell (does spread reach >= 25?).
  stage3 (exact): n=8, k=2, q=17, a=4 (a^2 = nk boundary): EXACT worstBad by
    exhausting u0 over coset representatives modulo span{1, x, u1}
    (bad-scalar sets are invariant under u0 += codeword and u0 += beta*u1),
    for all far monomials and all far c=1 spreads.

Conventions identical to probe_g92_spread_excess_c3.py / _SpreadExcessLaw.lean.
"""
import argparse
import itertools
import math
import os
import sys
import time

os.environ.setdefault("OMP_NUM_THREADS", "4")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "4")
os.environ.setdefault("MKL_NUM_THREADS", "4")

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import probe_g92_spread_excess_c3 as g92


# --------------------------------------------------------------------------
# lightweight domain (no interpolant table) for pencil certification
# --------------------------------------------------------------------------
def find_omega(n: int, q: int) -> int:
    """Element of exact order n in F_q^* (n a power of two, n | q-1)."""
    assert (q - 1) % n == 0
    for g in range(2, q):
        x = pow(g, (q - 1) // n, q)
        if n == 1 or pow(x, n // 2, q) != 1:
            return x
    raise RuntimeError("no omega")


def domain(n: int, q: int) -> np.ndarray:
    om = find_omega(n, q)
    xs = np.array([pow(om, l, q) for l in range(n)], dtype=np.int64)
    assert len(set(xs.tolist())) == n
    return xs


def window_levels(n, k):
    return [a for a in range(k + 2, n + 1) if a * a <= n * k]


def pencil_construct_verify(n, k, q, a, j, d, xs):
    """Build the pencil u0 for direction x^j with core codeword h = x^d and
    verify every claimed bad gamma by explicit witness. Returns certified B."""
    assert k <= j < a and 0 <= d < k and d < j
    u1 = np.array([pow(int(x), j, q) for x in xs], dtype=np.int64)
    h = np.array([pow(int(x), d, q) for x in xs], dtype=np.int64)
    Z = [l for l in range(n) if pow(int(xs[l]), j - d, q) == 1]
    z = len(Z)
    assert z == math.gcd(j - d, n), (z, math.gcd(j - d, n))
    assert z < a
    B = (n - z) // (a - z)
    if B == 0:
        return 0, None
    offZ = [l for l in range(n) if l not in Z]
    gammas = list(range(1, B + 1))
    assert B <= q - 1
    u0 = h.copy()
    for r in range(B):
        blk = offZ[r * (a - z):(r + 1) * (a - z)]
        for l in blk:
            u0[l] = (h[l] - gammas[r] * (u1[l] - h[l])) % q
    # verify each gamma with its explicit witness codeword (1+gamma)*x^d
    for r in range(B):
        c = ((1 + gammas[r]) * h) % q
        w = (u0 + gammas[r] * u1) % q
        agree = int((c == w).sum())
        assert agree >= a, (n, k, q, a, j, d, gammas[r], agree)
    # farness of x^j at level a is analytic: a deg<k poly agrees with x^j on
    # <= j < a points (j >= k), cf. farDirection_monoDir.
    return B, u0


def best_pencil(n, k, a):
    best = (0, None, None)
    for j in range(k, a):
        for d in range(0, min(k, j)):
            z = math.gcd(j - d, n)
            if z >= a:
                continue
            B = (n - z) // (a - z)
            if B > best[0]:
                best = (B, j, d)
    return best


def stage1(primes_per_n=2):
    print("=" * 78)
    print("[STAGE 1] certified pencil floors: worst_mono >= (n-z)//(a-z), "
          "z = gcd(j-d,n)")
    print(f"{'n':>4} {'k':>2} {'q':>9} {'a':>3} {'j':>3} {'d':>2} {'z':>3} "
          f"{'B=cert':>6} {'floor':>6} {'floor/B':>8}  note")
    rows = []
    for n in (16, 32, 64, 128, 256):
        qs = g92.primes_1_mod(n, max(n * n, 1 << 16), primes_per_n)
        for k in (2, 4):
            for qi, q in enumerate(qs):
                xs = domain(n, q)
                for a in window_levels(n, k):
                    B, j, d = best_pencil(n, k, a)
                    if j is None:
                        continue
                    Bv, _ = pencil_construct_verify(n, k, q, a, j, d, xs)
                    assert Bv == B
                    floor = n - (a - 1)
                    boundary = "BOUNDARY" if (a + 1) ** 2 > n * k else ""
                    rows.append(dict(n=n, k=k, q=q, a=a, j=j, d=d,
                                     z=math.gcd(j - d, n), B=B, floor=floor))
                    if qi == 0:  # print once per (n,k,a); certified at all qs
                        print(f"{n:>4} {k:>2} {q:>9} {a:>3} {j:>3} {d:>2} "
                              f"{math.gcd(j - d, n):>3} {B:>6} {floor:>6} "
                              f"{floor / B:>8.2f}  {boundary}", flush=True)
    # growth fit at the boundary a* = floor(sqrt(nk))
    print("\n[STAGE 1 growth at a* = floor(sqrt(nk))] certified B vs n:")
    for k in (2, 4):
        pts = []
        for n in (16, 32, 64, 128, 256):
            astar = int(math.isqrt(n * k))
            got = [r for r in rows if r["n"] == n and r["k"] == k
                   and r["a"] == astar]
            if got:
                pts.append((n, got[0]["B"], got[0]["floor"]))
        s = ", ".join(f"n={n}: B={B} (floor {f}, f/B={f/B:.2f})"
                      for n, B, f in pts)
        print(f"  k={k}: {s}")
        if len(pts) >= 2:
            (n0, B0, _), (n1, B1, _) = pts[0], pts[-1]
            theta = math.log(B1 / B0) / math.log(n1 / n0)
            print(f"  k={k}: fitted theta (B ~ n^theta, endpoints) = "
                  f"{theta:.3f}")
    return rows


# --------------------------------------------------------------------------
# stage 2: search with pencil seeds
# --------------------------------------------------------------------------
def pencil_seeds_for(amb, j, a):
    """All single-pencil u0 constructions for direction x^j (every d < k and
    every core coset value), as search seeds."""
    n, k, q, xs = amb.n, amb.k, amb.q, amb.xs
    u1 = amb.mono(j)
    seeds = []
    for d in range(0, min(k, j)):
        z = math.gcd(j - d, n)
        if z >= a:
            continue
        # cosets of the kernel: pick core where x^(j-d) = v, v in image
        image = sorted(set(pow(int(x), j - d, q) for x in xs))
        for v in image[:3]:
            h = np.array([v * pow(int(x), d, q) % q for x in xs],
                         dtype=np.int64)
            Z = [l for l in range(n) if h[l] == u1[l]]
            if not (0 < len(Z) < a):
                continue
            zz = len(Z)
            B = (n - zz) // (a - zz)
            if B == 0:
                continue
            offZ = [l for l in range(n) if l not in Z]
            u0 = h.copy()
            for r in range(B):
                blk = offZ[r * (a - zz):(r + 1) * (a - zz)]
                for l in blk:
                    u0[l] = (h[l] - (r + 1) * (u1[l] - h[l])) % q
            seeds.append(u0 % q)
    return seeds


def search_worst_seeded(amb, pk, a, rng, budget, extra_seeds):
    """g92.search_worst with extra seeds injected into the start pool."""
    q, n = amb.q, amb.n
    seeds = g92.structural_seeds(amb, pk, a, rng)
    pool = [np.zeros(n, dtype=np.int64)]
    pool += [amb.mono(j) for j in range(n)]
    pool += seeds + list(extra_seeds)
    pool += [g92.chain_seed(amb, pk["u1"], a, rng)
             for _ in range(budget["chains"])]
    pool += [g92.piecewise_seed(amb, rng) for _ in range(budget["piecewise"])]
    pool += [rng.integers(0, q, size=n).astype(np.int64)
             for _ in range(budget["randoms"])]
    U = np.array(pool)
    cnt = amb.fast_counts(U, pk, a)
    order = np.argsort(-cnt)
    best_c, best_u = int(cnt[order[0]]), U[order[0]].copy()
    starts = [U[i].copy() for i in order[: budget["restarts"]]]
    for su in starts:
        cur_u = su
        cur_c = int(amb.fast_counts(cur_u[None, :], pk, a)[0])
        stall = 0
        for _ in range(budget["rounds"]):
            cands = [cur_u]
            for _ in range(budget["mutations"]):
                m = cur_u.copy()
                for _ in range(int(rng.integers(1, 3))):
                    m[int(rng.integers(n))] = int(rng.integers(q))
                cands.append(m)
            for _ in range(budget["freshchains"]):
                cands.append(g92.chain_seed(amb, pk["u1"], a, rng))
            cc = amb.fast_counts(np.array(cands), pk, a)
            i = int(cc.argmax())
            if int(cc[i]) > cur_c:
                cur_c, cur_u = int(cc[i]), cands[i].copy()
                stall = 0
            else:
                stall += 1
                if stall >= budget["stall"]:
                    break
        if cur_c > best_c:
            best_c, best_u = cur_c, cur_u.copy()
    return best_c, best_u


def page_diagnostics(amb, u0, u1, a, pk, max_gammas=12):
    """For a witness u0: list bad gammas and their witness agreement sets."""
    bl = amb.fast_bad_list(u0, pk, a)
    if bl is None:
        print("    (all gammas bad)")
        return
    print(f"    bad gammas ({len(bl)}): sample {bl[:max_gammas]}")
    q = amb.q
    sets = []
    for gam in bl[:max_gammas]:
        w = (u0 + gam * u1) % q
        V = np.einsum("ptl,gpt->gpl", amb.L, w[None, amb.Tidx]) % q
        agr = (V[0] == w[None, :]).sum(axis=1)
        pi = int(agr.argmax())
        S = tuple(np.nonzero(V[0][pi] == w)[0].tolist())
        sets.append(set(S))
        print(f"      gamma={gam}: best witness agrees on {int(agr.max())} "
              f"coords {sorted(S)}")
    if len(sets) >= 2:
        ov = [len(sets[i] & sets[jj]) for i in range(len(sets))
              for jj in range(i + 1, len(sets))]
        print(f"    pairwise witness-set overlaps: min={min(ov)} "
              f"max={max(ov)} mean={sum(ov)/len(ov):.2f}")


def stage2():
    print("=" * 78)
    print("[STAGE 2] pencil-seeded symmetric search above the certified floor")
    rng = np.random.default_rng(4669101)
    budget = dict(chains=60, piecewise=20, randoms=100, restarts=3,
                  rounds=10, mutations=96, blockmoves=0, freshchains=12,
                  stall=3)
    budget_heavy = dict(chains=40, piecewise=20, randoms=80, restarts=2,
                        rounds=6, mutations=64, blockmoves=0, freshchains=8,
                        stall=2)
    cells = [
        # (n, k, q-count, a-list, j-list, budget)
        (16, 4, 1, [6, 7, 8], None, budget),
        (16, 2, 1, [4, 5], None, budget),
        (32, 4, 1, [10, 11], [8, 9, 4, 12], budget_heavy),
        (32, 2, 1, [7, 8], [4, 8, 2, 6], budget),
        (64, 2, 1, [9, 10, 11], [8, 4, 2, 6, 9], budget),
    ]
    results = []
    for (n, k, nq, alist, jlist, bud) in cells:
        qs = g92.primes_1_mod(n, max(n * n, 1 << 16), nq)
        for q in qs:
            t0 = time.time()
            amb = g92.Ambient(n, k, q)
            for a in alist:
                if a not in window_levels(n, k):
                    continue
                js = jlist if jlist else [j for j in range(k, a)]
                pb, pj, pd = best_pencil(n, k, a)
                per = {}
                for j in js:
                    if j >= a:  # keep the analytic farness guarantee
                        continue
                    pk = amb.pack(amb.mono(j))
                    if pk["agreemax"] >= a:
                        continue
                    seeds = pencil_seeds_for(amb, j, a)
                    cbest, w = search_worst_seeded(amb, pk, a, rng, bud,
                                                   seeds)
                    per[j] = (cbest, w)
                if not per:
                    continue
                jm = max(per, key=lambda t: per[t][0])
                mono_lb = per[jm][0]
                print(f"[CELL n={n} k={k} q={q} a={a}] pencil-cert={pb} "
                      f"(j={pj},d={pd}); search-lb per j: "
                      f"{ {j: v[0] for j, v in per.items()} } "
                      f"=> mono_lb={mono_lb} at x^{jm} "
                      f"[{time.time()-t0:.0f}s]", flush=True)
                pkm = amb.pack(amb.mono(jm))
                page_diagnostics(amb, per[jm][1], amb.mono(jm), a, pkm)
                results.append(dict(n=n, k=k, q=q, a=a, pencil=pb,
                                    search=mono_lb, best=max(pb, mono_lb),
                                    floor=n - (a - 1)))
    print("\n[STAGE 2 TABLE] certified pencil vs search lb (mono only)")
    print(f"{'n':>3} {'k':>2} {'q':>9} {'a':>3} {'pencil':>6} {'search':>6} "
          f"{'best':>5} {'floor':>5} {'floor/best':>10}")
    for r in results:
        print(f"{r['n']:>3} {r['k']:>2} {r['q']:>9} {r['a']:>3} "
              f"{r['pencil']:>6} {r['search']:>6} {r['best']:>5} "
              f"{r['floor']:>5} {r['floor']/r['best']:>10.2f}")
    return results


def stage2s():
    """Spread re-search at the G92 kill cell: can worst_spread reach >= 25
    (needed to keep C=3 refuted once mono >= 8 is certified)?"""
    print("=" * 78)
    print("[STAGE 2s] spread re-search at n=32 k=4 a=11 (target >= 25)")
    rng = np.random.default_rng(4669102)
    budget = dict(chains=60, piecewise=20, randoms=100, restarts=3,
                  rounds=10, mutations=96, blockmoves=0, freshchains=12,
                  stall=3)
    q = g92.primes_1_mod(32, 32 ** 4, 1)[0]
    amb = g92.Ambient(32, 4, q)
    a = 11
    best = (0, None, None)
    for (j, jp) in [(8, 10), (8, 26), (9, 11), (10, 24)]:
        u1 = (amb.mono(j) + amb.mono(jp)) % q
        pk = amb.pack(u1)
        if pk["agreemax"] >= a:
            continue
        cbest, w = search_worst_seeded(amb, pk, a, rng, budget, [])
        print(f"  x^{j}+x^{jp} (agreemax {pk['agreemax']}): {cbest}",
              flush=True)
        if cbest > best[0]:
            best = (cbest, (j, jp), w)
    print(f"  [spread re-search] best = {best[0]} at {best[1]} "
          f"(3*8 = 24 is the new bar; floor = 22)")


# --------------------------------------------------------------------------
# stage 3: exact worstBad at n=8, k=2, q=17, a=4 (a^2 = nk)
# --------------------------------------------------------------------------
def rref_pivots(rows, q):
    M = np.array(rows, dtype=np.int64) % q
    R, C = M.shape
    piv = []
    r = 0
    for c in range(C):
        pr = None
        for rr in range(r, R):
            if M[rr, c] % q:
                pr = rr
                break
        if pr is None:
            continue
        M[[r, pr]] = M[[pr, r]]
        M[r] = M[r] * pow(int(M[r, c]), q - 2, q) % q
        for rr in range(R):
            if rr != r and M[rr, c] % q:
                M[rr] = (M[rr] - M[rr, c] * M[r]) % q
        piv.append(c)
        r += 1
        if r == R:
            break
    return piv, r


def exact_worstbad(amb, u1, a, label):
    n, k, q = amb.n, amb.k, amb.q
    pk = amb.pack(u1)
    if pk["agreemax"] >= a:
        print(f"  {label}: NOT {a}-far (agreemax {pk['agreemax']}) -- skip")
        return None
    rows = [amb.mono(dd) for dd in range(k)] + [u1]
    piv, rank = rref_pivots(rows, q)
    assert rank == k + 1, (label, rank)
    free = [c for c in range(n) if c not in piv]
    nfree = len(free)
    total = q ** nfree
    best_c, best_u = -1, None
    chunk = 8192
    grid = np.zeros((chunk, n), dtype=np.int64)
    t0 = time.time()
    idx = 0
    buf = []
    for vals in itertools.product(range(q), repeat=nfree):
        buf.append(vals)
        if len(buf) == chunk or idx + len(buf) == total:
            U = np.zeros((len(buf), n), dtype=np.int64)
            U[:, free] = np.array(buf, dtype=np.int64)
            cnt = amb.fast_counts(U, pk, a)
            i = int(cnt.argmax())
            if int(cnt[i]) > best_c:
                best_c, best_u = int(cnt[i]), U[i].copy()
            idx += len(buf)
            buf = []
    # exactness: every u0 is equivalent mod span{1..x^(k-1), u1} to exactly
    # one representative with zeros at the pivot coordinates, and the
    # bad-scalar COUNT is invariant under u0 += codeword (witness shifts) and
    # u0 += beta*u1 (gamma reparametrization).
    bs = amb.brute_count(best_u, u1, a)
    assert bs == best_c
    print(f"  {label}: EXACT worstBad = {best_c}  "
          f"(reps {total}, {time.time()-t0:.0f}s; argmax brute-verified)")
    return best_c


def stage3():
    print("=" * 78)
    print("[STAGE 3] EXACT worstBad at n=8 k=2 q=17 a=4 (a^2 = nk boundary), "
          "coset-exhaustive")
    q, n, k, a = 17, 8, 2, 4
    amb = g92.Ambient(n, k, q)
    monos = {}
    for j in range(k, n):
        v = exact_worstbad(amb, amb.mono(j), a, f"x^{j}")
        if v is not None:
            monos[j] = v
    print(f"  exact mono values: {monos}; monoBaseline(exact,far-j-only) = "
          f"{max(monos.values()) if monos else None}")
    pb, pj, pd = best_pencil(n, k, a)
    print(f"  pencil-cert at this cell: {pb} (j={pj}, d={pd})")
    spreads = {}
    for (j, jp) in itertools.combinations(range(k, n), 2):
        u1 = (amb.mono(j) + amb.mono(jp)) % q
        v = exact_worstbad(amb, u1, a, f"x^{j}+x^{jp}")
        if v is not None:
            spreads[(j, jp)] = v
    if spreads and monos:
        sm = max(spreads.values())
        mm = max(monos.values())
        print(f"  exact spread max (c=1 class) = {sm}; EXACT ratio at this "
              f"boundary cell = {sm}/{mm} = {sm/mm:.3f}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", default="all",
                    choices=["all", "s1", "s2", "s2s", "s3"])
    args = ap.parse_args()
    t0 = time.time()
    rng = np.random.default_rng(46692)
    g92.self_test(rng)
    if args.stage in ("all", "s1"):
        stage1()
    if args.stage in ("all", "s3"):
        stage3()
    if args.stage in ("all", "s2"):
        stage2()
    if args.stage in ("all", "s2s"):
        stage2s()
    print(f"\n[G101F total {time.time()-t0:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
