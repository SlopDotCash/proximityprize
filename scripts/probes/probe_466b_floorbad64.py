#!/usr/bin/env python3
"""probe_466b_floorbad64.py — uniform-in-mu floor-bad characterization, rung n=64.

Lane FLOOR64, issue #466 round 2 (dossier v3 Tier-1 item 4).
Output: scripts/probes/_out_466b_floorbad64.txt

OBJECT (dossier v3 par.9; exact scanner source = scripts/probes/floor_scan_exact.c):
  floor-bad(n) contains a split prime p (p = 1 mod n)  iff  some "adjacent 7th-type
  pattern" A is realizable over F_p:
      rank[M_A] == rank[M_A | b_A],
      M_A rows = [x^0 .. x^{n/2-1} | -x^{n/2}]  for x in A,   b_A = x^{3n/4}.
  Pattern: classes cls[c] = { g0^j : j = c (mod 4) } (g0 = generator of mu_n, discrete-log
  classes mod 4), m = n/4, agr_min = m - m/4, agr_maj = m - m/2; pick rotation c0, take
  agr_min-subsets of cls[c0], cls[c0+1] and agr_maj-subsets of cls[c0+2], cls[c0+3].
  Ground truth (validated, #464): floor-bad(16) = {17} (17 -> 160/2304 patterns),
  floor-bad(32) = {97} (full 15,366,400-pattern scans; 193/257/353/449/577/673 good).
  Conjecture under test: floor-bad(64) = {193}  (smallest prime = 1 mod 64).

Q-FORMULATION (proven equivalent; the vectorized engine below):
  realizable(A)
    <=>  exists f (deg < n/2), g with  x^{3n/4} + g x^{n/2} - f(x) = 0 on A     [rank stmt]
    <=>  exists monic q, deg q = D := 3n/4 - |A|, such that h = q * P_A has zero
         coefficients at all degrees m in (n/2, 3n/4), where P_A = prod_{a in A}(x - a).
  (h vanishes on the |A| DISTINCT points of A iff P_A | h; the coefficient shape of h is
  exactly the binder shape.)  Since P_A is monic, the D rows m = |A| .. 3n/4-1 are unit
  lower-triangular in q and determine q UNIQUELY by back-substitution; realizable  <=>
  the residual rows m = n/2+1 .. |A|-1 all vanish.  (n=16: 1 residual; n=32: 3; n=64: 7.)

TOWER-REDUCTION THEOREM (elementary, used to prune the n=64 search):
  If A is closed under x -> -x (exponent j -> j+n/2), then h_even(x) := (h(x)+h(-x))/2
  keeps the binder coefficient shape and still vanishes on A, and h_even = H(x^2) where H
  has the binder shape FOR RUNG n/2 and vanishes on the image pattern (classes and
  adjacency preserved, sizes halved).  Conversely any rung-n/2 witness H lifts.  Hence:
    an antipode-closed pattern at rung n is realizable at p  iff  its image pattern at
    rung n/2 is realizable at p.
  Iterating: patterns that are unions of x^{2^t}-fibers reduce t rungs.  Corollary: ALL
  "pure sub-fiber" structured patterns at n=64 (pair-unions, quarter-coset unions, the
  full-8-coset + sparse-r family) are realizable at p iff p is floor-bad at rung 32 / 16,
  which the lower-rung full scans decide.  New badness at 64 must be antipode-ASYMMETRIC.

SUBCOMMANDS
  selftest              scalar-vs-vectorized engine agreement on random patterns
  validate16            n=16: rank-port (= C scanner) vs q-scalar vs vectorized, full scans
  scan32 <p> [...]      n=32 full 15.37M-pattern vectorized scans (revalidation + new)
  scan16grid            n=16 full scans at all p = 1 mod 16 up to 1601 (incl. mod-64 targets)
  sample64 <p> <N> [strategy] [seed]   n=64 random-pattern search (uniform | nearsym)
  certify64 <p> <c0> <j1,...,j40>      independent rank-formulation check of one pattern

PROBE-REGIME NOTE: the #400 trap (proper subgroups, p >~ n^4, decorrelated directions)
governs CHARACTER-SUM probes.  The floor-bad object is a rank/divisibility scan whose
conjectured law concerns the SMALLEST split primes; small p here is the object itself,
not a regime artifact.  mu_64 is proper in every field used (index >= 3).
"""

import sys, time, itertools, random
from math import comb
import numpy as np

# ---------------------------------------------------------------- basics

def is_prime(m):
    if m < 2: return False
    d = 2
    while d * d <= m:
        if m % d == 0: return False
        d += 1
    return True

def primitive_root(p):
    """Smallest primitive root mod p (matches generator() in floor_scan_exact.c)."""
    m = p - 1
    fac = []
    mm, d = m, 2
    while d * d <= mm:
        if mm % d == 0:
            fac.append(d)
            while mm % d == 0: mm //= d
        d += 1
    if mm > 1: fac.append(mm)
    for h in range(2, p):
        if all(pow(h, m // f, p) != 1 for f in fac):
            return h
    raise ValueError("no generator")

def mu_elems(p, n):
    """(g0, X): g0 = generator of mu_n, X[j] = g0^j.  Same indexing as the C scanner."""
    assert (p - 1) % n == 0 and is_prime(p)
    g0 = pow(primitive_root(p), (p - 1) // n, p)
    X = [pow(g0, j, p) for j in range(n)]
    assert len(set(X)) == n
    return g0, X

def pattern_params(n):
    m = n // 4
    return m, m - m // 4, m - m // 2      # m, agr_min, agr_maj

def classes(n):
    return [[j for j in range(n) if j % 4 == c] for c in range(4)]

# ------------------------------------------- rank formulation (port of floor_scan_exact.c)

def rank_mod(rows, p):
    M = [r[:] for r in rows]
    nr, nc = len(M), len(M[0])
    rank = 0
    for col in range(nc):
        if rank >= nr: break
        piv = next((r for r in range(rank, nr) if M[r][col] % p), None)
        if piv is None: continue
        M[rank], M[piv] = M[piv], M[rank]
        iv = pow(M[rank][col], p - 2, p)
        M[rank] = [(v * iv) % p for v in M[rank]]
        for r in range(nr):
            if r != rank and M[r][col] % p:
                f = M[r][col] % p
                M[r] = [(M[r][c] - f * M[rank][c]) % p for c in range(nc)]
        rank += 1
    return rank

def realizable_rank(p, n, X, A):
    """Direct port of the C scanner's per-pattern test."""
    half, deg34 = n // 2, 3 * n // 4
    rowsM, rowsAug = [], []
    for j in A:
        x = X[j]
        base = [pow(x, k, p) for k in range(half)] + [(p - pow(x, half, p)) % p]
        rowsM.append(base)
        rowsAug.append(base + [pow(x, deg34, p)])
    return rank_mod(rowsM, p) == rank_mod(rowsAug, p)

def patterns_iter(n):
    """All adjacent 7th-type patterns in the C scanner's lex order: (c0, A-exponents)."""
    m, agr_min, agr_maj = pattern_params(n)
    cls = classes(n)
    cmin = list(itertools.combinations(range(m), agr_min))
    cmaj = list(itertools.combinations(range(m), agr_maj))
    for c0 in range(4):
        mn0, mn1, mj0, mj1 = c0, (c0 + 1) % 4, (c0 + 2) % 4, (c0 + 3) % 4
        for a in cmin:
            for b in cmin:
                for d in cmaj:
                    for e in cmaj:
                        A = ([cls[mn0][i] for i in a] + [cls[mn1][i] for i in b]
                             + [cls[mj0][i] for i in d] + [cls[mj1][i] for i in e])
                        yield c0, A

def scan_rank_full(p, n, collect=False):
    _, X = mu_elems(p, n)
    count, total, bad = 0, 0, []
    for c0, A in patterns_iter(n):
        total += 1
        if realizable_rank(p, n, X, A):
            count += 1
            if collect: bad.append((c0, tuple(A)))
    return count, total, bad

# ------------------------------------------------------- q formulation, scalar reference

def poly_from_roots(roots, p):
    P = [1]
    for r in roots:
        Q = [0] * (len(P) + 1)
        for i, c in enumerate(P):
            Q[i + 1] = (Q[i + 1] + c) % p
            Q[i] = (Q[i] - r * c) % p
        P = Q
    return P            # P[k] = coeff of x^k, monic

def realizable_q_scalar(p, n, X, A):
    L = len(A)
    D = 3 * n // 4 - L
    P = poly_from_roots([X[j] for j in A], p)          # deg L
    Pk = lambda k: (P[k] if 0 <= k <= L else 0)
    q = [0] * (D + 1); q[D] = 1
    for m2 in range(3 * n // 4 - 1, L - 1, -1):        # rows m = 3n/4-1 .. L: solve q
        i0 = m2 - L
        s = sum(q[i] * Pk(m2 - i) for i in range(i0 + 1, D + 1)) % p
        q[i0] = (-s) % p
    for m2 in range(n // 2 + 1, L):                    # residual rows
        if sum(q[i] * Pk(m2 - i) for i in range(D + 1)) % p:
            return False
    return True

# ------------------------------------------------------- vectorized engine (batched P)

def realizable_from_P_batch(P, p, n, L):
    """P: (B, L+1) int64 array of monic pattern polys (P[:,L]==1).  Returns bool (B,)."""
    D = 3 * n // 4 - L
    B = P.shape[0]
    q = np.zeros((B, D + 1), dtype=np.int64); q[:, D] = 1
    getP = lambda k: (P[:, k] if 0 <= k <= L else np.zeros(B, dtype=np.int64))
    for m2 in range(3 * n // 4 - 1, L - 1, -1):
        i0 = m2 - L
        s = np.zeros(B, dtype=np.int64)
        for i in range(i0 + 1, D + 1):
            s = (s + q[:, i] * getP(m2 - i)) % p
        q[:, i0] = (-s) % p
    ok = np.ones(B, dtype=bool)
    for m2 in range(n // 2 + 1, L):
        s = np.zeros(B, dtype=np.int64)
        for i in range(D + 1):
            s = (s + q[:, i] * getP(m2 - i)) % p
        ok &= (s == 0)
    return ok

def batch_poly_from_roots(R, p):
    """R: (B, L) int64 roots -> (B, L+1) monic polys mod p."""
    B, L = R.shape
    P = np.zeros((B, L + 1), dtype=np.int64); P[:, 0] = 1
    for t in range(L):
        r = R[:, t:t + 1]
        newP = np.zeros_like(P)
        newP[:, 1:t + 2] = P[:, 0:t + 1]
        newP[:, 0:t + 1] = (newP[:, 0:t + 1] - r * P[:, 0:t + 1]) % p
        P = newP
    return P

def batch_conv(A, B_, p):
    """(N,a),(N,b) -> (N,a+b-1) polynomial products mod p."""
    N, a = A.shape; b = B_.shape[1]
    out = np.zeros((N, a + b - 1), dtype=np.int64)
    for s in range(a):
        out[:, s:s + b] = (out[:, s:s + b] + A[:, s:s + 1] * B_) % p
    return out

def subset_polys(vals, k, p):
    """All C(len(vals),k) subset root-polys: (ncomb, k+1) array + subsets (index tuples)."""
    subs = list(itertools.combinations(range(len(vals)), k))
    R = np.array([[vals[i] for i in s] for s in subs], dtype=np.int64)
    return batch_poly_from_roots(R, p), subs

# ------------------------------------------------------- full vectorized scan (n=16/32)

def scan_full_vec(p, n, collect_limit=2000, chunk_rows=200, verbose=True):
    """Full adjacent-pattern scan via the q-engine, outer-product organized.
    Returns (count, total, bad_list) with bad_list entries (c0, A-exponents)."""
    m, agr_min, agr_maj = pattern_params(n)
    L = 2 * agr_min + 2 * agr_maj
    D = 3 * n // 4 - L
    _, X = mu_elems(p, n)
    cls = classes(n)
    cminN = comb(m, agr_min); cmajN = comb(m, agr_maj)
    total = 4 * cminN * cminN * cmajN * cmajN
    count, bad = 0, []
    kmin = n // 2 + 1 - D
    t0 = time.time()
    for c0 in range(4):
        mn0, mn1, mj0, mj1 = c0, (c0 + 1) % 4, (c0 + 2) % 4, (c0 + 3) % 4
        PA_, subA = subset_polys([X[j] for j in cls[mn0]], agr_min, p)
        PB_, subB = subset_polys([X[j] for j in cls[mn1]], agr_min, p)
        PC_, subC = subset_polys([X[j] for j in cls[mj0]], agr_maj, p)
        PD_, subD = subset_polys([X[j] for j in cls[mj1]], agr_maj, p)
        # all min-pairs / maj-pairs, index = a*cminN+b (C lex order)
        nmin2 = cminN * cminN
        ii = np.repeat(np.arange(cminN), cminN); jj = np.tile(np.arange(cminN), cminN)
        PM = batch_conv(PA_[ii], PB_[jj], p)              # (nmin2, 2*agr_min+1)
        kk = np.repeat(np.arange(cmajN), cmajN); ll = np.tile(np.arange(cmajN), cmajN)
        PJ = batch_conv(PC_[kk], PD_[ll], p)              # (nmaj2, 2*agr_maj+1)
        nmaj2 = PJ.shape[0]
        dM = 2 * agr_min; dJ = 2 * agr_maj
        for lo in range(0, nmin2, chunk_rows):
            hi = min(lo + chunk_rows, nmin2)
            R = hi - lo
            # P_k arrays for k = kmin .. L-1 as (R, nmaj2); P_L = 1 implicit
            Pks = {}
            for k in range(kmin, L):
                acc = np.zeros((R, nmaj2), dtype=np.int64)
                for a2 in range(max(0, k - dJ), min(dM, k) + 1):
                    acc = (acc + PM[lo:hi, a2:a2 + 1] * PJ[:, k - a2][None, :]) % p
                Pks[k] = acc
            # q back-substitution
            q = {D: np.ones((R, nmaj2), dtype=np.int64)}
            for m2 in range(3 * n // 4 - 1, L - 1, -1):
                i0 = m2 - L
                s = np.zeros((R, nmaj2), dtype=np.int64)
                for i in range(i0 + 1, D + 1):
                    k = m2 - i
                    if k == L: s += q[i]
                    elif kmin <= k < L: s = (s + q[i] * Pks[k]) % p
                q[i0] = (-s) % p
            # residuals
            ok = np.ones((R, nmaj2), dtype=bool)
            for m2 in range(n // 2 + 1, L):
                s = np.zeros((R, nmaj2), dtype=np.int64)
                for i in range(D + 1):
                    k = m2 - i
                    if k == L: s += q[i]
                    elif k >= kmin: s = (s + q[i] * Pks[k]) % p
                    # k < kmin cannot occur: k >= n/2+1-D = kmin
                ok &= (s % p == 0)
            c = int(ok.sum())
            count += c
            if c and len(bad) < collect_limit:
                w = np.argwhere(ok)
                for (r, col) in w[:collect_limit - len(bad)]:
                    minidx = lo + int(r); majidx = int(col)
                    a, b = divmod(minidx, cminN); d, e = divmod(majidx, cmajN)
                    A = ([cls[mn0][i] for i in subA[a]] + [cls[mn1][i] for i in subB[b]]
                         + [cls[mj0][i] for i in subC[d]] + [cls[mj1][i] for i in subD[e]])
                    bad.append((c0, tuple(A)))
        if verbose:
            print(f"    [p={p} n={n}] rotation c0={c0} done, cumcount={count}, "
                  f"t={time.time()-t0:.1f}s", flush=True)
    return count, total, bad

# ------------------------------------------------------- n=64 random sampling

def sample64(p, nsamples, strategy="uniform", seed=466, batch=100000, report_every=10):
    n = 64
    m, agr_min, agr_maj = pattern_params(n)          # 16, 12, 8
    L = 40
    _, X = mu_elems(p, n)
    Xa = np.array(X, dtype=np.int64)
    cls = np.array(classes(n), dtype=np.int64)       # (4,16) exponents
    rng = np.random.default_rng(seed)
    tested = 0; hits = []
    t0 = time.time(); it = 0
    while tested < nsamples:
        B = min(batch, nsamples - tested)
        c0 = rng.integers(0, 4, size=B)
        rolesz = [agr_min, agr_min, agr_maj, agr_maj]
        exps = np.zeros((B, L), dtype=np.int64)
        pos = 0
        for ri, sz in enumerate(rolesz):
            cs = (c0 + ri) % 4
            # random sz-subsets of the 16 class members, per sample
            keys = rng.random((B, m))
            order = np.argsort(keys, axis=1)[:, :sz]
            exps[:, pos:pos + sz] = np.take_along_axis(
                cls[cs], order, axis=1)
            pos += sz
        if strategy == "nearsym":
            # symmetric core: force each subset to be a union of antipodal pairs
            # (j and j+32), then apply 1-2 asymmetric swaps.
            exps = make_nearsym(rng, cls, c0, rolesz, m, B)
        R = Xa[exps]                                  # (B, 40) field elements
        P = batch_poly_from_roots(R, p)
        ok = realizable_from_P_batch(P, p, n, L)
        if ok.any():
            for idx in np.nonzero(ok)[0]:
                hits.append((int(c0[idx]), tuple(int(v) for v in exps[idx])))
        tested += B; it += 1
        if it % report_every == 0:
            rate = tested / (time.time() - t0)
            print(f"    [p={p} sample64/{strategy}] tested={tested:,} hits={len(hits)} "
                  f"rate={rate:,.0f}/s", flush=True)
        if hits: break
    return tested, hits

def make_nearsym(rng, cls, c0, rolesz, m, B):
    """Antipode-symmetric core + 1-2 asymmetric single-element swaps."""
    L = sum(rolesz)
    exps = np.zeros((B, L), dtype=np.int64)
    pos = 0
    for ri, sz in enumerate(rolesz):
        cs = (c0 + ri) % 4
        npairs = sz // 2
        # class c members: exponents j = c, c+4, ..., c+60 (16 of them); antipodal pairing
        # j <-> j+32 pairs up index i <-> i+8 in cls row (since cls row = c+4*i).
        keys = rng.random((B, 8))
        pk = np.argsort(keys, axis=1)[:, :npairs]     # chosen pair indices (B, npairs)
        both = np.concatenate([pk, pk + 8], axis=1)   # (B, sz) indices into cls row
        rows = cls[cs]                                # (B, 16) exponents of each class
        exps[:, pos:pos + sz] = np.take_along_axis(rows, both, axis=1)
        pos += sz
    # 1-2 asymmetric swaps: replace one chosen element of a random role by an unchosen one
    nswap = rng.integers(1, 3, size=B)
    for _ in range(2):
        act = nswap > 0
        role = rng.integers(0, 4, size=B)
        offs = np.cumsum([0] + rolesz)
        for ri in range(4):
            selr = act & (role == ri)
            if not selr.any(): continue
            idxs = np.nonzero(selr)[0]
            lo, hi = offs[ri], offs[ri + 1]
            cs = (c0[idxs] + ri) % 4
            drop = rng.integers(lo, hi, size=len(idxs))
            for t, bi in enumerate(idxs):
                cur = set(exps[bi, lo:hi].tolist())
                pool = [v for v in cls[cs[t]].tolist() if v not in cur]
                exps[bi, drop[t]] = pool[rng.integers(0, len(pool))]
        nswap = nswap - 1
    return exps

# ------------------------------------------------------- subcommands

def cmd_selftest():
    print("== selftest: scalar-q vs rank vs vectorized engine, random patterns ==")
    rng = random.Random(1)
    for (p, n) in [(17, 16), (97, 16), (97, 32), (193, 32), (193, 64), (257, 64)]:
        _, X = mu_elems(p, n)
        m, agr_min, agr_maj = pattern_params(n)
        cl = classes(n)
        trials, agree = 60 if n < 64 else 25, 0
        Rbatch, meta = [], []
        for _ in range(trials):
            c0 = rng.randrange(4)
            A = (rng.sample(cl[c0], agr_min) + rng.sample(cl[(c0+1) % 4], agr_min)
                 + rng.sample(cl[(c0+2) % 4], agr_maj) + rng.sample(cl[(c0+3) % 4], agr_maj))
            vq = realizable_q_scalar(p, n, X, A)
            vr = realizable_rank(p, n, X, A)
            assert vq == vr, f"MISMATCH q-vs-rank p={p} n={n} A={A}"
            Rbatch.append([X[j] for j in A]); meta.append(vq); agree += 1
        P = batch_poly_from_roots(np.array(Rbatch, dtype=np.int64), p)
        vv = realizable_from_P_batch(P, p, n, 2*agr_min + 2*agr_maj)
        assert list(vv) == meta, f"MISMATCH vectorized p={p} n={n}"
        print(f"  p={p:5d} n={n:2d}: {agree} random patterns, all three engines agree")
    print("  SELFTEST PASS")

def cmd_validate16():
    print("== GROUND TRUTH REVALIDATION, n=16 (rank port vs q-scalar vs vectorized) ==")
    print("   expected (floor_scan_exact.c header + dossier): 17 -> 160/2304, others -> 0")
    ps = [17, 97, 113, 193, 241, 257, 337, 353, 401, 433, 449, 577]
    okall = True
    for p in ps:
        c_rank, tot, _ = scan_rank_full(p, 16)
        c_vec, tot2, _ = scan_full_vec(p, 16, verbose=False)
        exp = 160 if p == 17 else 0
        ok = (c_rank == c_vec == exp) and tot == tot2 == 2304
        okall &= ok
        print(f"  n=16 p={p:4d}: rank-port={c_rank:4d}  vectorized={c_vec:4d}  "
              f"total={tot}  expected={exp:4d}  {'OK' if ok else '*** FAIL ***'}", flush=True)
    print(f"  n=16 REVALIDATION: {'PASS — reconstruction matches ground truth' if okall else 'FAIL'}")
    return okall

def cmd_scan32(ps):
    print("== n=32 FULL SCANS (15,366,400 adjacent patterns each), q-engine ==")
    print("   ground truth: 97 BAD; 193/257/353/449/577/673 good (0 realizable)")
    for p in ps:
        if (p - 1) % 32 or not is_prime(p):
            print(f"  skip p={p} (not a split prime for n=32)"); continue
        t0 = time.time()
        count, total, bad = scan_full_vec(p, 32, collect_limit=2000, verbose=False)
        verdict = "BAD" if count else "good"
        print(f"  n=32 p={p:5d}: realizable={count} / {total}  -> {verdict}   "
              f"({time.time()-t0:.0f}s)", flush=True)
        if count:
            # cross-check a few via the independent rank port
            _, X = mu_elems(p, 32)
            chk = all(realizable_rank(p, 32, X, list(A)) for _, A in bad[:5])
            print(f"    first bad pattern (c0={bad[0][0]}): exponents {sorted(bad[0][1])}")
            print(f"    rank-formulation cross-check on first {min(5,len(bad))}: "
                  f"{'CONFIRMED' if chk else '*** FAIL ***'}")
            if len(bad) >= 2:
                sym = sum(1 for _, A in bad if set((j + 16) % 32 for j in A) == set(A))
                print(f"    antipode-closed among collected {len(bad)}: {sym} "
                      f"(tower-reduction predicts 0 unless p is n=16-bad)")

def cmd_scan16grid():
    print("== n=16 full scans at all split primes up to 1601 (incl. every n=64 target) ==")
    ps = [x for x in range(17, 1602, 16) if is_prime(x)]
    badset = []
    for p in ps:
        c, tot, _ = scan_full_vec(p, 16, verbose=False)
        if c: badset.append((p, c))
        print(f"  n=16 p={p:5d}: realizable={c:4d}/{tot} -> {'BAD' if c else 'good'}", flush=True)
    print(f"  n=16 bad primes found: {badset}  (law predicts exactly [(17,160)])")

def cmd_sample64(p, N, strategy, seed):
    n64 = 64
    print(f"== n=64 random-pattern search: p={p}, N={N:,}, strategy={strategy}, seed={seed} ==")
    space = 4 * comb(16, 12) ** 2 * comb(16, 8) ** 2
    print(f"   full pattern space at n=64: {space:,} (~{space:.3e}) — full enumeration infeasible;")
    print(f"   this run covers a fraction {N/space:.3e} (found-bad = certain; not-found = stratum coverage only)")
    tested, hits = sample64(p, N, strategy=strategy, seed=seed)
    if hits:
        c0, A = hits[0]
        print(f"  *** BAD PATTERN FOUND at p={p}, n=64 ***  c0={c0}")
        print(f"      exponents (sorted): {sorted(A)}")
        _, X = mu_elems(p, 64)
        vr = realizable_rank(p, 64, X, list(A))
        vq = realizable_q_scalar(p, 64, X, list(A))
        print(f"      independent checks: rank-formulation={vr}, scalar-q={vq}")
        emit_certificate(p, c0, list(A))
    else:
        print(f"  no bad pattern in {tested:,} sampled patterns at p={p} (strategy={strategy})")
    return hits

def emit_certificate(p, c0, A):
    """Solve for the witness h = x^48 + g x^32 - f and print a machine-checkable certificate."""
    n = 64; L = len(A); D = 3 * n // 4 - L
    _, X = mu_elems(p, n)
    P = poly_from_roots([X[j] for j in A], p)
    Pk = lambda k: (P[k] if 0 <= k <= L else 0)
    q = [0] * (D + 1); q[D] = 1
    for m2 in range(3 * n // 4 - 1, L - 1, -1):
        i0 = m2 - L
        q[i0] = (-sum(q[i] * Pk(m2 - i) for i in range(i0 + 1, D + 1))) % p
    # h = q * P
    h = [0] * (3 * n // 4 + 1)
    for i in range(D + 1):
        for k2 in range(L + 1):
            h[i + k2] = (h[i + k2] + q[i] * P[k2]) % p
    assert h[3 * n // 4] == 1 and all(h[m2] == 0 for m2 in range(n // 2 + 1, 3 * n // 4))
    g = h[n // 2]
    f = [(-h[k]) % p for k in range(n // 2)]      # h = x^48 + g x^32 - f
    xs = [X[j] for j in A]
    for x in xs:
        lhs = (pow(x, 48, p) + g * pow(x, 32, p)) % p
        rhs = sum(f[k] * pow(x, k, p) for k in range(32)) % p
        assert lhs == rhs
    print("  CERTIFICATE (all values mod p):")
    print(f"    p = {p}, n = 64, c0 = {c0}")
    print(f"    g0 (mu_64 generator) = {mu_elems(p,64)[0]}")
    print(f"    exponents A = {sorted(A)}")
    print(f"    points xs = {xs}")
    print(f"    g (x^32 coefficient) = {g}")
    print(f"    f coefficients (deg<32, f[k] = coeff of x^k) = {f}")
    print(f"    identity checked: x^48 + {g}*x^32 = f(x) for all 40 points  [VERIFIED]")

def cmd_certify64(p, c0, A):
    _, X = mu_elems(p, 64)
    vr = realizable_rank(p, 64, X, A)
    vq = realizable_q_scalar(p, 64, X, A)
    print(f"p={p} c0={c0} A={sorted(A)}: rank={vr} q={vq}")
    if vr: emit_certificate(p, c0, A)

def cmd_runbias64(p, N, runlen, seed=97):
    """n=64 sampling in the 'long consecutive run' stratum: pattern contains a random
    length-`runlen` cyclic run of exponents (97's bad orbit rep contains a 10-run out of
    size-20; runlen 20/24 are the scaled analogs).  runlen must be = 0 mod 4."""
    n = 64
    assert runlen % 4 == 0
    percls_run = runlen // 4
    _, X = mu_elems(p, n)
    Xa = np.array(X, dtype=np.int64)
    rng = np.random.default_rng(seed)
    need = [12, 12, 8, 8]
    print(f"== n=64 run-biased sampling p={p}, N={N:,}, runlen={runlen} ==")
    stratum = 64 * comb(16 - percls_run, 12 - percls_run) ** 2 \
                 * comb(16 - percls_run, 8 - percls_run) ** 2
    print(f"   stratum size (runs x completions, per rotation covered by profile): ~{stratum:,}")
    tested = 0; hits = []
    B = 100000
    cls4 = classes(n)
    while tested < N and not hits:
        Bc = min(B, N - tested)
        s = rng.integers(0, 64, size=Bc)
        c0 = rng.integers(0, 4, size=Bc)
        exps = np.zeros((Bc, 40), dtype=np.int64)
        exps[:, :runlen] = (s[:, None] + np.arange(runlen)[None, :]) % 64
        # completion per class
        pos = runlen
        for ri in range(4):
            c = (c0 + ri) % 4
            k = need[ri] - percls_run
            # remaining members of class c not in the run, per sample
            # class members: c, c+4, ..., c+60; run covers percls_run of them
            memb = np.broadcast_to(np.array(cls4[0], dtype=np.int64), (Bc, 16)).copy()
            memb = (memb + c[:, None]) % 64 if isinstance(c, np.ndarray) else (memb + c) % 64
            inrun = ((memb - s[:, None]) % 64) < runlen
            keys = rng.random((Bc, 16)) + inrun * 10.0     # push run members to the end
            order = np.argsort(keys, axis=1)[:, :k]
            exps[:, pos:pos + k] = np.take_along_axis(memb, order, axis=1)
            pos += k
        R = Xa[exps]
        P = batch_poly_from_roots(R, p)
        okv = realizable_from_P_batch(P, p, n, 40)
        tested += Bc
        if okv.any():
            for idx in np.nonzero(okv)[0]:
                hits.append((int(c0[idx]), tuple(int(v) for v in exps[idx])))
        if tested % 1000000 < B:
            print(f"    tested={tested:,} hits={len(hits)}", flush=True)
    print(f"  run-biased: tested={tested:,}, hits={len(hits)}")
    for c0_, A in hits[:3]:
        print(f"  *** HIT *** c0={c0_} A={sorted(A)}")
        print(f"      rank check: {realizable_rank(p, 64, X, list(A))}")
        emit_certificate(p, int(c0_), list(A))
    return hits

def cmd_bad32(p):
    """Collect ALL bad patterns at (p, n=32), analyze structure, test n=64 lifts."""
    print(f"== n=32 bad-pattern structure analysis at p={p} ==")
    count, total, bad = scan_full_vec(p, 32, collect_limit=100000, verbose=False)
    print(f"  realizable = {count} / {total}")
    if not bad:
        return
    _, X32 = mu_elems(p, 32)
    ok = all(realizable_rank(p, 32, X32, list(A)) for _, A in bad)
    print(f"  rank-formulation cross-check on ALL {len(bad)}: {'CONFIRMED' if ok else '*** FAIL ***'}")
    sets = [frozenset(A) for _, A in bad]
    uniq = set(sets)
    # translation orbit: exponents j -> j+s mod 32 (class rotation, adjacency preserved)
    orbits = []
    seen = set()
    for S in uniq:
        if S in seen: continue
        orb = set(frozenset((j + s) % 32 for j in S) for s in range(32))
        orbrep = orb & uniq
        for T in orbrep: seen.add(T)
        orbits.append((S, len(orbrep), len(orb)))
    print(f"  distinct bad sets: {len(uniq)}; translation orbits: {len(orbits)}")
    for S, inuniq, orbsize in orbits:
        Ss = sorted(S)
        print(f"    orbit rep {Ss}: orbit members that are bad {inuniq}/{orbsize}")
        # negation symmetry j -> j+16; Galois j -> u*j (u odd)
        neg = frozenset((j + 16) % 32 for j in S)
        print(f"      antipode-image bad? {neg in uniq}   (antipode-closed? {neg == S})")
        for u in (3, 5, 7, 9, 15):
            gal = frozenset((u * j) % 32 for j in S)
            print(f"      Galois u={u:2d} image bad? {gal in uniq}")
        # gap structure of the exponent set
        diffs = sorted(((Ss[(i+1) % len(Ss)] - Ss[i]) % 32 for i in range(len(Ss))))
        print(f"      multiset of cyclic gaps: {diffs}")
    return bad

def lift_patterns_64(S32):
    """Candidate lifts of a 20-element exponent set mod 32 to 40-element sets mod 64.
    The doubling lift j -> {2j, 2j+delta} preserves classes iff delta = 0 mod 4... we use
    the antipodal lift {j, j+32} (class-preserving, but provably dead=symmetric) only as
    a base for asymmetric perturbations; and the 'interleave' lifts {2j+c} do NOT preserve
    the class structure, so the honest transfer battery is perturbed antipodal lifts."""
    return [sorted(set(S32) | set((j + 32) for j in S32))]

def cmd_lift64(p, seeds_p=97, nper=400000, seed=17):
    """Near-lift battery at (p, n=64): perturbed antipodal lifts of the (seeds_p, n=32)
    bad patterns.  Perturbations = k asymmetric in-class swaps, k = 1..3."""
    print(f"== n=64 perturbed-lift battery at p={p} (seeds = bad patterns of n=32 at {seeds_p}) ==")
    _, _, bad = scan_full_vec(seeds_p, 32, collect_limit=100000, verbose=False)
    reps = sorted(set(frozenset(A) for _, A in bad), key=lambda s: sorted(s))
    print(f"  seed patterns: {len(reps)} (each lifted antipodally then asymmetrically perturbed)")
    n = 64
    _, X = mu_elems(p, n)
    Xa = np.array(X, dtype=np.int64)
    cls4 = classes(n)
    rng = np.random.default_rng(seed)
    rolesz = [12, 12, 8, 8]
    tested = 0; hits = []
    for S in reps:
        base = sorted(set(S) | set(j + 32 for j in S))          # 40 exponents, symmetric
        # infer c0: class sizes
        bycls = [sorted(j for j in base if j % 4 == c) for c in range(4)]
        sizes = [len(b) for b in bycls]
        c0 = next(c for c in range(4) if sizes[c] == 12 and sizes[(c+1) % 4] == 12)
        B = nper
        exps = np.zeros((B, 40), dtype=np.int64)
        pos = 0
        for ri in range(4):
            c = (c0 + ri) % 4
            exps[:, pos:pos+rolesz[ri]] = np.array(bycls[c], dtype=np.int64)[None, :]
            pos += rolesz[ri]
        # k in {1,2,3} random in-class swaps per sample
        nsw = rng.integers(1, 4, size=B)
        offs = np.cumsum([0] + rolesz)
        for it in range(3):
            act = nsw > it
            role = rng.integers(0, 4, size=B)
            for ri in range(4):
                idxs = np.nonzero(act & (role == ri))[0]
                if len(idxs) == 0: continue
                lo, hi = offs[ri], offs[ri+1]
                c = (c0 + ri) % 4
                members = cls4[c]
                drop = rng.integers(lo, hi, size=len(idxs))
                for t, bi in enumerate(idxs):
                    cur = set(exps[bi, lo:hi].tolist())
                    pool = [v for v in members if v not in cur]
                    exps[bi, drop[t]] = pool[rng.integers(0, len(pool))]
        R = Xa[exps]
        P = batch_poly_from_roots(R, p)
        okv = realizable_from_P_batch(P, p, n, 40)
        tested += B
        if okv.any():
            for idx in np.nonzero(okv)[0]:
                hits.append((c0, tuple(int(v) for v in exps[idx])))
            break
        print(f"    seed {sorted(S)[:6]}...: {B:,} perturbed lifts, 0 hits", flush=True)
    print(f"  total tested {tested:,}; hits: {len(hits)}")
    for c0, A in hits[:3]:
        print(f"  *** HIT *** c0={c0} A={sorted(A)}")
        emit_certificate(p, c0, list(A))
    return hits

# ------------------------------------------------------- main

if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "selftest"
    if cmd == "selftest":
        cmd_selftest()
    elif cmd == "validate16":
        cmd_validate16()
    elif cmd == "scan32":
        cmd_scan32([int(x) for x in sys.argv[2:]])
    elif cmd == "scan16grid":
        cmd_scan16grid()
    elif cmd == "sample64":
        p = int(sys.argv[2]); N = int(sys.argv[3])
        strategy = sys.argv[4] if len(sys.argv) > 4 else "uniform"
        seed = int(sys.argv[5]) if len(sys.argv) > 5 else 466
        cmd_sample64(p, N, strategy, seed)
    elif cmd == "runbias64":
        cmd_runbias64(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    elif cmd == "bad32":
        cmd_bad32(int(sys.argv[2]))
    elif cmd == "lift64":
        p = int(sys.argv[2])
        nper = int(sys.argv[3]) if len(sys.argv) > 3 else 400000
        cmd_lift64(p, nper=nper)
    elif cmd == "certify64":
        p = int(sys.argv[2]); c0 = int(sys.argv[3])
        A = [int(x) for x in sys.argv[4].split(",")]
        cmd_certify64(p, c0, A)
    else:
        print(__doc__)
