#!/usr/bin/env python3
"""probe_g92_spread_excess_c3.py -- #466 lane G92: the bounded spread-excess law
at C = 3, probed across scales.

Question: in the prize window (k+2 <= a, a^2 <= n*k), is
    worst_spread <= 3 * worst_mono ?
per (n, q, a) cell, where worst_* is the worst-offset bad-scalar count
(lineBadScalars sup over u0) of the best 2-Fourier-component direction
x^j + c*x^j' vs the best a-far monomial direction x^j.

History: windowed SumsetExtremal REFUTED (466-r1-windowed-extremal-spread-beats);
C = 2 REFUTED in evidence (466b-p5-referee: >= 21 vs 9 at n=16,k=4,a=7).
Live constant: C = 3.  A measured in-window ratio > 3 kills C = 3.

Conventions (identical to probe_466b_p5_referee.py / Frontier/_SpreadExcessLaw.lean):
  - domain = mu_n in F_q (q prime, n | q-1), RS_k = degree-<k evaluations;
  - badcount(u0, u1, a) = #{gamma : exists c in RS_k with agree(c, u0+gamma*u1) >= a};
  - direction eligible at a  <=>  agreemax(u1) < a  <=>  FarDirection;
  - worst_* values are SEARCH lower bounds (u0-space is q^n); the engine count
    per word is EXACT (self-tested vs full enumeration), and headline winners
    are re-verified (full-gamma brute at n<=16; per-gamma independent
    soundness checks at n=32).
  - search parity: every searched direction (mono or spread) gets the
    identical class-blind driver and budget; structural (agreemax = a-1)
    seeds are given to ANY direction that has them, regardless of class.

Cells: (n=8,k=2,a=4) x {4129,4153,4201};
       (n=16,k=4,a in {6,7,8}) x {65537,65617,65633};
       (n=16,k=2,a in {4,5}) x {65537,65617};
       (n=32,k=4,a in {6,10,11}) x two primes = 1 mod 32, >= 32^4.
       (n=32,k=8 SKIPPED: C(32,8)=10.5M interpolants -- infeasible exactly.)

Also: 3-component census at (n=16,k=4,a=7) for the subadditivity question.
"""
import argparse
import itertools
import os
import sys
import time

os.environ.setdefault("OMP_NUM_THREADS", "4")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "4")
os.environ.setdefault("MKL_NUM_THREADS", "4")

import numpy as np


def is_prime(m: int) -> bool:
    if m < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if m % p == 0:
            return m == p
    d, r = m - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
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


def primes_1_mod(n: int, lo: int, count: int):
    out = []
    q = lo + ((1 - lo) % n)
    while len(out) < count:
        if q >= lo and is_prime(q):
            out.append(q)
        q += n
    return out


def inverse_table(q: int) -> np.ndarray:
    inv = np.zeros(q, dtype=np.int64)
    inv[1] = 1
    for i in range(2, q):
        inv[i] = (q - (q // i) * inv[q % i]) % q
    return inv


class Ambient:
    def __init__(self, n: int, k: int, q: int):
        assert is_prime(q) and (q - 1) % n == 0
        self.n, self.k, self.q = n, k, q
        om = None
        for g in range(2, q):
            x = pow(g, (q - 1) // n, q)
            # exact order n (n a power of two here)
            if pow(x, n // 2, q) != 1:
                om = x
                break
        self.om = om
        xs = np.array([pow(om, l, q) for l in range(n)], dtype=np.int64)
        assert len(set(xs.tolist())) == n
        self.xs = xs
        subsets = list(itertools.combinations(range(n), k))
        self.P = len(subsets)
        self.Tidx = np.array(subsets, dtype=np.int64)
        L = np.zeros((self.P, k, n), dtype=np.int64)
        for pi, T in enumerate(subsets):
            for ti, t in enumerate(T):
                den = 1
                for s in T:
                    if s != t:
                        den = den * int(xs[t] - xs[s]) % q
                deninv = pow(den % q, q - 2, q)
                for l in range(n):
                    num = 1
                    for s in T:
                        if s != t:
                            num = num * int(xs[l] - xs[s]) % q
                    L[pi, ti, l] = num * deninv % q
        self.L = L
        self.inv = inverse_table(q)

    def mono(self, j: int) -> np.ndarray:
        return np.array([pow(int(x), j, self.q) for x in self.xs], dtype=np.int64)

    def codeword(self, coeffs) -> np.ndarray:
        r = np.zeros(self.n, dtype=np.int64)
        for c in reversed(list(coeffs)):
            r = (r * self.xs + c) % self.q
        return r

    def pack(self, u1) -> dict:
        q = self.q
        u1 = np.asarray(u1, dtype=np.int64) % q
        H = np.einsum("ptl,pt->pl", self.L, u1[self.Tidx]) % q
        B = (u1[None, :] - H) % q
        zc = (B == 0).sum(axis=1)
        return dict(u1=u1, B=B, nz=(B != 0), Binv=self.inv[B],
                    agreemax=int(zc.max()), zerocounts=zc)

    def agreemax_only(self, u1) -> int:
        q = self.q
        u1 = np.asarray(u1, dtype=np.int64) % q
        H = np.einsum("ptl,pt->pl", self.L, u1[self.Tidx]) % q
        return int(((u1[None, :] - H) % q == 0).sum(axis=1).max())

    def agree_sets(self, pk) -> list:
        out, seen = [], set()
        am = pk["agreemax"]
        for pi in np.nonzero(pk["zerocounts"] == am)[0]:
            S = tuple(np.nonzero(pk["B"][pi] == 0)[0].tolist())
            if S in seen:
                continue
            seen.add(S)
            h = np.einsum("tl,t->l", self.L[pi], pk["u1"][self.Tidx[pi]]) % self.q
            out.append((S, h))
        return out

    # exact bad-scalar counts, linear-in-gamma engine (see referee probe)
    def fast_counts(self, U, pk, a: int, chunk: int = None) -> np.ndarray:
        q, n, P = self.q, self.n, self.P
        if chunk is None:
            chunk = max(1, min(192, (48 << 20) // (P * n)))
        U = np.asarray(U, dtype=np.int64) % q
        if U.ndim == 1:
            U = U[None, :]
        out = np.zeros(len(U), dtype=np.int64)
        Bz = (~pk["nz"])[None]
        for s in range(0, len(U), chunk):
            Uc = U[s:s + chunk]
            N = len(Uc)
            P0 = np.einsum("ptl,npt->npl", self.L, Uc[:, self.Tidx]) % q
            A = (Uc[:, None, :] - P0) % q
            base = ((A == 0) & Bz).sum(axis=2)
            gam = (q - A) % q * pk["Binv"][None] % q
            gam = np.where(pk["nz"][None], gam, q)
            gs = np.sort(gam, axis=2)
            t = a - base
            full = (t <= 0).any(axis=1)
            qual = np.zeros(gs.shape, dtype=bool)
            tmax = int(t.max()) if t.size else 0
            for tv in range(1, min(max(tmax, 0), n) + 1):
                rows = (t == tv)
                if not rows.any():
                    continue
                if tv == 1:
                    mark = gs < q
                else:
                    mark = np.zeros(gs.shape, dtype=bool)
                    mark[:, :, : n - (tv - 1)] = (
                        (gs[:, :, tv - 1:] == gs[:, :, : n - (tv - 1)])
                        & (gs[:, :, : n - (tv - 1)] < q))
                qual |= rows[:, :, None] & mark
            vals = np.where(qual, gs, q).reshape(N, P * n)
            vals.sort(axis=1)
            c = (vals[:, 0] < q).astype(np.int64)
            c += ((vals[:, 1:] != vals[:, :-1]) & (vals[:, 1:] < q)).sum(axis=1)
            c[full] = q
            out[s:s + N] = c
        return out

    def fast_bad_list(self, u0, pk, a: int):
        """Distinct bad gammas for one word (same math as fast_counts)."""
        q, n = self.q, self.n
        u0 = np.asarray(u0, dtype=np.int64) % q
        P0 = np.einsum("ptl,pt->pl", self.L, u0[self.Tidx]) % q
        A = (u0[None, :] - P0) % q
        base = ((A == 0) & (~pk["nz"])).sum(axis=1)
        if (a - base <= 0).any():
            return None  # every gamma bad
        gam = (q - A) % q * pk["Binv"] % q
        gam = np.where(pk["nz"], gam, q)
        gs = np.sort(gam, axis=1)
        t = a - base
        bad = set()
        for pi in range(self.P):
            tv = int(t[pi])
            row = gs[pi]
            if tv == 1:
                bad.update(int(v) for v in row[row < q])
            else:
                m = (row[tv - 1:] == row[: n - (tv - 1)]) & (row[: n - (tv - 1)] < q)
                bad.update(int(v) for v in row[: n - (tv - 1)][m])
        return sorted(bad)

    def brute_count(self, u0, u1, a: int, gchunk: int = 256, collect: bool = False):
        q = self.q
        u0 = np.asarray(u0, dtype=np.int64) % q
        u1 = np.asarray(u1, dtype=np.int64) % q
        tot, bad = 0, []
        for s in range(0, q, gchunk):
            G = np.arange(s, min(s + gchunk, q), dtype=np.int64)
            W = (u0[None, :] + G[:, None] * u1[None, :]) % q
            V = np.einsum("ptl,gpt->gpl", self.L, W[:, self.Tidx]) % q
            hit = ((V == W[:, None, :]).sum(axis=2) >= a).any(axis=1)
            tot += int(hit.sum())
            if collect and hit.any():
                bad.extend(G[hit].tolist())
        return (tot, bad) if collect else tot

    def check_gamma_bad(self, u0, u1, a: int, g: int) -> bool:
        """Independent soundness check for one gamma (direct interpolation)."""
        q = self.q
        w = (np.asarray(u0, dtype=np.int64) + g * np.asarray(u1, dtype=np.int64)) % q
        V = np.einsum("ptl,pt->pl", self.L, w[self.Tidx]) % q
        return bool(((V == w[None, :]).sum(axis=1) >= a).any())


# --------------------------------------------------------------------------
# seeds and the class-blind search driver (referee protocol)
# --------------------------------------------------------------------------
def chain_seed(amb, u1, a, rng):
    n, k, q, xs = amb.n, amb.k, amb.q, amb.xs
    u1 = np.asarray(u1, dtype=np.int64) % q
    order = rng.permutation(n)
    u0 = np.full(n, -1, dtype=np.int64)
    g = int(rng.integers(1, q))
    cw = amb.codeword([int(rng.integers(q)) for _ in range(k)])
    S = order[:a]
    u0[S] = (cw[S] - g * u1[S]) % q
    assigned = list(S)
    pos = a
    while pos + (a - k) <= n:
        O = rng.choice(np.array(assigned), size=k, replace=False)
        gn = int(rng.integers(1, q))
        while gn == g:
            gn = int(rng.integers(1, q))
        w = (u0[O] + gn * u1[O]) % q
        cw2 = np.zeros(n, dtype=np.int64)
        for ti, t in enumerate(O):
            den = 1
            for s_ in O:
                if s_ != t:
                    den = den * int(xs[t] - xs[s_]) % q
            wgt = int(w[ti]) * pow(den % q, q - 2, q) % q
            num = np.ones(n, dtype=np.int64)
            for s_ in O:
                if s_ != t:
                    num = num * ((xs - xs[s_]) % q) % q
            cw2 = (cw2 + wgt * num) % q
        g = gn
        Nt = order[pos:pos + (a - k)]
        u0[Nt] = (cw2[Nt] - g * u1[Nt]) % q
        assigned = list(O) + list(Nt)
        pos += (a - k)
    m = u0 < 0
    if m.any():
        u0[m] = rng.integers(0, q, size=int(m.sum()))
    return u0 % q


def piecewise_seed(amb, rng):
    n, k, q = amb.n, amb.k, amb.q
    perm = rng.permutation(n)
    nb = int(rng.integers(2, 5))
    cuts = sorted(rng.choice(np.arange(1, n), size=nb - 1, replace=False).tolist())
    u0 = np.zeros(n, dtype=np.int64)
    for blk in np.split(perm, cuts):
        cw = amb.codeword([int(rng.integers(q)) for _ in range(k)])
        u0[blk] = cw[blk]
    return u0


def structural_seeds(amb, pk, a, rng, count=16):
    """Elevated-agreement floor seeds: only exist when agreemax == a-1
    (class-blind: given to any direction that has them)."""
    q, n = amb.q, amb.n
    if pk["agreemax"] != a - 1:
        return []
    seeds = []
    pairs = amb.agree_sets(pk)
    for _ in range(count):
        S, h = pairs[int(rng.integers(len(pairs)))]
        c0 = amb.codeword([int(rng.integers(q)) for _ in range(amb.k)])
        u0 = c0.copy()
        off = [l for l in range(n) if l not in S]
        gs = rng.choice(np.arange(1, q), size=len(off), replace=False)
        for l, g in zip(off, gs):
            u0[l] = (c0[l] - int(g) * (pk["u1"][l] - h[l])) % q
        seeds.append(u0 % q)
    return seeds


def search_worst(amb, pk, a, rng, budget):
    q, n = amb.q, amb.n
    seeds = structural_seeds(amb, pk, a, rng)
    pool = [np.zeros(n, dtype=np.int64)]
    pool += [amb.mono(j) for j in range(n)]
    pool += seeds
    pool += [chain_seed(amb, pk["u1"], a, rng) for _ in range(budget["chains"])]
    pool += [piecewise_seed(amb, rng) for _ in range(budget["piecewise"])]
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
            for _ in range(budget["blockmoves"]):
                m = cur_u.copy()
                gnew = int(rng.integers(1, q))
                O = rng.choice(np.arange(n), size=amb.k, replace=False)
                w = (m[O] + gnew * pk["u1"][O]) % q
                cw = np.zeros(n, dtype=np.int64)
                for ti, t in enumerate(O):
                    den = 1
                    for s_ in O:
                        if s_ != t:
                            den = den * int(amb.xs[t] - amb.xs[s_]) % q
                    wgt = int(w[ti]) * pow(den % q, q - 2, q) % q
                    num = np.ones(n, dtype=np.int64)
                    for s_ in O:
                        if s_ != t:
                            num = num * ((amb.xs - amb.xs[s_]) % q) % q
                    cw = (cw + wgt * num) % q
                tgt = rng.choice(np.setdiff1d(np.arange(n), O),
                                 size=a - amb.k, replace=False)
                m[tgt] = (cw[tgt] - gnew * pk["u1"][tgt]) % q
                cands.append(m)
            for _ in range(budget["freshchains"]):
                cands.append(chain_seed(amb, pk["u1"], a, rng))
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


def self_test(rng):
    print("[SELF-TEST] engine vs brute, n=8 k=2 q=4129: 20 random + 4 chains",
          flush=True)
    amb = Ambient(8, 2, 4129)
    for i in range(20):
        u1 = rng.integers(0, amb.q, size=8).astype(np.int64)
        u0 = rng.integers(0, amb.q, size=8).astype(np.int64)
        a = int(rng.integers(3, 5))
        pk = amb.pack(u1)
        f = int(amb.fast_counts(u0[None, :], pk, a)[0])
        b = amb.brute_count(u0, u1, a, gchunk=4129)
        assert f == b, f"MISMATCH #{i}: fast={f} brute={b} a={a}"
        bl = amb.fast_bad_list(u0, pk, a)
        assert bl is not None and len(bl) == f, f"badlist mismatch #{i}"
        _, bg = amb.brute_count(u0, u1, a, gchunk=4129, collect=True)
        assert bl == sorted(bg), f"badlist content mismatch #{i}"
    for i in range(4):
        u1 = amb.mono(int(rng.integers(2, 8)))
        pk = amb.pack(u1)
        u0 = chain_seed(amb, u1, 3, rng)
        f = int(amb.fast_counts(u0[None, :], pk, 3)[0])
        b = amb.brute_count(u0, u1, 3, gchunk=4129)
        assert f == b, f"chain MISMATCH #{i}"
    print("[SELF-TEST] PASS (counts and bad-lists)", flush=True)


# --------------------------------------------------------------------------
# one cell
# --------------------------------------------------------------------------
def window_levels(n, k):
    return [a for a in range(k + 2, n + 1) if a * a <= n * k]


def run_cell(amb, a, rng, budget, n_spread_search, forced_pairs, cvals,
             brute_verify, results, tri_census=False):
    n, k, q = amb.n, amb.k, amb.q
    t0 = time.time()
    print(f"\n[CELL] n={n} k={k} q={q} a={a}  (window: {k+2}<={a}, "
          f"{a*a}<={n*k})", flush=True)

    # census: monomials
    mono_pk = {}
    for j in range(n):
        mono_pk[j] = amb.pack(amb.mono(j))
    elig_m = [j for j in range(n) if mono_pk[j]["agreemax"] < a]
    print(f"  eligible monomials ({len(elig_m)}): agreemax "
          f"{ {j: mono_pk[j]['agreemax'] for j in elig_m} }", flush=True)

    # census: spreads (all pairs x cvals) -- agreemax only, cheap
    spread_am = {}
    for (j, jp) in itertools.combinations(range(n), 2):
        for c in cvals:
            u1 = (amb.mono(j) + c * amb.mono(jp)) % q
            spread_am[(j, jp, c)] = amb.agreemax_only(u1)
    elig_s = {key: am for key, am in spread_am.items() if am < a}
    am_hist = {}
    for am in elig_s.values():
        am_hist[am] = am_hist.get(am, 0) + 1
    print(f"  eligible spreads: {len(elig_s)}/{len(spread_am)}; "
          f"agreemax histogram {dict(sorted(am_hist.items()))}", flush=True)
    at_floor = [key for key, am in elig_s.items() if am == a - 1]
    gapset = sorted(set((jp - j) % n for (j, jp, c) in at_floor))
    print(f"  spreads with agreemax = a-1 = {a-1}: {len(at_floor)} "
          f"(gaps {gapset}); floor certificate n-(a-1) = {n - (a - 1)}",
          flush=True)

    # pick spread search targets: prefer high agreemax, then forced pairs
    targets = sorted(elig_s.items(), key=lambda kv: -kv[1])[:n_spread_search]
    tkeys = [key for key, _ in targets]
    for fp in forced_pairs:
        for c in cvals[:1]:
            key = (fp[0], fp[1], c)
            if key in elig_s and key not in tkeys:
                tkeys.append(key)

    # search: monomials (all eligible), identical budget
    mono_best, mono_wit = {}, {}
    for j in elig_m:
        cbest, w = search_worst(amb, mono_pk[j], a, rng, budget)
        mono_best[j] = cbest
        mono_wit[j] = w
    mmax = max(mono_best.values()) if mono_best else 0
    jmax = max(mono_best, key=mono_best.get) if mono_best else None
    print(f"  [MONO] per-direction search max: {mono_best}", flush=True)
    print(f"  [MONO] baseline (search lower bound) = {mmax} at x^{jmax} "
          f"[{time.time()-t0:.0f}s]", flush=True)

    # search: spreads
    spread_best, spread_wit = {}, {}
    for key in tkeys:
        j, jp, c = key
        u1 = (amb.mono(j) + c * amb.mono(jp)) % q
        pk = amb.pack(u1)
        cbest, w = search_worst(amb, pk, a, rng, budget)
        spread_best[key] = cbest
        spread_wit[key] = w
    smax = max(spread_best.values()) if spread_best else 0
    skey = max(spread_best, key=spread_best.get) if spread_best else None
    print(f"  [SPREAD] searched {len(tkeys)} directions; per-direction max:",
          flush=True)
    for key, v in sorted(spread_best.items(), key=lambda kv: -kv[1]):
        j, jp, c = key
        print(f"    x^{j}+{c}*x^{jp} (gap {(jp-j) % n}, "
              f"agreemax {elig_s[key]}): {v}", flush=True)

    # verification of the two winners
    ver = ""
    if skey is not None:
        j, jp, c = skey
        u1s = (amb.mono(j) + c * amb.mono(jp)) % q
        pks = amb.pack(u1s)
        if brute_verify == "full":
            bs = amb.brute_count(spread_wit[skey], u1s, a)
            assert bs == smax, f"spread brute mismatch {bs} != {smax}"
            if jmax is not None:
                bm = amb.brute_count(mono_wit[jmax], amb.mono(jmax), a)
                assert bm == mmax, f"mono brute mismatch {bm} != {mmax}"
            ver = "BRUTE-full"
        else:
            bl = amb.fast_bad_list(spread_wit[skey], pks, a)
            assert bl is not None and len(bl) == smax
            sample = bl if len(bl) <= 64 else \
                [bl[i] for i in rng.choice(len(bl), size=64, replace=False)]
            for g in sample:
                assert amb.check_gamma_bad(spread_wit[skey], u1s, a, g), \
                    f"gamma {g} not actually bad"
            ver = f"per-gamma({len(sample)}/{len(bl)})"

    ratio = smax / mmax if mmax else float("inf")
    flag = "*** C=3 VIOLATED (in evidence) ***" if ratio > 3 else \
        ("C=2 violated" if ratio > 2 else "")
    stag = "-" if skey is None else f"x^{skey[0]}+{skey[2]}*x^{skey[1]}"
    print(f"  [VERDICT] n={n} k={k} q={q} a={a}: worst_spread(lb) = {smax} "
          f"({stag}), worst_mono(lb) = {mmax}"
          f" (x^{jmax}), ratio = {ratio:.3f}  [{ver}] {flag}", flush=True)
    results.append(dict(n=n, k=k, q=q, a=a, spread=smax, mono=mmax,
                        ratio=ratio, skey=skey, jmax=jmax,
                        floor=n - (a - 1), has_floor_dir=len(at_floor) > 0,
                        s_agreemax=elig_s.get(skey), ver=ver,
                        spread_wit=None if skey is None else
                        spread_wit[skey].tolist()))

    # optional: 3-component census for the subadditivity question
    if tri_census:
        best3, key3 = 0, None
        tris = list(itertools.combinations(range(4, n), 3))
        rng2 = np.random.default_rng(4669203)
        sel = [tris[i] for i in rng2.choice(len(tris), size=min(12, len(tris)),
                                            replace=False)]
        for tri in sel:
            u1 = (amb.mono(tri[0]) + amb.mono(tri[1]) + amb.mono(tri[2])) % q
            pk = amb.pack(u1)
            if pk["agreemax"] >= a:
                continue
            cbest, _ = search_worst(amb, pk, a, rng, budget)
            if cbest > best3:
                best3, key3 = cbest, tri
        print(f"  [3-COMP census] best over {len(sel)} sampled far triples: "
              f"{best3} at {key3} (vs spread {smax}, mono {mmax})", flush=True)
    print(f"  [cell {time.time()-t0:.0f}s]", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", default="all",
                    choices=["all", "n8", "n16", "n32"])
    args = ap.parse_args()
    rng = np.random.default_rng(46692)
    t0 = time.time()
    self_test(rng)
    results = []

    budget16 = dict(chains=80, piecewise=30, randoms=150, restarts=3,
                    rounds=10, mutations=96, blockmoves=16, freshchains=16,
                    stall=3)
    budget8 = dict(chains=80, piecewise=30, randoms=150, restarts=3,
                   rounds=10, mutations=96, blockmoves=16, freshchains=16,
                   stall=3)
    budget32 = dict(chains=40, piecewise=20, randoms=80, restarts=2,
                    rounds=6, mutations=64, blockmoves=12, freshchains=8,
                    stall=2)

    if args.stage in ("all", "n8"):
        for q in (4129, 4153, 4201):
            amb = Ambient(8, 2, q)
            g = int(pow(3, 1, q))
            cvals = [1, 2, g + 5]
            for a in window_levels(8, 2):
                run_cell(amb, a, rng, budget8, n_spread_search=8,
                         forced_pairs=[(3, 5), (3, 6)], cvals=cvals,
                         brute_verify="full", results=results)

    if args.stage in ("all", "n16"):
        for q in (65537, 65617, 65633):
            amb = Ambient(16, 4, q)
            cvals = [1, 2, 7]
            for a in window_levels(16, 4):
                run_cell(amb, a, rng, budget16, n_spread_search=8,
                         forced_pairs=[(4, 14), (7, 13), (4, 8)], cvals=cvals,
                         brute_verify="full" if (a >= 7 and q != 65633)
                         else "sound",
                         results=results, tri_census=(a == 7 and q == 65617))
        # k=2 at n=16 for k-diversity (cheap)
        for q in (65537, 65617):
            amb = Ambient(16, 2, q)
            for a in window_levels(16, 2):
                run_cell(amb, a, rng, budget16, n_spread_search=6,
                         forced_pairs=[(4, 14)], cvals=[1, 2],
                         brute_verify="sound", results=results)

    if args.stage in ("all", "n32"):
        qs = primes_1_mod(32, 32 ** 4, 2)
        print(f"\n[n32] primes: {qs}", flush=True)
        for q in qs:
            amb = Ambient(32, 4, q)
            for a in (6, 10, 11):
                if a == 6 and q != qs[0]:
                    continue
                run_cell(amb, a, rng, budget32, n_spread_search=8,
                         forced_pairs=[(4, 14), (8, 28)], cvals=[1, 2],
                         brute_verify="sound", results=results)

    print("\n" + "=" * 78)
    print("[G92 FINAL TABLE] worst_spread(lb) / worst_mono(search-lb) per cell")
    print(f"{'n':>3} {'k':>2} {'q':>8} {'a':>3} {'spread':>7} {'mono':>5} "
          f"{'ratio':>6} {'floor':>5} {'a-1 dir':>7}  winner")
    viol = []
    for r in results:
        wtag = "-" if r["skey"] is None else \
            f"x^{r['skey'][0]}+{r['skey'][2]}*x^{r['skey'][1]}"
        print(f"{r['n']:>3} {r['k']:>2} {r['q']:>8} {r['a']:>3} "
              f"{r['spread']:>7} {r['mono']:>5} {r['ratio']:>6.3f} "
              f"{r['floor']:>5} {str(r['has_floor_dir']):>7}  {wtag} "
              f"[{r['ver']}]")
        if r["ratio"] > 3:
            viol.append(r)
    print(f"\n[C=3 VERDICT] cells with ratio > 3: {len(viol)}")
    for r in viol:
        print(f"  VIOLATION: n={r['n']} k={r['k']} q={r['q']} a={r['a']} "
              f"spread={r['spread']} mono={r['mono']} ratio={r['ratio']:.3f} "
              f"witness u0={r['spread_wit']}")
    print(f"[total {time.time()-t0:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
