#!/usr/bin/env python3
"""probe_466b_p5_referee.py -- LANE P5REF (#466 round 2): independent referee
re-verification of the round-1 claim

    "windowed SumsetExtremal is REFUTED at n = 16: at n=16, k=4, a=7
     (window-interior delta = 9/16), the 2-Fourier-component direction
     u1 = x^4 + 1*x^14 strictly beats every monomial direction's
     worst-offset bad-scalar count, 13 vs exactly 9, at q in
     {65537, 65617, 65633}."

REFEREE PROTOCOL (independent code; the original probe was read only to fix
conventions, no logic imported at the code level):
  conventions replicated:
    - domain = mu_16 = the (unique) order-16 subgroup of F_q^*, k = 4;
    - bad-scalar count of a stack (u0, u1) at agreement level a =
        #{gamma in F_q : exists c in RS_k(mu_16) with
                          #{l : (u0 + gamma*u1)(x_l) = c(x_l)} >= a};
    - direction eligible at level a iff agreemax(u1) < a, where
      agreemax(u1) = max agreement of u1 itself with an RS_k codeword;
    - level a=7  <=>  delta = 1 - a/n = 9/16 (window-interior check below).
  ground truth: EVERY decision number printed as [BRUTE] is computed by full
  enumeration of ALL q scalars gamma, testing RS(>=a)-agreement of
  u0 + gamma*u1 against every one of the C(16,4) = 1820 degree<4 Lagrange
  interpolants (exhaustive and exact: any codeword agreeing on >= a >= k
  points IS the interpolant of one of its k-subsets).
  search accelerator: a linear-in-gamma exact engine (base + per-position
  candidate-gamma multiplicity thresholding; the interpolation trick is
  mathematically forced, so it necessarily coincides with the original
  probe's math) -- but it is re-derived and re-implemented here, and is
  SELF-TESTED against the full-enumeration path at n=8 (q=4129, all gamma)
  and spot-tested at n=16 before any verdict is drawn.
  search parity: monomial and spread directions get the IDENTICAL search
  driver and budget (the original run gave the spread class more refinement;
  here both classes get the same, larger, budget), so the monomial max is a
  like-for-like lower bound.
  witnesses: the spread side additionally gets a purely STRUCTURAL seed
  (derived from the agreemax=6 codeword of u1; see spread_structural_seeds)
  which already certifies >= 10 > 9 without any search.

Verdict semantics: worst-u0 search is heuristic for BOTH classes, so every
reported max is a lower bound on the true worst case; only brute-verified
witness counts are asserted as exact.

Usage: python probe_466b_p5_referee.py [--qmain 65617] [--second 65633]
                                       [--quick]
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


# ---------------------------------------------------------------------------
# primality (deterministic Miller-Rabin for 64-bit)
# ---------------------------------------------------------------------------
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


def inverse_table(q: int) -> np.ndarray:
    inv = np.zeros(q, dtype=np.int64)
    inv[1] = 1
    for i in range(2, q):
        inv[i] = (q - (q // i) * inv[q % i]) % q
    return inv


# ---------------------------------------------------------------------------
# ambient setting: mu_n in F_q, all C(n,k) Lagrange interpolants
# ---------------------------------------------------------------------------
class Ambient:
    def __init__(self, n: int, k: int, q: int):
        assert is_prime(q), f"{q} not prime"
        assert (q - 1) % n == 0, f"mu_{n} does not embed in F_{q}^*"
        self.n, self.k, self.q = n, k, q
        # order-n element: g^((q-1)/n) for successive g, requiring exact order n
        # (n is a power of two here, so order n <=> x^(n/2) != 1).
        om = None
        for g in range(2, q):
            x = pow(g, (q - 1) // n, q)
            if pow(x, n // 2, q) != 1:
                om = x
                break
        assert om is not None
        self.om = om
        xs = np.array([pow(om, l, q) for l in range(n)], dtype=np.int64)
        assert len(set(xs.tolist())) == n
        self.xs = xs
        subsets = list(itertools.combinations(range(n), k))
        self.P = len(subsets)
        self.Tidx = np.array(subsets, dtype=np.int64)
        # Lagrange basis evaluations L[p, t, l] = ell_{T_p, t}(x_l)
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

    # -- basic vectors -------------------------------------------------------
    def mono(self, j: int) -> np.ndarray:
        return np.array([pow(int(x), j, self.q) for x in self.xs], dtype=np.int64)

    def codeword(self, coeffs) -> np.ndarray:
        r = np.zeros(self.n, dtype=np.int64)
        for c in reversed(list(coeffs)):
            r = (r * self.xs + c) % self.q
        return r

    # -- direction preprocessing ---------------------------------------------
    def pack(self, u1) -> dict:
        q = self.q
        u1 = np.asarray(u1, dtype=np.int64) % q
        H = np.einsum("ptl,pt->pl", self.L, u1[self.Tidx]) % q
        B = (u1[None, :] - H) % q
        zc = (B == 0).sum(axis=1)
        return dict(u1=u1, B=B, nz=(B != 0), Binv=self.inv[B],
                    agreemax=int(zc.max()), zerocounts=zc)

    def agree_sets(self, pk) -> list:
        """All (positions, codeword) pairs realizing agreemax for pk['u1']."""
        out, seen = [], set()
        am = pk["agreemax"]
        for pi in np.nonzero(pk["zerocounts"] == am)[0]:
            S = tuple(np.nonzero(pk["B"][pi] == 0)[0].tolist())
            if S in seen:
                continue
            seen.add(S)
            h = np.einsum("tl,t->l", self.L[pi],
                          pk["u1"][self.Tidx[pi]]) % self.q
            out.append((S, h))
        return out

    # -- exact bad-scalar counts, linear-in-gamma engine (search accelerator) -
    def fast_counts(self, U, pk, a: int, chunk: int = 192) -> np.ndarray:
        q, n, P = self.q, self.n, self.P
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
            base = ((A == 0) & Bz).sum(axis=2)                    # (N,P)
            gam = (q - A) % q * pk["Binv"][None] % q
            gam = np.where(pk["nz"][None], gam, q)                # sentinel q
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

    # -- GROUND TRUTH: full enumeration over ALL gamma in F_q ------------------
    def brute_count(self, u0, u1, a: int, gchunk: int = 256,
                    collect: bool = False):
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


# ---------------------------------------------------------------------------
# u0 candidate builders (referee's own constructions)
# ---------------------------------------------------------------------------
def chain_seed(amb: Ambient, u1, a: int, rng) -> np.ndarray:
    """Glued interpolation-adversarial word: block 1 forces gamma_1 on an
    a-set; each later block reuses k already-assigned positions (so the new
    codeword is the interpolant of u0 + g_new*u1 there) and forces g_new on
    a-k fresh positions.  Certifies 1 + floor((n-a)/(a-k)) bad scalars."""
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
        # interpolate (O, w) -> codeword values everywhere
        pi = None  # build Lagrange directly (O may be any k-set)
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


def piecewise_seed(amb: Ambient, rng) -> np.ndarray:
    n, k, q = amb.n, amb.k, amb.q
    perm = rng.permutation(n)
    nb = int(rng.integers(2, 5))
    cuts = sorted(rng.choice(np.arange(1, n), size=nb - 1, replace=False).tolist())
    u0 = np.zeros(n, dtype=np.int64)
    for blk in np.split(perm, cuts):
        cw = amb.codeword([int(rng.integers(q)) for _ in range(k)])
        u0[blk] = cw[blk]
    return u0


def spread_structural_seeds(amb: Ambient, pk, a: int, rng, count: int = 24):
    """The mechanism behind the win: if u1 agrees with a codeword h on a set
    S* with |S*| = agreemax = a - 1, take any codeword c0 and set
    u0 = c0 on S*, u0_l = c0_l - g_l*(u1_l - h_l) off S* with distinct g_l.
    Then u0 + g_l*u1 agrees with the codeword c0 + g_l*h on S* + {l}:
    |S*| + 1 = a points, so ALL n - |S*| chosen scalars are bad.  For
    agreemax = 6, n = 16 this certifies >= 10 bad scalars deterministically."""
    q, n = amb.q, amb.n
    seeds = []
    pairs = amb.agree_sets(pk)
    for _ in range(count):
        S, h = pairs[int(rng.integers(len(pairs)))]
        if len(S) < a - 1:
            break
        c0 = amb.codeword([int(rng.integers(q)) for _ in range(amb.k)])
        u0 = c0.copy()
        off = [l for l in range(n) if l not in S]
        gs = rng.choice(np.arange(1, q), size=len(off), replace=False)
        for l, g in zip(off, gs):
            u0[l] = (c0[l] - int(g) * (pk["u1"][l] - h[l])) % q
        seeds.append(u0 % q)
    return seeds


# ---------------------------------------------------------------------------
# the (class-blind) search driver: identical protocol for every direction
# ---------------------------------------------------------------------------
def search_worst(amb: Ambient, pk, a: int, rng, budget: dict,
                 extra_seeds=None):
    q, n = amb.q, amb.n
    pool = [np.zeros(n, dtype=np.int64)]
    pool += [amb.mono(j) for j in range(n)]
    pool += list(extra_seeds or [])
    pool += [chain_seed(amb, pk["u1"], a, rng) for _ in range(budget["chains"])]
    pool += [piecewise_seed(amb, rng) for _ in range(budget["piecewise"])]
    pool += [rng.integers(0, q, size=n).astype(np.int64)
             for _ in range(budget["randoms"])]
    U = np.array(pool)
    cnt = amb.fast_counts(U, pk, a)
    order = np.argsort(-cnt)
    best_c, best_u = int(cnt[order[0]]), U[order[0]].copy()

    # hill climb with restarts from the top pool entries
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


# ---------------------------------------------------------------------------
# engine self-test at n=8 against full enumeration
# ---------------------------------------------------------------------------
def self_test(rng):
    print("[SELF-TEST] engine vs full-enumeration ground truth, n=8 k=2 "
          "q=4129, 24 random instances + 6 adversarial chains", flush=True)
    amb = Ambient(8, 2, 4129)
    ok = 0
    for i in range(24):
        u1 = rng.integers(0, amb.q, size=8).astype(np.int64)
        u0 = rng.integers(0, amb.q, size=8).astype(np.int64)
        a = int(rng.integers(3, 5))
        pk = amb.pack(u1)
        f = int(amb.fast_counts(u0[None, :], pk, a)[0])
        b = amb.brute_count(u0, u1, a, gchunk=4129)
        assert f == b, f"SELF-TEST MISMATCH #{i}: fast={f} brute={b} a={a}"
        ok += 1
    for i in range(6):
        u1 = amb.mono(int(rng.integers(2, 8)))
        pk = amb.pack(u1)
        a = 3
        u0 = chain_seed(amb, u1, a, rng)
        f = int(amb.fast_counts(u0[None, :], pk, a)[0])
        b = amb.brute_count(u0, u1, a, gchunk=4129)
        assert f == b, f"SELF-TEST chain MISMATCH #{i}: fast={f} brute={b}"
        guaranteed = 1 + (amb.n - a) // (a - amb.k)
        assert f >= guaranteed, f"chain below its certificate: {f} < {guaranteed}"
        ok += 1
    print(f"[SELF-TEST] all {ok} instances: fast == brute.  PASS", flush=True)


# ---------------------------------------------------------------------------
# one referee run at a given prime
# ---------------------------------------------------------------------------
def referee_setting(q: int, a: int, rng, budget: dict, spot_brute: bool):
    n, k = 16, 4
    t0 = time.time()
    print(f"\n{'='*78}\n[REFEREE] n={n} k={k} q={q} a={a}", flush=True)
    # (3) window / regime arithmetic
    delta = 1 - a / n
    print(f"  window check: delta = 1 - a/n = {n-a}/{n} = {delta:.4f}; "
          f"prize window (1-sqrt(rho), 1-rho) = (0.5, 0.75); interior: "
          f"{0.5 < delta < 0.75}", flush=True)
    print(f"  regime check: q prime: {is_prime(q)}; q >= n^4 = {n**4}: "
          f"{q >= n**4}; n | q-1: {(q-1) % n == 0}; proper subgroup "
          f"(n < q-1): {n < q - 1}", flush=True)
    amb = Ambient(n, k, q)
    print(f"  mu_16 generator (referee's own choice) omega = {amb.om}; "
          f"{amb.P} interpolants", flush=True)

    # monomial degeneracy census
    packs = {}
    print("  monomial agreemax census:", flush=True)
    line = []
    for j in range(n):
        pk = amb.pack(amb.mono(j))
        packs[j] = pk
        line.append(f"j{j}:{pk['agreemax']}")
    print("    " + " ".join(line), flush=True)
    eligible = [j for j in range(n) if packs[j]["agreemax"] < a]
    print(f"  eligible monomials at a={a}: {eligible} "
          f"(degenerate: {[j for j in range(n) if j not in eligible]})",
          flush=True)

    # ---- SPREAD SIDE: the claimed winning direction x^4 + 1*x^14 ----------
    u1s = (amb.mono(4) + amb.mono(14)) % q
    pks = amb.pack(u1s)
    gaps = (10, 16 - 10)
    print(f"\n  [SPREAD] u1 = x^4 + x^14 on mu_16 (their sp2_4_14_c1): "
          f"agreemax = {pks['agreemax']} (claimed 6); eligible at a={a}: "
          f"{pks['agreemax'] < a}", flush=True)
    print(f"  correlated-direction exclusion: component gap 14-4 = 10 "
          f"(= {min(gaps)} mod-16-symmetric); n/2 = 8; gap != n/2: "
          f"{min(gaps) != 8 and max(gaps) != 8}", flush=True)
    asets = amb.agree_sets(pks)
    for S, h in asets:
        print(f"    agreemax witness: u1 agrees with codeword on positions "
              f"{list(S)} (|S| = {len(S)})", flush=True)

    seeds = spread_structural_seeds(amb, pks, a, rng, count=24)
    if seeds:
        sc = amb.fast_counts(np.array(seeds), pks, a)
        print(f"  structural seeds (no search): counts {sorted(set(sc.tolist()))} "
          f"-- certificate floor {n - pks['agreemax']} = {n - pks['agreemax']}",
          flush=True)
    best_s, wit_s = search_worst(amb, pks, a, rng, budget, extra_seeds=seeds)
    print(f"  [SPREAD] search max (fast engine) = {best_s}", flush=True)
    bs, badg = amb.brute_count(wit_s, u1s, a, collect=True)
    assert bs == best_s, f"spread witness mismatch: fast={best_s} brute={bs}"
    print(f"  [BRUTE] spread witness verified over ALL {q} gammas: "
          f"count = {bs}; bad gammas = {badg}", flush=True)
    print(f"  [BRUTE] spread witness u0 = {wit_s.tolist()}", flush=True)

    # ---- MONOMIAL SIDE: identical protocol, every eligible monomial --------
    mono_best = {}
    mono_wit = {}
    for j in eligible:
        c, w = search_worst(amb, packs[j], a, rng, budget, extra_seeds=None)
        mono_best[j] = c
        mono_wit[j] = w
        print(f"  [MONO] x^{j}: search max = {c}   [{time.time()-t0:.0f}s]",
              flush=True)
    mmax = max(mono_best.values())
    jmax = max(mono_best, key=mono_best.get)
    if spot_brute:
        bm = amb.brute_count(mono_wit[jmax], amb.mono(jmax), a)
        assert bm == mono_best[jmax], \
            f"mono witness mismatch: fast={mono_best[jmax]} brute={bm}"
        print(f"  [BRUTE] best monomial witness (x^{jmax}) verified over ALL "
              f"gammas: count = {bm}", flush=True)

    print(f"\n  [VERDICT q={q} a={a}] spread(x^4+x^14) = {best_s}  vs  "
          f"monomial max = {mmax} (all: {mono_best})", flush=True)
    strict = best_s > mmax
    print(f"  spread strictly beats every monomial: {strict}   "
          f"[setting {time.time()-t0:.0f}s]", flush=True)
    return dict(q=q, spread=best_s, mono=mono_best, mono_max=mmax,
                strict=strict, agreemax_spread=pks["agreemax"],
                bad_gammas=badg)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--qmain", type=int, default=65617)
    ap.add_argument("--second", type=int, default=65633)
    ap.add_argument("--skip-second", action="store_true")
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    rng = np.random.default_rng(466901)
    t0 = time.time()

    self_test(rng)

    if args.quick:
        budget = dict(chains=60, piecewise=30, randoms=120, restarts=3,
                      rounds=8, mutations=96, blockmoves=16, freshchains=16,
                      stall=3)
        budget2 = budget
    else:
        # >= the original run's budget on the monomial side (they used a
        # 209-word shared pool + 24 chains, then 3 refine rounds x ~128 for
        # the top-2 monomials only; here EVERY direction gets a ~1000-word
        # pool + a multi-restart climb, i.e. several thousand exact
        # evaluations per direction).
        budget = dict(chains=120, piecewise=40, randoms=200, restarts=3,
                      rounds=10, mutations=96, blockmoves=16, freshchains=16,
                      stall=3)
        budget2 = budget

    results = []
    results.append(referee_setting(args.qmain, 7, rng, budget,
                                   spot_brute=True))
    if not args.skip_second:
        results.append(referee_setting(args.second, 7, rng, budget2,
                                       spot_brute=False))

    print("\n" + "=" * 78)
    print("[REFEREE FINAL] claim under review: at n=16 k=4 a=7 (delta=9/16), "
          "sp2_4_14_c1 beats every monomial 13 vs 9 at q=65617 (and 65633).")
    for r in results:
        ratio = r["spread"] / r["mono_max"]
        print(f"  q={r['q']}: spread(x^4+x^14) = {r['spread']} "
              f"(agreemax {r['agreemax_spread']}), monomial max = "
              f"{r['mono_max']}, strict win: {r['strict']}, "
              f"excess ratio >= {ratio:.2f} (round-1 proposed replacement "
              f"law C <= 2: {'VIOLATED' if ratio > 2 else 'respected'} "
              f"if the monomial value is the true optimum)", flush=True)
    print(f"[total {time.time()-t0:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
