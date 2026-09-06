#!/usr/bin/env python3
"""sw1_ctr_structured_families.py -- SW1 lane CTR (2026-09-05): the ADVERSARIAL direction.

Question.  For RS[F_p, mu_n, k] at agreement a just below the Johnson agreement sqrt(nk)
(radius delta = 1 - a/n just ABOVE Johnson 1 - sqrt(rho)), is there a STRUCTURED family of far
lines {u0 + gamma*u1} whose exact MCA-bad-scalar count beats the prize budget q*eps* ~ n
ROBUSTLY in p (flat beyond some p*), and how does it scale in n?

Exact objects (ABF26 Def 4.3 / in-tree `mcaEvent`, workbench `badScalars`):
  gamma is BAD  <=>  exists S, |S| >= a, (u0+gamma*u1)|_S in RS_k|_S  and NOT (u1|_S in RS_k|_S).
  (For an a-far direction -- agreemax(u1) < a -- the second clause is automatic and
   bad = close = the far-line incidence.)
  aligned directions (u1 a codeword multiple) carry zero bad scalars and are excluded.

Engine (exact, any prime p < 2^29, int64 modular arithmetic, no floats):
  * a COVERING FAMILY of k-node sets T such that every a-subset of [n] contains some T
    (pigeonhole base / m-part partition / half+1); any codeword agreeing on >= a points is
    the interpolant through one of the T's.  For node set T:
        A = u0 - interp_T(u0),  B = u1 - interp_T(u1)   (vectors in F_p^n)
    (u0+gamma*u1) agrees with interp_T(u0+gamma*u1) at l  <=>  A_l + gamma*B_l = 0.
    base_T = #{l : A_l = B_l = 0}; cnt_T(gamma) = #{l : B_l != 0, gamma = -A_l/B_l}.
    gamma bad via T  <=>  cnt_T(gamma) >= max(1, a - base_T)      (the cnt >= 1 clause is the
    "not jointly codeword-like" MCA clause; identical to the incidence count on far directions).
  * LIST-STACKING construction of u0 (new here; G92's structural seeds used ONE set):
    let S_1..S_t be the agreement sets of u1 of size >= a-1 (its list at level a-1, codewords
    h_i).  Impose u0|_{S_i} in RS_k|_{S_i} for all i (a LINEAR system, (|S_i|-k) rows each).
    Then for every l not in S_i, gamma_{i,l} = -(u0(l)-c_i(l))/(u1(l)-h_i(l)) is bad
    (agreement set S_i u {l}), so #bad >~ sum_i (n - |S_i|) whenever the solution space is
    larger than the code.  Generic stacking cap: t*(a-1-k) <= n-k-1.

Families (all directions non-aligned; agreemax recorded):
  (i)   2-/3-spike Fourier directions x^e1 + c x^e2 (+ c' x^e3), exponents in the dual band
        [k, n-1], c in a structured set (1, -1, 2, 3, mu_n, mu_2n \\ mu_n, random);
  (ii)  directions supported on a coset of mu_{n/2^j} (j = 1, 2), plus even/odd words;
  (iii) Frobenius/Galois twists v(x^u), u odd (= exponent-orbit closure of (i));
  (iv)  offsets u0 = codeword + error on a coset (vs the stacked u0);
  (v)   the SYZ52/SYZ53 iota=2 witness shape (3-scalar chain on region cores), rate 1/2;
  (vi)  random-restart hill-climb on (u0, u1) as a control.

Self-tests: covering property (exhaustive at n <= 16, sampled at n = 32); engine vs full
codeword enumeration (n=8 k=2, n=16 k=4, n=8 k=4 at small p); two independent coverings agree
at n=32; every reported bad gamma is re-verified by plain-integer interpolation.

Usage:
  python3 sw1_ctr_structured_families.py selftest
  python3 sw1_ctr_structured_families.py cell  --n 16 --k 4 --a 7 --p 65537
  python3 sw1_ctr_structured_families.py sweep --n 16 --k 4 --a 7 [--pmax 1048576]
  python3 sw1_ctr_structured_families.py hill  --n 16 --k 4 --a 7 --p 65537
  python3 sw1_ctr_structured_families.py witness --n 16 --k 4 --a 7 --p 65537 --out FILE
Prints a final PASS/FAIL line (FAIL = an internal consistency check broke), exit code 1 on FAIL.
"""
import argparse
import itertools
import math
import os
import random
import sys
import time

os.environ.setdefault("OMP_NUM_THREADS", "2")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "2")
import numpy as np

FAILS = []


def fail(msg):
    FAILS.append(msg)
    print("[FAIL] " + msg, flush=True)


# --------------------------------------------------------------------------- primes / roots
def is_prime(m: int) -> bool:
    if m < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if m % q == 0:
            return m == q
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


def next_prime_1mod(n: int, lo: int) -> int:
    q = lo + ((1 - lo) % n)
    while not is_prime(q):
        q += n
    return q


def primes_per_octave(n: int, lo_exp: int, hi_exp: int, per: int = 2):
    """`per` primes == 1 (mod n) in each octave [2^e, 2^(e+1)), e = lo_exp..hi_exp."""
    out = []
    for e in range(lo_exp, hi_exp + 1):
        lo, hi = 1 << e, 1 << (e + 1)
        got = []
        starts = [lo + (hi - lo) * i // per for i in range(per)]
        for s in starts:
            q = next_prime_1mod(n, s)
            if q < hi and q not in got and q not in out:
                got.append(q)
        out.extend(sorted(got))
    return out


def _factor(m):
    f, d = [], 2
    while d * d <= m:
        while m % d == 0:
            f.append(d)
            m //= d
        d += 1
    if m > 1:
        f.append(m)
    return sorted(set(f))


def primitive_root(p: int) -> int:
    fs = _factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise RuntimeError("no primitive root")


def mu_points(p: int, n: int):
    """Canonical mu_n subset F_p: omega = g^((p-1)/n) for the least primitive root g."""
    assert (p - 1) % n == 0
    g = primitive_root(p)
    om = pow(g, (p - 1) // n, p)
    xs = [pow(om, i, p) for i in range(n)]
    assert len(set(xs)) == n
    return om, xs


# --------------------------------------------------------------------------- modular linear algebra
def nullspace_mod(rows, ncols: int, p: int):
    """Basis of {x in F_p^ncols : R x = 0} (python ints, exact)."""
    M = [[int(v) % p for v in r] for r in rows]
    piv_cols, r = [], 0
    for c in range(ncols):
        pr = next((i for i in range(r, len(M)) if M[i][c]), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [v * inv % p for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(vi - f * vr) % p for vi, vr in zip(M[i], M[r])]
        piv_cols.append(c)
        r += 1
        if r == len(M):
            break
    free = [c for c in range(ncols) if c not in piv_cols]
    basis = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for i, pc in enumerate(piv_cols):
            v[pc] = (-M[i][fc]) % p
        basis.append(v)
    return basis


def rank_mod(rows, ncols, p):
    return ncols - len(nullspace_mod(rows, ncols, p))


# --------------------------------------------------------------------------- covering families
def covering(n: int, k: int, a: int):
    """Node sets (P, k) such that every a-subset of range(n) contains one of them.
    Returns (array, name)."""
    cands = []
    # (A) pigeonhole base: every a-set meets range(n-a+k) in >= k points.
    base = n - a + k
    if base >= k:
        cands.append(("pigeon", math.comb(base, k)))
    # (B) m parts: some part carries >= ceil(a/m) >= k points  <=>  a > m(k-1).
    m = (a - 1) // (k - 1) if k > 1 else a
    if m >= 2:
        parts = np.array_split(np.arange(n), m)
        cands.append((f"parts{m}", sum(math.comb(len(P), k) for P in parts)))
    # (C) half+1: valid for a >= 2k-3 (the larger half then carries >= k-1 points and the
    #     other half >= 1, unless a half already carries k points).
    if k >= 2 and a >= 2 * k - 3 and n % 2 == 0:
        h = n // 2
        cands.append(("half+1", 2 * math.comb(h, k) + 2 * math.comb(h, k - 1) * h))
    name, _ = min(cands, key=lambda t: t[1])
    if name == "pigeon":
        T = np.array(list(itertools.combinations(range(base), k)), dtype=np.int64)
    elif name.startswith("parts"):
        parts = np.array_split(np.arange(n), m)
        T = np.array([c for P in parts for c in itertools.combinations(P.tolist(), k)],
                     dtype=np.int64)
    else:
        h = n // 2
        H = [list(range(h)), list(range(h, n))]
        rows = []
        for i in (0, 1):
            rows += [c for c in itertools.combinations(H[i], k)]
            for c in itertools.combinations(H[i], k - 1):
                for x in H[1 - i]:
                    rows.append(tuple(sorted(c + (x,))))
        T = np.array(rows, dtype=np.int64)
    return T, name


def check_covering_exhaustive(n, k, a, T):
    keys = set(map(tuple, T.tolist()))
    for S in itertools.combinations(range(n), a):
        if not any(c in keys for c in itertools.combinations(S, k)):
            return False
    return True


def check_covering_sampled(n, k, a, T, rng, samples=20000):
    keys = set(map(tuple, T.tolist()))
    samples = min(samples, max(40, 3_000_000 // math.comb(a, k)))
    for _ in range(samples):
        S = sorted(rng.sample(range(n), a))
        # hit test restricted to node sets inside S (cheap): use the family's own structure
        if not any(c in keys for c in itertools.combinations(S, k)):
            return False
    return True


# --------------------------------------------------------------------------- the exact engine
class Engine:
    def __init__(self, n, k, p, a, chunk_T=24000):
        assert is_prime(p) and (p - 1) % n == 0 and p < (1 << 29)
        self.n, self.k, self.p, self.a = n, k, p, a
        self.om, self.xs = mu_points(p, n)
        self.x = np.array(self.xs, dtype=np.int64)
        self.D = (self.x[:, None] - self.x[None, :]) % p          # D[l, s] = x_l - x_s
        self.T, self.cover_name = covering(n, k, a)
        self.P = len(self.T)
        self.chunk_T = chunk_T
        self._L = {}                                                # chunk id -> (Tc, Lc)

    # ---- Lagrange tensors, chunked and cached
    def _lag(self, Tc):
        """L[P, k, n]: L[i, t, l] = value at x_l of the Lagrange basis poly of node Tc[i, t]."""
        p, k, n = self.p, self.k, self.n
        Pc = len(Tc)
        L = np.zeros((Pc, k, n), dtype=np.int64)
        for t in range(k):
            num = np.ones((Pc, n), dtype=np.int64)
            den = np.ones(Pc, dtype=np.int64)
            for s in range(k):
                if s == t:
                    continue
                num = num * self.D[:, Tc[:, s]].T % p               # (Pc, n): x_l - x_{T_s}
                den = den * self.D[Tc[:, t], Tc[:, s]] % p
            dinv = np.array([pow(int(v), p - 2, p) for v in den], dtype=np.int64)
            L[:, t, :] = num * dinv[:, None] % p
        return L

    def chunks(self):
        for ci, s in enumerate(range(0, self.P, self.chunk_T)):
            if ci not in self._L:
                Tc = self.T[s:s + self.chunk_T]
                self._L[ci] = (Tc, self._lag(Tc))
            yield self._L[ci]

    def interp(self, U, Tc, Lc):
        """U (N, n) -> (N, Pc, n): interpolant of each row through each node set."""
        return np.einsum("ptl,npt->npl", Lc, U[:, Tc]) % self.p

    def modinv_arr(self, B):
        p = self.p
        res = np.ones_like(B)
        base = B.copy()
        e = p - 2
        while e:
            if e & 1:
                res = res * base % p
            base = base * base % p
            e >>= 1
        return res

    # ---- direction pack
    def pack(self, u1):
        u1 = np.asarray(u1, dtype=np.int64) % self.p
        parts, agreemax = [], 0
        for Tc, Lc in self.chunks():
            H = self.interp(u1[None, :], Tc, Lc)[0]
            B = (u1[None, :] - H) % self.p
            nz = B != 0
            Binv = np.where(nz, self.modinv_arr(np.where(nz, B, 1)), 0)
            zc = (~nz).sum(axis=1)
            agreemax = max(agreemax, int(zc.max()))
            parts.append((Tc, Lc, nz, Binv))
        return dict(u1=u1, parts=parts, agreemax=agreemax,
                    aligned=bool(agreemax == self.n))

    # ---- exact MCA-bad counts for a batch of offsets
    def counts(self, U0, pk, a=None, want_lists=False):
        a = self.a if a is None else a
        p, n = self.p, self.n
        U0 = np.asarray(U0, dtype=np.int64) % p
        if U0.ndim == 1:
            U0 = U0[None, :]
        N = len(U0)
        out = np.zeros(N, dtype=np.int64)
        lists = [set() for _ in range(N)] if want_lists else None
        nb = max(1, min(N, (1 << 22) // max(1, self.chunk_T * n)))
        for s in range(0, N, nb):
            Uc = U0[s:s + nb]
            Nc = len(Uc)
            vals_all = []
            for (Tc, Lc, nz, Binv) in pk["parts"]:
                P0 = self.interp(Uc, Tc, Lc)
                A = (Uc[:, None, :] - P0) % p
                base = ((A == 0) & (~nz)[None]).sum(axis=2)          # (Nc, Pc)
                gam = (p - A) % p * Binv[None] % p
                gam = np.where(nz[None], gam, p)
                gs = np.sort(gam, axis=2)
                tv = np.maximum(a - base, 1)                          # MCA rule
                qual = np.zeros(gs.shape, dtype=bool)
                for t in range(1, int(tv.max()) + 1):
                    rows = tv == t
                    if not rows.any():
                        continue
                    if t == 1:
                        mark = gs < p
                    else:
                        mark = np.zeros(gs.shape, dtype=bool)
                        mark[:, :, : n - (t - 1)] = ((gs[:, :, t - 1:] == gs[:, :, : n - (t - 1)])
                                                     & (gs[:, :, : n - (t - 1)] < p))
                    qual |= rows[:, :, None] & mark
                vals_all.append(np.where(qual, gs, p).reshape(Nc, -1))
            V = np.concatenate(vals_all, axis=1)
            V.sort(axis=1)
            c = (V[:, 0] < p).astype(np.int64)
            c += ((V[:, 1:] != V[:, :-1]) & (V[:, 1:] < p)).sum(axis=1)
            out[s:s + Nc] = c
            if want_lists:
                for i in range(Nc):
                    row = V[i]
                    lists[s + i] = set(int(v) for v in row[row < p])
        return (out, lists) if want_lists else out

    def bad_list_with_witness(self, u0, pk, a=None):
        """{gamma: (agreement set S, codeword values h on all n points)} exact."""
        a = self.a if a is None else a
        p, n = self.p, self.n
        u0 = np.asarray(u0, dtype=np.int64) % p
        wit = {}
        for (Tc, Lc, nz, Binv) in pk["parts"]:
            P0 = self.interp(u0[None, :], Tc, Lc)[0]
            A = (u0[None, :] - P0) % p
            base = ((A == 0) & (~nz)).sum(axis=1)
            gam = np.where(nz, (p - A) % p * Binv % p, p)
            tv = np.maximum(a - base, 1)
            for i in range(len(Tc)):
                row = gam[i]
                vals, cnts = np.unique(row[row < p], return_counts=True)
                for g, c in zip(vals, cnts):
                    if c >= tv[i] and int(g) not in wit:
                        g = int(g)
                        w = (u0 + g * pk["u1"]) % p
                        # codeword = interpolant of w through Tc[i]
                        hh = np.einsum("tl,t->l", Lc[i], w[Tc[i]]) % p
                        S = tuple(int(l) for l in np.nonzero(hh == w)[0])
                        wit[g] = (S, hh.tolist())
        return wit

    # ---- exact list of agreement sets of size >= a1 (streams a covering for a1)
    def agreement_sets(self, u1, a1, complete=True):
        """[(S tuple, h values)] for every codeword h with |{l: u1(l)=h(l)}| >= a1 (deduped by S).
        complete=False reuses the level-a count family (cheap; may miss a1-sets that contain no
        node set of that family -- a LOWER-bound list, flagged by the caller)."""
        p, n, k = self.p, self.n, self.k
        u1 = np.asarray(u1, dtype=np.int64) % p
        use_own = (a1 == self.a) or (not complete)
        if use_own:
            Tfam = self.T
        else:
            Tfam, _ = covering(n, k, a1)
            if len(Tfam) == self.P and np.array_equal(Tfam, self.T):
                use_own = True
        seen, out = set(), []
        for s in range(0, len(Tfam), self.chunk_T):
            Tc = Tfam[s:s + self.chunk_T]
            if use_own:
                ci = s // self.chunk_T
                if ci not in self._L:
                    self._L[ci] = (Tc, self._lag(Tc))
                Lc = self._L[ci][1]
            else:
                Lc = self._lag_cached_complete(a1, s, Tc)
            H = self.interp(u1[None, :], Tc, Lc)[0]
            eq = H == u1[None, :]
            zc = eq.sum(axis=1)
            for i in np.nonzero(zc >= a1)[0]:
                S = tuple(int(l) for l in np.nonzero(eq[i])[0])
                if S not in seen:
                    seen.add(S)
                    out.append((S, H[i].tolist()))
        return out

    def _lag_cached_complete(self, a1, s, Tc):
        """Lagrange chunks of the complete level-a1 covering, cached as int32 when small."""
        if not hasattr(self, "_Lc"):
            self._Lc = {}
        key = (a1, s)
        if key in self._Lc:
            return self._Lc[key].astype(np.int64)
        L = self._lag(Tc)
        Pfull = covering(self.n, self.k, a1)[0].shape[0]
        if Pfull * self.k * self.n * 4 < 700_000_000:
            self._Lc[key] = L.astype(np.int32)
        return L

    # ---- list-stacking offsets
    def parity_rows(self, S):
        """Rows v in F_p^n supported on S with v.c = 0 for every codeword c (|S|-k of them)."""
        p, k = self.p, self.k
        V = [[pow(self.xs[l], d, p) for l in S] for d in range(k)]      # k x |S|
        null = nullspace_mod(V, len(S), p)
        rows = []
        for v in null:
            r = [0] * self.n
            for j, l in enumerate(S):
                r[l] = v[j]
            rows.append(r)
        return rows

    def stack_offsets(self, sets, rng, nsamples=6, max_sets=None):
        """u0 codeword-like on as many of the given agreement sets as leaves the solution space
        strictly larger than the code.  Returns (list of u0 samples, #sets used, dim)."""
        p, n, k = self.p, self.n, self.k
        order = sorted(range(len(sets)), key=lambda i: (len(sets[i][0]), rng.random()))
        if max_sets is not None:
            order = order[:max_sets]
        rows, used = [], []
        for i in order:
            cand = rows + self.parity_rows(sets[i][0])
            d = n - rank_mod(cand, n, p)
            if d >= k + 1:
                rows, used = cand, used + [i]
        if not used:
            return [], 0, k
        Nb = nullspace_mod(rows, n, p)
        d = len(Nb)
        outs = []
        for _ in range(nsamples):
            u0 = [0] * n
            for b in Nb:
                c = rng.randrange(p)
                u0 = [(x + c * y) % p for x, y in zip(u0, b)]
            outs.append(np.array(u0, dtype=np.int64))
        return outs, len(used), d

    # ---- independent verification of a bad gamma (plain python ints, no numpy engine)
    def verify_bad(self, u0, u1, g, S):
        """Check: |S| >= a, the k-point interpolant through the first k points of S agrees with
        w = u0 + g*u1 on all of S, and u1 is NOT codeword-like on S (MCA clause)."""
        p, k, n, a = self.p, self.k, self.n, self.a
        if len(S) < a:
            return False
        w = [(int(u0[l]) + g * int(u1[l])) % p for l in range(n)]

        def interp_ok(vec):
            nodes = S[:k]
            for l in S:
                # Lagrange evaluation at x_l from nodes
                val = 0
                for t in nodes:
                    num, den = 1, 1
                    for s_ in nodes:
                        if s_ != t:
                            num = num * (self.xs[l] - self.xs[s_]) % p
                            den = den * (self.xs[t] - self.xs[s_]) % p
                    val = (val + vec[t] * num * pow(den, p - 2, p)) % p
                if val != vec[l]:
                    return False
            return True

        return interp_ok(w) and not interp_ok([int(v) % p for v in u1])

    def brute_counts_all_codewords(self, u0, u1):
        """Independent: enumerate ALL p^k codewords, all gamma (small p only). MCA rule."""
        p, k, n, a = self.p, self.k, self.n, self.a
        coeffs = np.array(list(itertools.product(range(p), repeat=k)), dtype=np.int64)
        V = np.array([[pow(x, d, p) for d in range(k)] for x in self.xs], dtype=np.int64)
        C = coeffs @ V.T % p                                          # (p^k, n)
        u0 = np.asarray(u0) % p
        u1 = np.asarray(u1) % p
        # joint sets: S where u1 codeword-like: for each codeword h, Z(h) = {u1 == h}
        eq1 = C == u1[None, :]
        bad = 0
        for g in range(p):
            w = (u0 + g * u1) % p
            eq = C == w[None, :]
            ag = eq.sum(axis=1)
            for ci in np.nonzero(ag >= a)[0]:
                S = eq[ci]
                # not jointly codeword-like on S: u1|_S must not be a codeword restriction
                if not (eq1[:, S].all(axis=1)).any():
                    bad += 1
                    break
        return bad


# --------------------------------------------------------------------------- direction families
def mono(E, e):
    return np.array([pow(x, e, E.p) for x in E.xs], dtype=np.int64)


def spike(E, exps, cs):
    u = np.zeros(E.n, dtype=np.int64)
    for e, c in zip(exps, cs):
        u = (u + c * mono(E, e)) % E.p
    return u


def c_set(E, rng, nrand=2):
    p, n = E.p, E.n
    cs = [1, p - 1, 2, 3]
    cs += [E.om]                                                       # mu_n (one rep; rest by dilation)
    if (p - 1) % (2 * n) == 0:
        g = primitive_root(p)
        cs.append(pow(g, (p - 1) // (2 * n), p))                       # mu_2n \ mu_n
    cs += [rng.randrange(2, p) for _ in range(nrand)]
    return [c % p for c in cs if c % p != 0]


def dilation_reps(n, pairs):
    """Exponent pairs modulo the odd-Galois twist e -> u e (u odd): family (iii) orbit reps."""
    seen, reps = set(), []
    for (e1, e2) in pairs:
        key = min(tuple(sorted(((u * e1) % n, (u * e2) % n))) for u in range(1, n, 2))
        if key not in seen:
            seen.add(key)
            reps.append((e1, e2))
    return reps


def family_directions(E, rng, max_pairs=None, max_triples=12, coset_samples=6, ncs=None):
    """Yields (label, family, u1)."""
    n, k, p = E.n, E.k, E.p
    band = list(range(k, n))
    pairs = list(itertools.combinations(band, 2))
    if max_pairs is not None and len(pairs) > max_pairs:
        # policy: all (k, e2); structured gaps n/2, n/4, 3n/4, 1, 2; then random fill
        pri = [(e1, e2) for (e1, e2) in pairs if e1 == k or (e2 - e1) in
               (n // 2, n // 4, 3 * n // 4, 1, 2)]
        rest = [pr for pr in pairs if pr not in pri]
        pairs = pri[:max_pairs] + rng.sample(rest, max(0, min(len(rest), max_pairs - len(pri))))
    cs = c_set(E, rng)
    if ncs is not None:
        cs = cs[:ncs]
    for (e1, e2) in pairs:
        for c in cs:
            yield (f"x^{e1}+{c}x^{e2}", "2spike", spike(E, (e1, e2), (1, c)))
    trip = list(itertools.combinations(band, 3))
    for tr in (rng.sample(trip, min(max_triples, len(trip))) if trip else []):
        for (c, c2) in ((1, 1), (1, p - 1), (2, 3)):
            yield (f"x^{tr[0]}+{c}x^{tr[1]}+{c2}x^{tr[2]}", "3spike", spike(E, tr, (1, c, c2)))
    # (ii) coset-supported and tower-structured (even / odd) directions
    for j in (1, 2):
        m = n >> j
        if m < 2:
            continue
        for r in range(1 << j):
            idx = [i for i in range(n) if i % (1 << j) == r]           # coset r * mu_m
            for e in rng.sample(band, min(coset_samples, len(band))):
                u = np.zeros(n, dtype=np.int64)
                u[idx] = mono(E, e)[idx]
                yield (f"x^{e}|coset{r}/mu{m}", f"coset_mu{m}", u)
            u = np.zeros(n, dtype=np.int64)
            u[idx] = np.array([rng.randrange(1, p) for _ in idx], dtype=np.int64)
            yield (f"rand|coset{r}/mu{m}", f"coset_mu{m}", u)
    evens = [e for e in band if e % 2 == 0]
    odds = [e for e in band if e % 2 == 1]
    for (lab, ex) in (("even", evens), ("odd", odds)):
        for _ in range(3):
            sel = rng.sample(ex, min(3, len(ex)))
            yield (f"{lab}:" + "+".join(f"x^{e}" for e in sel), f"{lab}word",
                   spike(E, sel, [1] * len(sel)))


# --------------------------------------------------------------------------- evaluation of one direction
def eval_direction(E, u1, rng, nsamples=6, coset_offsets=True, complete=True):
    """Exact max bad count over the structured offsets for direction u1.
    Returns dict(count, agreemax, nsets, used, dim, u0, mode)."""
    n, k, p, a = E.n, E.k, E.p, E.a
    pk = E.pack(u1)
    if pk["aligned"]:
        return None
    sets = E.agreement_sets(u1, a - 1, complete=complete)   # includes size >= a (non-far) sets
    true_am = max([pk["agreemax"]] + [len(S) for (S, h) in sets])
    best = dict(count=0, agreemax=true_am, nsets=len(sets), used=0, dim=k,
                u0=np.zeros(n, dtype=np.int64), mode="none")
    cands, tags = [], []
    if sets:
        U, used, d = E.stack_offsets(sets, rng, nsamples=nsamples)
        cands += U
        tags += [("stack", used, d)] * len(U)
        # single-set floor seeds (G92 structural seed) for comparison
        for (S, h) in sets[:3]:
            U1, used1, d1 = E.stack_offsets([(S, h)], rng, nsamples=1)
            cands += U1
            tags += [("single", used1, d1)] * len(U1)
    if coset_offsets:
        for j in (1, 2):
            m = n >> j
            r = rng.randrange(1 << j)
            idx = [i for i in range(n) if i % (1 << j) == r]
            c = spike(E, rng.sample(range(k), 1), (1,))
            u0 = c.copy()
            u0[idx] = (u0[idx] + np.array([rng.randrange(1, p) for _ in idx])) % p
            cands.append(u0)
            tags.append((f"cosetErr_mu{m}", 0, k))
    cands.append(np.array([rng.randrange(p) for _ in range(n)], dtype=np.int64))
    tags.append(("random", 0, k))
    cnt = E.counts(np.array(cands), pk)
    i = int(cnt.argmax())
    best.update(count=int(cnt[i]), used=tags[i][1], dim=tags[i][2], u0=cands[i],
                mode=tags[i][0], pk=pk)
    return best


def syz_iota2_lines(E, rng, max_wit=20, trials=40):
    """(v) SYZ52/53 shape: three cores (S_AB u S_AC u T etc.) from region witnesses, three
    scalars z_i, stack (u0,u1) so that u0 + z_i u1 is codeword-like on core_i.  Rate 1/2 only."""
    n, k, p, a = E.n, E.k, E.p, E.a
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    try:
        from probe_syz52_witness_lift import find_witnesses, cores_of
    except Exception as ex:                                       # pragma: no cover
        print(f"  [syz] import failed: {ex}")
        return []
    ar = (a - 1) // 2                                             # region size: s = 2ar + t = a
    t = a - 2 * ar
    if 3 * ar + t > n or ar < 1:
        return []
    _, wit = find_witnesses(p, n, ar, max_wit=max_wit)
    out = []
    for (AC, BC, AB, T, R) in wit:
        cores = cores_of(AC, BC, AB, T)
        for _ in range(trials):
            zs = rng.sample(range(1, p), 3)
            rows = []
            for i in range(3):
                for v in E.parity_rows(cores[i]):
                    rows.append(v + [(zs[i] * x) % p for x in v])
            Nb = nullspace_mod(rows, 2 * n, p)
            if not Nb:
                continue
            u = [0] * (2 * n)
            for b in Nb:
                c = rng.randrange(p)
                u = [(x + c * y) % p for x, y in zip(u, b)]
            u0 = np.array(u[:n], dtype=np.int64)
            u1 = np.array(u[n:], dtype=np.int64)
            if not u1.any():
                continue
            out.append((f"syz(ar={ar},t={t})", u0, u1))
    return out


def hill_climb(E, rng, start_u0, start_u1, evals=300):
    """(vi) control: random-restart local search on (u0, u1)."""
    n, k, p = E.n, E.k, E.p
    u0, u1 = start_u0.copy(), start_u1.copy()
    pk = E.pack(u1)
    if pk["aligned"]:
        return 0, u0, u1
    cur = int(E.counts(u0, pk)[0])
    best = (cur, u0.copy(), u1.copy())
    used = 0
    stall = 0
    while used < evals:
        cands, cpk = [], pk
        if rng.random() < 0.15:                                    # move the direction
            v1 = u1.copy()
            v1[rng.randrange(n)] = rng.randrange(p)
            cpk = E.pack(v1)
            if cpk["aligned"]:
                continue
            cands = [u0.copy()]
            for _ in range(7):
                m = u0.copy()
                m[rng.randrange(n)] = rng.randrange(p)
                cands.append(m)
        else:
            for _ in range(8):
                m = u0.copy()
                for _ in range(rng.randrange(1, 3)):
                    m[rng.randrange(n)] = rng.randrange(p)
                cands.append(m)
            # block move: patch u0 so that a fresh scalar agrees with a codeword on a-k new pts
            m = u0.copy()
            g = rng.randrange(1, p)
            O = rng.sample(range(n), k)
            w = [(int(m[l]) + g * int(cpk["u1"][l])) % p for l in O]
            for l in rng.sample([i for i in range(n) if i not in O], E.a - k):
                val = 0
                for ti, t in enumerate(O):
                    num, den = 1, 1
                    for s_ in O:
                        if s_ != t:
                            num = num * (E.xs[l] - E.xs[s_]) % p
                            den = den * (E.xs[t] - E.xs[s_]) % p
                    val = (val + w[ti] * num * pow(den, p - 2, p)) % p
                m[l] = (val - g * int(cpk["u1"][l])) % p
            cands.append(m)
        cnt = E.counts(np.array(cands), cpk)
        used += len(cands)
        i = int(cnt.argmax())
        if int(cnt[i]) >= cur:
            if int(cnt[i]) > cur:
                stall = 0
            cur, u0, u1, pk = int(cnt[i]), cands[i].copy(), cpk["u1"].copy(), cpk
            if cur > best[0]:
                best = (cur, u0.copy(), u1.copy())
        else:
            stall += 1
    return best


# --------------------------------------------------------------------------- cell driver
def run_cell(n, k, a, p, rng, verbose=True, max_pairs=None, do_syz=True, do_hill=False,
             hill_evals=240, nsamples=6):
    t0 = time.time()
    E = Engine(n, k, p, a)
    budget = n
    cap = math.comb(n, a)
    aJ = math.sqrt(n * k)
    delta = 1 - a / n
    if verbose:
        print(f"\n[CELL] n={n} k={k} a={a} p={p}  delta={delta:.4f}  Johnson 1-sqrt(rho)="
              f"{1 - math.sqrt(k / n):.4f} (a_J={aJ:.2f})  budget n={budget}  cap C(n,a)={cap}  "
              f"floor n-(a-1)={n - a + 1}  cover={E.cover_name}({E.P})  "
              f"generic stack cap t<={(n - k - 1) // max(1, a - 1 - k)}", flush=True)
    results = []
    fam_best = {}
    for (label, fam, u1) in family_directions(E, rng, max_pairs=max_pairs):
        r = eval_direction(E, u1, rng, nsamples=nsamples)
        if r is None:
            continue
        r["label"], r["fam"], r["u1"] = label, fam, u1
        results.append(r)
        fb = fam_best.get(fam)
        if fb is None or r["count"] > fb["count"]:
            fam_best[fam] = r
    if do_syz and 2 * k == n:
        for (label, u0, u1) in syz_iota2_lines(E, rng):
            pk = E.pack(u1)
            if pk["aligned"]:
                continue
            c = int(E.counts(u0, pk)[0])
            r = dict(count=c, agreemax=pk["agreemax"], nsets=-1, used=0, dim=0, u0=u0,
                     mode="syz", label=label, fam="syz_iota2", u1=u1, pk=pk)
            results.append(r)
            fb = fam_best.get("syz_iota2")
            if fb is None or c > fb["count"]:
                fam_best["syz_iota2"] = r
    best = max(results, key=lambda r: r["count"]) if results else None
    if do_hill and best is not None:
        hc, hu0, hu1 = hill_climb(E, rng, best["u0"], best["u1"], evals=hill_evals)
        pk = E.pack(hu1)
        r = dict(count=hc, agreemax=pk["agreemax"], nsets=-1, used=0, dim=0, u0=hu0,
                 mode="hill", label="hill-climb", fam="hill", u1=hu1, pk=pk)
        results.append(r)
        fam_best["hill"] = r
        if hc > best["count"]:
            best = r
        # random-start control
        ru0 = np.array([rng.randrange(p) for _ in range(n)], dtype=np.int64)
        ru1 = np.array([rng.randrange(p) for _ in range(n)], dtype=np.int64)
        hc2, hu02, hu12 = hill_climb(E, rng, ru0, ru1, evals=hill_evals)
        pk2 = E.pack(hu12)
        fam_best["hill_random_start"] = dict(count=hc2, agreemax=pk2["agreemax"], nsets=-1,
                                             used=0, dim=0, u0=hu02, mode="hill",
                                             label="hill-random", fam="hill_random_start",
                                             u1=hu12, pk=pk2)
        if hc2 > best["count"]:
            best = fam_best["hill_random_start"]
    # verify the best line's bad scalars independently
    ver = ""
    if best is not None:
        wit = E.bad_list_with_witness(best["u0"], best["pk"])
        if len(wit) != best["count"]:
            fail(f"witness count {len(wit)} != engine count {best['count']} at n={n} p={p}")
        bad_ok = all(E.verify_bad(best["u0"], best["u1"], g, S) for g, (S, h) in wit.items())
        if not bad_ok:
            fail(f"independent verification failed at n={n} k={k} a={a} p={p}")
        ver = f"verified {len(wit)}/{len(wit)}"
    if verbose:
        for fam in sorted(fam_best, key=lambda f: -fam_best[f]["count"]):
            r = fam_best[fam]
            print(f"  {fam:<18} max={r['count']:<5} {r['label']:<28} agreemax={r['agreemax']} "
                  f"L_(a-1)={r['nsets']} stacked={r['used']} dim={r['dim']} via={r['mode']}",
                  flush=True)
        if best is not None:
            print(f"  [BEST] n={n} k={k} a={a} p={p}: bad={best['count']} "
                  f"({'OVER' if best['count'] > budget else 'within'} budget {budget}; "
                  f"{best['count'] / budget:.2f}x)  dir={best['label']} [{best['fam']}] "
                  f"agreemax={best['agreemax']} L_(a-1)={best['nsets']} {ver}  "
                  f"[{time.time() - t0:.0f}s]", flush=True)
    return dict(n=n, k=k, a=a, p=p, best=best, fam_best=fam_best, E=E, elapsed=time.time() - t0)


# --------------------------------------------------------------------------- self-test
def selftest():
    rng = random.Random(1)
    print("[SELFTEST] covering families", flush=True)
    for (n, k, a) in [(8, 2, 3), (8, 2, 4), (8, 4, 5), (16, 4, 6), (16, 4, 7), (16, 4, 8),
                      (16, 8, 10), (16, 8, 11), (16, 2, 5)]:
        T, name = covering(n, k, a)
        ok = check_covering_exhaustive(n, k, a, T)
        print(f"  ({n},{k},{a}) {name} size={len(T)} exhaustive={ok}")
        if not ok:
            fail(f"covering ({n},{k},{a}) not exhaustive")
    for (n, k, a) in [(32, 8, 14), (32, 8, 15), (32, 8, 16), (64, 8, 22)]:
        T, name = covering(n, k, a)
        ok = check_covering_sampled(n, k, a, T, rng, samples=3000)
        print(f"  ({n},{k},{a}) {name} size={len(T)} sampled={ok}")
        if not ok:
            fail(f"covering ({n},{k},{a}) sampled failure")
    print("[SELFTEST] engine vs full codeword enumeration (MCA rule)", flush=True)
    for (n, k, a, p, trials) in [(8, 2, 3, 17, 30), (8, 2, 4, 41, 30), (8, 2, 3, 73, 12),
                                 (8, 4, 5, 17, 20), (16, 4, 7, 17, 8), (16, 4, 6, 17, 6)]:
        E = Engine(n, k, p, a)
        for tr in range(trials):
            if tr % 3 == 0:
                u1 = spike(E, rng.sample(range(k, n), 2), (1, rng.randrange(1, p)))
            elif tr % 3 == 1:
                u1 = np.array([rng.randrange(p) for _ in range(n)], dtype=np.int64)
                u1[: n // 2] = 0                                   # coset-ish support
            else:
                u1 = np.array([rng.randrange(p) for _ in range(n)], dtype=np.int64)
            if not u1.any():
                continue
            u0 = np.array([rng.randrange(p) for _ in range(n)], dtype=np.int64)
            if tr % 2 == 0:                                       # seeded (many bad) offsets
                pk0 = E.pack(u1)
                sets = E.agreement_sets(u1, a - 1)
                if sets:
                    U, _, _ = E.stack_offsets(sets, rng, nsamples=1)
                    if U:
                        u0 = U[0]
            pk = E.pack(u1)
            if pk["aligned"]:
                continue
            f = int(E.counts(u0, pk)[0])
            b = E.brute_counts_all_codewords(u0, u1)
            if f != b:
                fail(f"engine {f} != brute {b} at n={n} k={k} a={a} p={p} trial {tr}")
            wit = E.bad_list_with_witness(u0, pk)
            if len(wit) != f or not all(E.verify_bad(u0, u1, g, S) for g, (S, h) in wit.items()):
                fail(f"witness list inconsistent at n={n} k={k} a={a} p={p} trial {tr}")
        print(f"  n={n} k={k} a={a} p={p}: {trials} lines agree with brute force", flush=True)
    print("[SELFTEST] two independent coverings agree at n=32 k=8 a=15 (p=97)", flush=True)
    E1 = Engine(32, 8, 97, 15)
    T2 = np.array(list(itertools.combinations(range(32 - 15 + 8), 8)), dtype=np.int64)
    E2 = Engine(32, 8, 97, 15)
    E2.T, E2.P, E2.cover_name, E2._L = T2, len(T2), "pigeon-forced", {}
    for tr in range(3):
        u1 = spike(E1, rng.sample(range(8, 32), 2), (1, rng.randrange(1, 97)))
        if tr > 0:                                            # force an (a-1)-agreement set
            h = spike(E1, rng.sample(range(8), 3), (1, 2, 3))
            u1 = h.copy()
            for l in rng.sample(range(32), 32 - 14):
                u1[l] = (u1[l] + rng.randrange(1, 97)) % 97
        sets = E1.agreement_sets(u1, 14)
        U, _, _ = E1.stack_offsets(sets, rng, nsamples=1) if sets else ([], 0, 0)
        u0 = U[0] if U else np.array([rng.randrange(97) for _ in range(32)], dtype=np.int64)
        c1 = int(E1.counts(u0, E1.pack(u1))[0])
        c2 = int(E2.counts(u0, E2.pack(u1))[0])
        print(f"  trial {tr}: half-family {c1} vs pigeonhole-family {c2}", flush=True)
        if c1 != c2:
            fail(f"n=32 coverings disagree {c1} vs {c2}")


# --------------------------------------------------------------------------- sweep driver
def sweep(n, k, a, pmin_exp, pmax_exp, per, rng_seed, max_pairs, hill_at, out_rows):
    primes = primes_per_octave(n, pmin_exp, pmax_exp, per)
    print(f"\n[SWEEP] n={n} k={k} a={a}: {len(primes)} primes == 1 (mod {n}): {primes}",
          flush=True)
    rows = []
    for p in primes:
        rng = random.Random(rng_seed * 1000003 + p)
        res = run_cell(n, k, a, p, rng, max_pairs=max_pairs, do_hill=(p in hill_at))
        b = res["best"]
        fb = res["fam_best"]
        row = dict(p=p, best=b["count"] if b else 0, label=b["label"] if b else "-",
                   fam=b["fam"] if b else "-", L=b["nsets"] if b else 0,
                   fams={f: fb[f]["count"] for f in fb}, t=res["elapsed"])
        rows.append(row)
        out_rows.append((n, k, a, row))
    print(f"\n[SWEEP TABLE] n={n} k={k} a={a}  budget n={n}  cap C(n,a)={math.comb(n, a)}")
    fams = sorted({f for r in rows for f in r["fams"]})
    print(f"{'p':>10} {'log2':>5} {'best':>5} {'x/n':>5}  " + " ".join(f"{f[:10]:>10}" for f in fams)
          + "  winner")
    for r in rows:
        print(f"{r['p']:>10} {math.log2(r['p']):5.1f} {r['best']:>5} {r['best'] / n:5.2f}  "
              + " ".join(f"{r['fams'].get(f, 0):>10}" for f in fams)
              + f"  {r['label']} [{r['fam']}] L={r['L']}")
    return rows


def write_witness(n, k, a, p, rng, path, max_pairs=None):
    res = run_cell(n, k, a, p, rng, max_pairs=max_pairs, do_hill=True)
    b = res["best"]
    E = res["E"]
    wit = E.bad_list_with_witness(b["u0"], b["pk"])
    with open(path, "w") as f:
        f.write(f"# SW1-CTR witness  n={n} k={k} a={a} p={p}  omega={E.om} (mu_n = omega^i)\n")
        f.write(f"# delta = {1 - a / n:.6f}  Johnson = {1 - math.sqrt(k / n):.6f}  "
                f"budget n = {n}  bad = {len(wit)}  direction agreemax = {b['agreemax']} "
                f"(a-far: {b['agreemax'] < a})  family = {b['fam']} {b['label']}\n")
        f.write(f"u0 = {b['u0'].tolist()}\n")
        f.write(f"u1 = {b['u1'].tolist()}\n")
        f.write("# gamma : agreement set S (indices i of omega^i) : codeword values on mu_n\n")
        for g in sorted(wit):
            S, h = wit[g]
            ok = E.verify_bad(b["u0"], b["u1"], g, S)
            f.write(f"{g} : {list(S)} : {h}  verified={ok}\n")
    print(f"[witness] wrote {path} ({len(wit)} bad scalars)")
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("stage", choices=["selftest", "cell", "sweep", "hill", "witness"])
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--k", type=int, default=4)
    ap.add_argument("--a", type=int, default=7)
    ap.add_argument("--p", type=int, default=65537)
    ap.add_argument("--pmin", type=int, default=None, help="min octave exponent")
    ap.add_argument("--pmax", type=int, default=20, help="max octave exponent")
    ap.add_argument("--per", type=int, default=2, help="primes per octave")
    ap.add_argument("--max-pairs", type=int, default=None)
    ap.add_argument("--hill-evals", type=int, default=240)
    ap.add_argument("--seed", type=int, default=2026)
    ap.add_argument("--out", type=str, default=None)
    args = ap.parse_args()
    t0 = time.time()
    if args.stage == "selftest":
        selftest()
    elif args.stage == "cell":
        run_cell(args.n, args.k, args.a, args.p, random.Random(args.seed),
                 max_pairs=args.max_pairs, do_hill=False)
    elif args.stage == "hill":
        run_cell(args.n, args.k, args.a, args.p, random.Random(args.seed),
                 max_pairs=args.max_pairs, do_hill=True, hill_evals=args.hill_evals)
    elif args.stage == "sweep":
        pmin = args.pmin if args.pmin is not None else (args.n.bit_length())
        rows = []
        hill_at = set()
        sweep(args.n, args.k, args.a, pmin, args.pmax, args.per, args.seed, args.max_pairs,
              hill_at, rows)
    elif args.stage == "witness":
        write_witness(args.n, args.k, args.a, args.p, random.Random(args.seed),
                      args.out or f"sw1_ctr_witness_{args.n}_{args.p}.txt",
                      max_pairs=args.max_pairs)
    print(f"\n[{time.time() - t0:.0f}s] " + ("FAIL: " + "; ".join(FAILS) if FAILS else "PASS"))
    sys.exit(1 if FAILS else 0)


if __name__ == "__main__":
    main()
