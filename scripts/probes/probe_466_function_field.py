#!/usr/bin/env python3
"""
probe_466_function_field.py -- Lane W4 (#466): the function-field model of the prize law.

QUESTION (dossier v3 sec 6 Tier-3): is there a PROVABLE function-field analogue of
    (CORE)  M(mu_n) = max_{psi != 1} |sum_{x in mu_n} psi(x)| <= C sqrt(n log m),  m = index,
for a thin 2-power multiplicative structure in F_q[t]/(f) or the Carlitz analogue of mu_n --
exploiting that Weil/RH is a THEOREM for function fields?

STRUCTURAL FACTS this probe verifies numerically (kill-risk check):

  (A) The residue ring F_q[t]/(f), f irreducible of degree d, IS the finite field F_{q^d}.
      So the "F_q[t] model" of mu_n is mu_n inside a prime-POWER field F_{p^K}. Two cases:

      (A1) TRACE-COLLAPSE LEMMA (elementary, proved in the kb note): for E = F_{p^K} and
           F' = F_p(mu_n) = F_{p^k}, k = ord_n(p) (a 2-power when n is), every additive
           character sum over mu_n factors through a' = Tr_{E/F'}(a):
               S_E(a) = S_{F'}(Tr_{E/F'} a).
           Hence  M_E(mu_n) = M_{F'}(mu_n)  if E = F' (mu_n generates), and
                  M_E(mu_n) = n  EXACTLY    if E != F' (some a != 0 has Tr_{E/F'} a = 0,
                                             giving a NONTRIVIAL character trivial on mu_n).
           Consequence 1: pumping the index m = (q^d-1)/n by growing deg f FREEZES M
           -- the naive FF law "M <= C sqrt(n log m)" with m = ring index is FALSE
           (countermodel: n = 64 in F_{193^2}: M = 64 > sqrt(2*64*ln 582) = 28.6).
           Consequence 2: the only non-degenerate FF instance is E = F_p(mu_n), i.e. the
           VERBATIM prime-power version of the open F_p problem. No new leverage.

      (A2) In the generating case, is the empirical law the SAME as over F_p
           (constant hugging sqrt(2))? If yes, the FF model is exactly-as-open,
           and Weil is exactly-as-vacuous (mu_n is a 0-dimensional group scheme in
           EVERY characteristic; RH-for-curves is Weil's theorem over F_p too --
           the "RH is proven in function fields" premise buys nothing for a 0-dim sum).

  (B) The Carlitz-module analogue. Dictionary: Z -> A = F_q[t], prime 2 -> prime t,
      mu_{2^mu} = G_m[2^mu] -> Carlitz torsion C[t^mu], "p = 1 mod 2^mu" -> f = 1 mod t^mu.
      C[t^mu](A/f) is an F_q-LINEAR SUBSPACE of F_{q^D} (Carlitz action is additive!).
      (B1) Additive character sums over an F_q-subspace V take ONLY the values {0, |V|}
           -- the naive transliteration of the prize law is DEGENERATE (max = n exactly).
      (B2) The dual model (multiplicative characters over V -- Thakur-Gauss-sum shaped,
           where Weil COULD act): at q = 2, |V| = 2^w, index 2^{D-w} (the exact "thin
           2-power structure at index 2^128" shape). Known Weil/Katz bound for subspace
           character sums saves only sqrt(q) = sqrt(2): (D-1) * 2^{w-1/2} > 2^w = trivial
           -- VACUOUS at q = 2. And subFIELD subspaces (w | D) give M = n-1 spikes
           (chi trivial on the subfield), so the unguarded dual law is FALSE too.
           We measure: Carlitz t^mu-torsion vs random subspaces vs subfield -- constant
           vs sqrt(2 n ln #chi).

REGIME DISCIPLINE: mu_n proper (index >= ~4000), Q = p^k >= n^4 (beta >= 4), never
n = Q-1, multiple primes, Fermat primes (257, 65537) excluded from compliant instances
(193 appears ONLY in the deliberately-degenerate countermodel A1, labeled as such),
p = -1 mod n (norm-one-torus symmetry) instances flagged.

Pure stdlib + numpy. Deterministic (seeded).
"""

import math
import random
import sys

import numpy as np

random.seed(466)
OUT = []


def log(s=""):
    print(s)
    OUT.append(str(s))


# ---------------------------------------------------------------- utilities
def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def factor(n: int):
    fs = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            fs[d] = fs.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        fs[n] = fs.get(n, 0) + 1
    return fs


def mult_order(a: int, n: int) -> int:
    """order of a modulo n"""
    o = 1
    x = a % n
    while x != 1:
        x = x * a % n
        o += 1
    return o


# ---------------------------------------------------------------- F_{p^k} arithmetic
class GFpk:
    """F_p[x]/(h), h monic irreducible of degree k. Elements = tuples of length k."""

    def __init__(self, p, k):
        self.p, self.k = p, k
        self.Q = p**k
        self.h = self._find_irreducible()
        self.g = self._find_generator()

    # polynomial helpers over F_p (lists low->high, len <= 2k)
    def _pmulmod(self, a, b):
        p, k, h = self.p, self.k, self.h
        r = [0] * (2 * k - 1)
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    r[i + j] = (r[i + j] + ai * bj) % p
        # reduce by monic h (degree k)
        for i in range(2 * k - 2, k - 1, -1):
            c = r[i]
            if c:
                r[i] = 0
                for j in range(k):
                    r[i - k + j] = (r[i - k + j] - c * h[j]) % p
        return tuple(r[:k])

    def mul(self, a, b):
        return self._pmulmod(list(a), list(b))

    def pw(self, a, e):
        r = tuple([1] + [0] * (self.k - 1))
        while e:
            if e & 1:
                r = self.mul(r, a)
            a = self.mul(a, a)
            e >>= 1
        return r

    def _find_irreducible(self):
        p, k = self.p, self.k
        if k == 1:
            return [0, 1]
        rng = random.Random(p * 1000 + k)
        while True:
            h = [rng.randrange(p) for _ in range(k)] + [1]
            if self._is_irred(h):
                return h

    def _is_irred(self, h):
        p, k = self.p, self.k
        # x^(p^j) mod h via repeated Frobenius; irreducible iff x^(p^k) == x
        # and x^(p^(k/l)) != x for all prime l | k.
        def pmul(a, b):
            r = [0] * (len(a) + len(b) - 1)
            for i, ai in enumerate(a):
                if ai:
                    for j, bj in enumerate(b):
                        r[i + j] = (r[i + j] + ai * bj) % p
            return r

        def pmod(a):
            a = a[:]
            for i in range(len(a) - 1, k - 1, -1):
                c = a[i]
                if c:
                    a[i] = 0
                    for j in range(k):
                        a[i - k + j] = (a[i - k + j] - c * h[j]) % p
            return a[:k]

        def ppow_x(e):  # x^e mod h
            r, b = [1], [0, 1]
            while e:
                if e & 1:
                    r = pmod(pmul(r, b))
                b = pmod(pmul(b, b))
                e >>= 1
            return r + [0] * (k - len(r))

        x = [0, 1] + [0] * (k - 2)
        if ppow_x(p**k) != x:
            return False
        for l in factor(k):
            if ppow_x(p ** (k // l)) == x:
                return False
        return True

    def _find_generator(self):
        Q = self.Q
        fs = list(factor(Q - 1))
        rng = random.Random(self.p * 7 + self.k)
        while True:
            a = tuple(rng.randrange(self.p) for _ in range(self.k))
            if all(v == 0 for v in a):
                continue
            one = tuple([1] + [0] * (self.k - 1))
            if all(self.pw(a, (Q - 1) // l) != one for l in fs):
                return a


def M_additive(p, k, n, zeta_coords_list):
    """max over nonzero F_p-functionals lambda of |sum_j e_p(lambda(zeta^j))|
    computed as a k-dimensional FFT over (Z_p)^k."""
    grid = np.zeros((p,) * k, dtype=np.complex128)
    for c in zeta_coords_list:
        grid[tuple(int(v) % p for v in c)] += 1.0
    F = np.fft.fftn(grid)
    A = np.abs(F).ravel()
    A[0] = -1.0  # exclude the trivial functional
    return float(A.max())


def instance_ext(p, k, n):
    """mu_n inside F_{p^k}; returns (M, m, degenerate_flag)."""
    K = GFpk(p, k)
    Q = K.Q
    assert (Q - 1) % n == 0, (p, k, n)
    zeta = K.pw(K.g, (Q - 1) // n)
    pts, x = [], tuple([1] + [0] * (k - 1))
    for _ in range(n):
        x = K.mul(x, zeta)
        pts.append(x)
    assert x == tuple([1] + [0] * (k - 1)), "zeta order != n"
    assert len(set(pts)) == n
    M = M_additive(p, k, n, pts)
    m = (Q - 1) / n
    return M, m


def law_c2(M, n, m):
    """M / sqrt(2 n ln m): conjectural law has this ~ 1 (C = sqrt(2) normalization)."""
    return M / math.sqrt(2 * n * math.log(m))


# ---------------------------------------------------------------- Part A
def part_A():
    log("=" * 78)
    log("PART A -- residue-ring model: mu_n inside F_q[t]/(f) = F_{p^k}")
    log("=" * 78)
    log("")
    log("A1. TRACE-COLLAPSE COUNTERMODEL (degenerate direction, labeled non-compliant):")
    log("    n=64, mu_64 in F_193 (193 = 1 mod 64), ambient E = F_{193^2} = F_193[t]/(f),")
    log("    deg f = 2. Claim: M_E = n = 64 EXACTLY (nontrivial character trivial on F_193).")
    p, n = 193, 64
    # mu_64 in the base field, embedded with second coordinate 0
    g = next(a for a in range(2, p) if mult_order(a, p) == p - 1)
    z = pow(g, (p - 1) // n, p)
    pts = [(pow(z, j, p), 0) for j in range(1, n + 1)]
    M = M_additive(p, 2, n, pts)
    mE = (p**2 - 1) / n
    log(f"    computed M_E = {M:.6f}   (n = {n})   -> exact-n degeneracy: {abs(M - n) < 1e-6}")
    for kk in (2, 3, 4):
        mk = (p**kk - 1) / n
        bound = math.sqrt(2 * n * math.log(mk))
        log(f"    deg f = {kk}: index m = {mk:.3g}, naive-FF-law bound sqrt(2n ln m) = "
            f"{bound:.2f}  vs  M = {n}  -> law violated by {n/bound:.2f}x")
    log("    => the naive F_q[t] transplant of (CORE) with m = ring index is FALSE;")
    log("       M is frozen at its F_p(mu_n) value while deg f pumps m arbitrarily.")
    log("")
    # sanity: also verify M over F_193 itself (base-field value), for the collapse identity
    Mbase = M_additive(p, 1, n, [(pow(z, j, p),) for j in range(1, n + 1)])
    log(f"    collapse identity check: M_(F_193)(mu_64) = {Mbase:.4f}; "
        f"M_E = max(n, M_base) = {max(n, Mbase):.4f} = {M:.4f}  OK={abs(M-max(n,Mbase))<1e-6}")
    log("")

    log("A2. GENERATING instances (E = F_p(mu_n) = F_{p^k}, k = ord_n(p) -- the only")
    log("    non-degenerate FF residue-ring model). Regime: Q = p^k >= n^4, index >= 4e3,")
    log("    multiple primes, no Fermat primes. Question: same sqrt(2)-law as F_p?")
    log("")
    log(f"    {'field':>14} {'n':>4} {'k':>2} {'index m':>10} {'M':>10} "
        f"{'sqrt(2n ln m)':>14} {'c2 = M/that':>12}  notes")
    rows = [
        # (p, k, n, note)
        (263, 2, 16, ""),
        (311, 2, 16, ""),
        (271, 2, 16, "p = -1 mod n (norm-one torus)"),
        (19, 4, 16, "k = 4"),
        (1039, 2, 32, ""),
        (1103, 2, 32, ""),
        (1087, 2, 32, "p = -1 mod n (norm-one torus)"),
        (41, 4, 32, "k = 4"),
    ]
    cs_ext = []
    for p, k, n, note in rows:
        assert is_prime(p)
        assert mult_order(p, n) == k, (p, k, n)
        M, m = instance_ext(p, k, n)
        c2 = law_c2(M, n, m)
        cs_ext.append(c2)
        bound = math.sqrt(2 * n * math.log(m))
        log(f"    F_{p}^{k}{'':>{max(0,10-len(str(p))-len(str(k)))}} {n:>4} {k:>2} "
            f"{m:>10.0f} {M:>10.4f} {bound:>14.4f} {c2:>12.4f}  {note}")
    log("")

    log("A3. F_p BASELINES at matched (n, index) -- the classical prize object:")
    base_rows = []
    for n, near in ((16, 66000), (16, 90000), (16, 120000),
                    (32, 1080000), (32, 1150000), (32, 1220000)):
        p = near + 1
        while not (p % n == 1 and is_prime(p) and p not in (257, 65537)):
            p += 1
        base_rows.append((p, n))
    cs_base = []
    for p, n in base_rows:
        M, m = instance_ext(p, 1, n)
        c2 = law_c2(M, n, m)
        cs_base.append(c2)
        bound = math.sqrt(2 * n * math.log(m))
        log(f"    F_{p:<9} {n:>4} {1:>2} {m:>10.0f} {M:>10.4f} {bound:>14.4f} {c2:>12.4f}")
    log("")
    log(f"    c2 over EXTENSION fields (F_q[t] model):  "
        f"min={min(cs_ext):.3f} max={max(cs_ext):.3f} mean={np.mean(cs_ext):.3f}")
    log(f"    c2 over PRIME fields   (prize object)  :  "
        f"min={min(cs_base):.3f} max={max(cs_base):.3f} mean={np.mean(cs_base):.3f}")
    log("    => if the two distributions match, the FF residue-ring model obeys the SAME")
    log("       empirical sqrt(2)-law and is the SAME open problem (Weil equally vacuous:")
    log("       mu_n is 0-dimensional in every characteristic; RH-for-curves is already a")
    log("       theorem over F_p and bounds nothing here).")
    log("")


# ---------------------------------------------------------------- GF(2) bit-polys
def clmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
    return r


def pdeg(a):
    return a.bit_length() - 1


def pmodf(a, f):
    df = pdeg(f)
    while pdeg(a) >= df:
        a ^= f << (pdeg(a) - df)
    return a


def pmulmod(a, b, f):
    return pmodf(clmul(a, b), f)


def ppow(a, e, f):
    r = 1
    while e:
        if e & 1:
            r = pmulmod(r, a, f)
        a = pmulmod(a, a, f)
        e >>= 1
    return r


def pgcd(a, b):
    while b:
        a, b = b, pmodf(a, b) if pdeg(a) >= pdeg(b) else a
        if a == b:
            break
        if b and pdeg(a) < pdeg(b):
            a, b = b, a
    return a


def pgcd2(a, b):
    while b:
        if pdeg(a) < pdeg(b):
            a, b = b, a
            continue
        a = pmodf(a, b)
        a, b = b, a
    return a


def is_irred2(f):
    """f irreducible over F_2 (deg D): x^(2^D) == x mod f, and for each prime l | D,
    gcd(x^(2^(D/l)) - x, f) == 1."""
    D = pdeg(f)
    x = 2
    # x^(2^j) by repeated squaring
    def frob_iter(j):
        y = x
        for _ in range(j):
            y = pmulmod(y, y, f)
        return y

    if frob_iter(D) != x:
        return False
    for l in factor(D):
        if pgcd2(frob_iter(D // l) ^ x, f) != 1:
            return False
    return True


def find_f_carlitz(D, mu):
    """irreducible f of degree D over F_2 with f = 1 mod t^mu (Carlitz analogue of
    p = 1 mod 2^mu)."""
    rng = random.Random(D * 100 + mu)
    while True:
        h = (1 << (D - mu)) | rng.getrandbits(D - mu - 1) << 1 | rng.getrandbits(1)
        f = (h << mu) | 1
        if pdeg(f) == D and is_irred2(f):
            return f


def gf2_matrix_kernel(cols, D):
    """kernel basis of the linear map with given column images (ints), over F_2."""
    # build rows of [M | I] style elimination on columns: solve M v = 0.
    # Represent M as list of columns; do Gaussian elimination on (column, unitvec) pairs.
    pairs = [(cols[i], 1 << i) for i in range(D)]
    basis = {}  # pivot bit -> (col, comb)
    kernel = []
    for col, comb in pairs:
        c, m = col, comb
        while c:
            pb = c.bit_length() - 1
            if pb in basis:
                bc, bm = basis[pb]
                c ^= bc
                m ^= bm
            else:
                basis[pb] = (c, m)
                break
        if c == 0:
            kernel.append(m)
    return kernel


def span_set(basis_vecs):
    s = {0}
    for b in basis_vecs:
        s |= {x ^ b for x in s}
    return s


def carlitz_torsion(f, D, mu):
    """C[t^mu](F_2[t]/f) = kernel of (C_t)^mu, C_t(u) = t*u + u^2."""
    # column images of C_t on basis t^i
    def Ct(u):
        return pmulmod(u << 1, 1, f) ^ pmulmod(u, u, f)  # t*u + u^2  (mod f)

    def Ct_pow(u, e):
        for _ in range(e):
            u = Ct(u)
        return u

    cols = [Ct_pow(1 << i, mu) for i in range(D)]
    ker = gf2_matrix_kernel(cols, D)
    return span_set(ker), len(ker)


def frobenius_subfield(f, D, w):
    """F_{2^w} inside F_2[t]/f (needs w | D): kernel of (Frob^w + id)."""
    def frob_pow(u, e):
        for _ in range(e):
            u = pmulmod(u, u, f)
        return u

    cols = [frob_pow(1 << i, w) ^ (1 << i) for i in range(D)]
    ker = gf2_matrix_kernel(cols, D)
    return span_set(ker), len(ker)


def random_subspace(D, w, rng):
    while True:
        vecs = [rng.getrandbits(D) for _ in range(w)]
        s = span_set(vecs)
        if len(s) == 1 << w:
            return s


def find_generator2(f, D):
    N = (1 << D) - 1
    fs = list(factor(N))
    rng = random.Random(D * 31 + 7)
    while True:
        g = rng.getrandbits(D)
        if g in (0, 1):
            continue
        if all(ppow(g, N // l, f) != 1 for l in fs):
            return g


def additive_char_values_check(V, D):
    """values of sum_{x in V} (-1)^<a,x> over ALL a, via Walsh-Hadamard: verify in {0,|V|}."""
    N = 1 << D
    u = np.zeros(N, dtype=np.float64)
    for x in V:
        u[x] = 1.0
    # iterative WHT
    h = 1
    while h < N:
        u = u.reshape(-1, 2 * h)
        a = u[:, :h].copy()
        b = u[:, h:].copy()
        u[:, :h] = a + b
        u[:, h:] = a - b
        u = u.ravel()
        h *= 2
    vals = set(np.round(np.abs(u)).astype(int).tolist())
    return vals


def part_B(D, mu, run_wht=True):
    log("-" * 78)
    log(f"PART B -- Carlitz model at q=2:  D = {D}, g = t^{mu}  "
        f"(|V| = n = 2^{mu} = {1 << mu}, additive index 2^{D - mu}, "
        f"#chi = 2^{D}-1 = {(1 << D) - 1})")
    log("-" * 78)
    f = find_f_carlitz(D, mu)
    log(f"    f = {f:#x} (irreducible, deg {D}, f = 1 mod t^{mu})  "
        f"[Carlitz analogue of p = 1 mod 2^mu]")
    Vc, dimc = carlitz_torsion(f, D, mu)
    log(f"    Carlitz torsion C[t^{mu}] dim = {dimc} (expected {mu}; residue module "
        f"cyclic A/(f-1): {dimc == mu})")
    n = len(Vc)

    if run_wht:
        vals = additive_char_values_check(Vc, D)
        log(f"    B1 additive characters over C[t^{mu}]: value set of |sum| = {sorted(vals)}")
        log(f"       -> ONLY {{0, n}}: the naive transliteration (additive chars over Carlitz")
        log(f"          torsion) is DEGENERATE -- max = n = {n} exactly, zero cancellation.")

    # B2: multiplicative characters via DFT over Z_{2^D-1}
    N = (1 << D) - 1
    g = find_generator2(f, D)
    w = mu
    rng = random.Random(D * 1009 + w)
    subs = {"Carlitz C[t^mu]": Vc}
    if D % w == 0:
        Vs, dims = frobenius_subfield(f, D, w)
        assert dims == w
        subs[f"subfield F_2^{w}"] = Vs
    for i in range(5):
        subs[f"random subspace #{i+1}"] = random_subspace(D, w, rng)

    names = list(subs)
    us = {nm: np.zeros(N, dtype=np.float64) for nm in names}
    sets = {nm: subs[nm] for nm in names}
    x = 1
    for i in range(N):
        x = pmulmod(x, g, f) if i > 0 else 1
        for nm in names:
            if x in sets[nm]:
                us[nm][i] = 1.0
    katz = (D - 1) * 2 ** (w - 0.5)
    log(f"    B2 multiplicative characters (dual/Thakur-Gauss-sum model), n = {n}:")
    log(f"       Weil/Katz subspace bound (D-1) q^(w-1/2) = {katz:.1f}  vs trivial n = {n}"
        f"  -> VACUOUS at q=2 (bound {'>' if katz > n else '<='} trivial)")
    log(f"       gauss-dual elementary bound sqrt(2^D) = {2**(D/2):.1f} "
        f" -> vacuous iff index > n: {(1 << (D - w)) > n}")
    log(f"       {'subspace':>22} {'M_mult':>10} {'sqrt(2n lnN)':>13} {'c2':>7}  spike?")
    for nm in names:
        S = np.fft.fft(us[nm])
        A = np.abs(S)
        A[0] = -1.0
        M = float(A.max())
        c2 = M / math.sqrt(2 * n * math.log(N))
        spike = "M = n-1 EXACT (subfield chi)" if abs(M - (n - 1)) < 1e-6 else ""
        log(f"       {nm:>22} {M:>10.4f} {math.sqrt(2*n*math.log(N)):>13.4f} "
            f"{c2:>7.3f}  {spike}")
        if nm.startswith("subfield"):
            ntriv = N // ((1 << w) - 1) - 1
            cnt = int(np.sum(np.abs(A - (n - 1)) < 1e-6))
            log(f"       {'':>22} (# nontrivial chi with |S| = n-1: {cnt}, "
                f"predicted (2^D-1)/(2^w-1) - 1 = {ntriv})")
    log("")


def main():
    quick = "--quick" in sys.argv
    log("probe_466_function_field.py -- Lane W4: function-field model of the prize law")
    log(f"numpy {np.__version__}; seed 466; quick={quick}")
    log("")
    part_A()
    part_B(12, 6)                      # sanity scale
    if not quick:
        part_B(16, 8)
        part_B(20, 10, run_wht=False)  # WHT at 2^20 fine but redundant; DFT is the point
        part_B(20, 8, run_wht=False)   # THIN regime: index 2^12 >> n = 2^8 (prize shape;
        #                                gauss-dual sqrt(2^D) = 1024 > n -- vacuous)
    with open("scripts/probes/_out_466_function_field.txt", "w") as fh:
        fh.write("\n".join(OUT) + "\n")


if __name__ == "__main__":
    main()
