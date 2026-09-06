#!/usr/bin/env python3
"""
SW1 lane HD (2026-09-05): Hasse-Davenport exact angle relations along subgroup cosets of
Z/m, run against the ladder object J_j = jacobiCoeff chi lam j of
`_R19JacobiFourierExpansion.lean`, on prize-shaped cells (mu_n, n in {8,16}, p = 1 mod n,
m = (p-1)/n with a small divisor k in {2,3,4}).

Successor of the 2026-07-10 HD arc (DISPROOF_LOG `466-r3-hasse-davenport-coset-triple-collapse`,
`466-HD1` .. `466-HD7-HD8`; `_R297HasseDavenportCosetTriple.lean`,
`_R298MixedDepthCorrelation.lean`; `probe_466_r3_hasse_davenport_coset.py`).  What is NEW here
(the HD6/HD7/HD8 certificates lived in a deleted /tmp directory and were floating-point):

  (A) the HD product relation with its EXACT normalisation, checked for EVERY divisor k of
      N = p-1 and EVERY character, on prize-shaped cells (MulChar convention g(1) = -1);
  (B) the ladder coset identities (Ik), k in {2,3,4}:
          prod_{a<k} J_{j+a m/k} = kappa_k * J_k(k j),
          kappa_k = chi(k)^k * prod_{a=1}^{k-1} Jac(chi^a, chi),  J_k = ladder of chi^k,
      at every index j (nondegenerate indices must pass; degenerate ones are reported);
  (C) the r=3 rung split: energy of the Lean `tripleConv` (nonzero-index convention of
      _R21/_R22/_R23) versus the HD-pinned strata (k=3 full-coset triples = R298's cosetDiag;
      k=2 half-shift pairs), i.e. "constrained part vs total";
  (D) the HD7/HD8 dimension law with a RIGOROUS two-sided certificate:
        nullity_Q(web) = phi(N)/2   and   pinned ladder angles = max(0, (m-1) - phi(N)/2),
      where web = conjugation rows + ALL k-fold HD product rows (k | N, k >= 2), variables
      gamma(c) = arg g(omega^c), c in Z/N \\ {0}.
        upper bound on nullity: N-1 - rank_{F_P}(web)      (rank over F_P <= rank over Q);
        lower bound on nullity: the Stickelberger/Bernoulli vectors
            f_t(c) = {t c / N} - 1/2,  t in (Z/N)^x,
          are verified EXACTLY (integer arithmetic, scaled by 2N) to lie in the null space;
          their rank over F_P is a lower bound on their Q-rank.
      Pinned ladder angles use theta_j = gamma(jn) + gamma(1) - gamma(jn+1), j in Z/m \\ {0}.

Deterministic; prints PASS/FAIL and exits nonzero on FAIL.  Exact integer/rational arithmetic
everywhere except the complex-number identity checks (A), (B), (C), which use complex128 at
relative tolerance 1e-9 on the natural scale.
"""
import cmath
import math
import sys
from fractions import Fraction

import numpy as np

TOL = 1e-9
FAILS = []


def fail(msg):
    FAILS.append(msg)
    print("  FAIL:", msg)


# ----------------------------------------------------------------------------------------
# finite field tables
# ----------------------------------------------------------------------------------------
def is_prime(p):
    if p < 2:
        return False
    d = 2
    while d * d <= p:
        if p % d == 0:
            return False
        d += 1
    return True


def prime_factors(n):
    fac = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            fac.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        fac.append(n)
    return fac


def primitive_root(p):
    fac = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g
    raise ValueError


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def phi(n):
    r = n
    for f in prime_factors(n):
        r = r // f * (f - 1)
    return r


class Cell:
    """F_p with primitive root g, N = p-1, omega^e(g^k) = zeta_N^{ek}, psi(x) = e(x/p)."""

    def __init__(self, p, n):
        assert is_prime(p) and (p - 1) % n == 0
        self.p, self.n = p, n
        self.N = p - 1
        self.m = self.N // n
        g = primitive_root(p)
        self.ind = {}
        x = 1
        for k in range(self.N):
            self.ind[x] = k
            x = (x * g) % p
        N = self.N
        self.zN = [cmath.exp(2j * math.pi * k / N) for k in range(N)]
        self.ep = [cmath.exp(2j * math.pi * k / p) for k in range(p)]
        # Gauss sums g(e) = sum_{x != 0} omega^e(x) psi(x); MulChar convention g(0) = -1.
        self.gauss = [None] * N
        for e in range(N):
            s = 0j
            for x in range(1, p):
                s += self.zN[(e * self.ind[x]) % N] * self.ep[x]
            self.gauss[e] = s
        self._jac = {}

    def chi(self, e, x):
        x %= self.p
        if x == 0:
            return 0j
        return self.zN[(e * self.ind[x]) % self.N]

    def jac(self, e1, e2):
        """Jac(omega^e1, omega^e2) = sum_x omega^e1(x) omega^e2(1-x) (MulChar: chi(0) = 0)."""
        key = (e1 % self.N, e2 % self.N)
        if key not in self._jac:
            s = 0j
            for x in range(self.p):
                s += self.chi(e1, x) * self.chi(e2, 1 - x)
            self._jac[key] = s
        return self._jac[key]

    def ladder(self, e, s=1):
        """J^{(s)}_j = Jac(lam_j, chi^s) with lam_j = omega^{j n}, chi = omega^e."""
        return [self.jac(j * self.n, s * e) for j in range(self.m)]


# ----------------------------------------------------------------------------------------
# (A) Hasse-Davenport product relation, exact normalisation, every k | N, every character
#     prod_{a=0}^{k-1} g(chi rho^a) = chi(k)^{-k} g(chi^k) prod_{a=1}^{k-1} g(rho^a),
#     rho = omega^{N/k} of exact order k; g(trivial) = -1.
# ----------------------------------------------------------------------------------------
def check_hd_product(cell, kmax=None):
    N, p = cell.N, cell.p
    ks = [k for k in divisors(N) if k >= 2 and (kmax is None or k <= kmax)]
    checked = 0
    worst = 0.0
    for k in ks:
        if p % k == 0:
            continue
        step = N // k
        aux = 1
        for a in range(1, k):
            aux *= cell.gauss[(a * step) % N]
        for c in range(N):
            lhs = 1
            for a in range(k):
                lhs *= cell.gauss[(c + a * step) % N]
            rhs = (cell.chi(c, k) ** (-k)) * cell.gauss[(k * c) % N] * aux
            scale = math.exp(0.5 * k * math.log(p))
            err = abs(lhs - rhs) / scale
            worst = max(worst, err)
            checked += 1
            if err > TOL:
                fail(f"HD product p={p} k={k} c={c} relerr={err:.3e}")
    return checked, ks, worst


# ----------------------------------------------------------------------------------------
# (B) ladder coset identities (Ik), k in {2,3,4}, k | m
# ----------------------------------------------------------------------------------------
def check_ladder_coset(cell, e=1):
    N, p, m, n = cell.N, cell.p, cell.m, cell.n
    J = cell.ladder(e)
    out = {}
    for k in (2, 3, 4):
        if m % k != 0 or p % k == 0:
            continue
        u = m // k
        kappa = cell.chi(e, k) ** k
        for a in range(1, k):
            kappa *= cell.jac(a * e, e)
        Jk = cell.ladder(e, s=k)
        nondeg_pass = nondeg_total = deg_pass = deg_total = 0
        worst = 0.0
        for j in range(m):
            lhs = 1
            degenerate = False
            for a in range(k):
                idx = (j + a * u) % m
                lhs *= J[idx]
                if (idx * n) % N == 0 or (idx * n + e) % N == 0:
                    degenerate = True
            if (k * j * n) % N == 0 or (k * j * n + k * e) % N == 0:
                degenerate = True
            for a in range(1, k + 1):
                if (a * e) % N == 0:
                    degenerate = True
            rhs = kappa * Jk[(k * j) % m]
            err = abs(lhs - rhs) / p ** (k / 2)
            ok = err <= TOL
            if degenerate:
                deg_total += 1
                deg_pass += ok
            else:
                nondeg_total += 1
                nondeg_pass += ok
                worst = max(worst, err)
                if not ok:
                    fail(f"(I{k}) p={p} n={n} m={m} j={j} relerr={err:.3e}")
        out[k] = (nondeg_pass, nondeg_total, deg_pass, deg_total, worst)
    return out


# ----------------------------------------------------------------------------------------
# (C) r=3 rung: Lean tripleConv (nonzero indices) vs HD-pinned strata
# ----------------------------------------------------------------------------------------
def rung_split(cell, e=1):
    m, p = cell.m, cell.p
    J = cell.ladder(e)
    nz = [j for j in range(m) if j != 0]
    tc = [0j] * m
    coset3 = [0j] * m   # ordered triples that are a full k=3 coset (R298 cosetDiag)
    pair2 = [0j] * m    # ordered triples containing a half-shift pair (k=2 HD-pinned)
    n_total = n_c3 = n_p2 = 0
    u3 = m // 3 if m % 3 == 0 else None
    u2 = m // 2 if m % 2 == 0 else None
    for j1 in nz:
        for j2 in nz:
            for j3 in nz:
                d = (j1 + j2 + j3) % m
                term = J[j1] * J[j2] * J[j3]
                tc[d] += term
                n_total += 1
                if u3 is not None:
                    s = {j1, j2, j3}
                    if len(s) == 3 and (((j2 - j1) % m in (u3, 2 * u3)) and ((j3 - j1) % m in (u3, 2 * u3))):
                        coset3[d] += term
                        n_c3 += 1
                if u2 is not None:
                    if (j2 - j1) % m == u2 or (j3 - j1) % m == u2 or (j3 - j2) % m == u2:
                        pair2[d] += term
                        n_p2 += 1
    # cross-check against the Lean definitional form tripleConv = sum_j selfConv(d-j) J_j
    for d in range(m):
        sc_sum = 0j
        for j in nz:
            c = (d - j) % m
            sc = sum(J[i] * J[(c - i) % m] for i in nz if (c - i) % m != 0)
            sc_sum += sc * J[j]
        if abs(sc_sum - tc[d]) > TOL * m * m * p ** 1.5:
            fail(f"tripleConv cross-check p={p} d={d}")
    E = sum(abs(z) ** 2 for z in tc)
    E3 = sum(abs(z) ** 2 for z in coset3)
    E2 = sum(abs(z) ** 2 for z in pair2)
    wick = 6 * m ** 3 * p ** 3
    return dict(E=E, E_over_wick=E / wick, E3=E3, E2=E2, n_total=n_total, n_c3=n_c3,
                n_p2=n_p2, Cinf=E / (m ** 3 * p ** 3))


# ----------------------------------------------------------------------------------------
# (D) the identity web on Z/N and the dimension law (exact two-sided certificate)
# ----------------------------------------------------------------------------------------
PRIMES = (2147483647, 2147483629)   # two large primes for modular rank (one-sided bounds)


def web_rows(N):
    """Integer rows over variables e_c, c = 1..N-1 (column c-1).  e_0 is a constant (dropped)."""
    rows = set()
    # conjugation: e_c + e_{-c}
    for c in range(1, N):
        v = [0] * (N - 1)
        v[c - 1] += 1
        v[(N - c) - 1] += 1
        rows.add(tuple(v))
    # HD product for every k | N, k >= 2, every coset representative c mod N/k
    for k in divisors(N):
        if k < 2:
            continue
        step = N // k
        for c in range(step):
            v = [0] * (N - 1)
            for a in range(k):
                idx = (c + a * step) % N
                if idx != 0:
                    v[idx - 1] += 1
            kc = (k * c) % N
            if kc != 0:
                v[kc - 1] -= 1
            for a in range(1, k):
                idx = (a * step) % N
                v[idx - 1] -= 1
            if any(v):
                rows.add(tuple(v))
    return [list(r) for r in rows]


def rank_mod(M, P):
    """Rank of an integer matrix over F_P (numpy int64, entries reduced mod P)."""
    A = np.array(M, dtype=np.int64) % P
    if A.size == 0:
        return 0
    r = 0
    rows, cols = A.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if A[i, c] != 0:
                piv = i
                break
        if piv is None:
            continue
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        others = np.nonzero(A[:, c])[0]
        others = others[others != r]
        if len(others):
            A[others] = (A[others] - np.outer(A[others, c], A[r])) % P
        r += 1
        if r == rows:
            break
    return r


def stickelberger_vectors(N):
    """2N * f_t, f_t(c) = {tc/N} - 1/2, for t in (Z/N)^x with t < N/2 (f_{-t} = -f_t)."""
    vecs = []
    for t in range(1, N):
        if math.gcd(t, N) != 1 or 2 * t > N:
            continue
        v = [2 * ((t * c) % N) - N for c in range(1, N)]   # 2N*({tc/N} - 1/2)
        vecs.append(v)
    return vecs


def dimension_law(N, n):
    m = N // n
    rows = web_rows(N)
    V = stickelberger_vectors(N)
    # exact: every Stickelberger vector is in the null space (integer arithmetic)
    for v in V:
        for r in rows:
            if sum(a * b for a, b in zip(r, v)) != 0:
                fail(f"Stickelberger vector not in null space N={N}")
                break
    rk = [rank_mod(rows, P) for P in PRIMES]
    rkV = [rank_mod(V, P) for P in PRIMES]
    nullity_upper = N - 1 - max(rk)          # rank_Q >= rank_P
    nullity_lower = max(rkV)                 # rank_Q(V) >= rank_P(V), V subset null space
    # ladder angles theta_j = e_{jn} + e_1 - e_{jn+1}, j in Z/m \ {0}
    proj_cols = []
    for j in range(1, m):
        proj_cols.append(((j * n) % N, 1, (j * n + 1) % N))
    PV = []
    for v in V:
        PV.append([v[a - 1] + v[b - 1] - v[c - 1] for (a, b, c) in proj_cols])
    rkPV = max(rank_mod(PV, P) for P in PRIMES) if PV and proj_cols else 0
    # exact rational rank of the projected null space (small matrix: <= phi(N)/2 x (m-1));
    # V spans the whole null space over Q whenever nullity_lower == nullity_upper, so
    # pinned = (m-1) - rank_Q(pi V) is then EXACT.  The pinned linear forms are the
    # rational left-kernel vectors a with sum_j a_j theta_j constant on the web.
    import sympy
    pinned_forms = []
    if PV and proj_cols:
        M = sympy.Matrix(PV)
        rkPV_exact = M.rank()
        for vec in M.nullspace():
            den = sympy.ilcm(*[sympy.fraction(x)[1] for x in vec])
            ints = [int(x * den) for x in vec]
            g = 0
            for x in ints:
                g = math.gcd(g, abs(x))
            pinned_forms.append([x // g for x in ints] if g else ints)
    else:
        rkPV_exact = 0
    pinned_exact = (m - 1) - rkPV_exact if nullity_lower == nullity_upper else None
    pinned_upper = (m - 1) - rkPV            # rank_Q(pi(Null)) >= rank_Q(pi(V)) >= rank_P
    pinned_lower = max(0, (m - 1) - nullity_upper)
    return dict(N=N, m=m, rows=len(rows), rank_modP=rk, nullity_upper=nullity_upper,
                nullity_lower=nullity_lower, phi_half=phi(N) // 2, rkV=rkV,
                angles=m - 1, rkPV=rkPV, pinned_upper=pinned_upper, pinned_lower=pinned_lower,
                pinned_exact=pinned_exact, pinned_forms=pinned_forms)


# ----------------------------------------------------------------------------------------
def main():
    cells = []
    for n in (8, 16):
        for p in range(n + 1, 600, n):
            if is_prime(p):
                m = (p - 1) // n
                if any(m % k == 0 for k in (2, 3, 4)):
                    cells.append((p, n))
    print(f"prize-shaped cells (p = 1 mod n, m has a divisor in {{2,3,4}}): {len(cells)}")
    print()
    print("(A) Hasse-Davenport product relation, every divisor k | N with k <= 16, every character:")
    print("    prod_{a<k} g(chi rho^a) = chi(k)^{-k} g(chi^k) prod_{0<a<k} g(rho^a), g(1) = -1")
    hd_total = 0
    for (p, n) in cells:
        if p > 300:
            continue                     # O(N * #divisors * k) products; keep the sweep cheap
        cell = Cell(p, n)
        checked, ks, worst = check_hd_product(cell, kmax=16)
        hd_total += checked
        print(f"  p={p:4d} n={n:2d} m={cell.m:3d}: {checked:6d} instances, k in {ks}, worst relerr {worst:.1e}")
    print(f"  total HD instances checked: {hd_total}")
    print()
    print("(B) ladder coset identities (Ik), chi = omega^1, lam_j = omega^{jn}:")
    for (p, n) in cells:
        cell = Cell(p, n)
        res = check_ladder_coset(cell, e=1)
        parts = []
        for k, (np_, nt, dp, dt, worst) in sorted(res.items()):
            parts.append(f"(I{k}) nondeg {np_}/{nt} deg {dp}/{dt} worst {worst:.1e}")
        print(f"  p={p:4d} n={n:2d} m={cell.m:3d}: " + "; ".join(parts))
    print()
    print("(C) r=3 rung split (Lean tripleConv, nonzero indices): total vs HD-pinned strata")
    print("    E/6m^3q^3 = Gaussian ratio; C_inf = E/(m^3 q^3) (TripleConvEnergyBound constant);")
    print("    E3 = k=3 full-coset stratum (R298 cosetDiag), E2 = k=2 half-shift-pair stratum")
    for (p, n) in cells:
        cell = Cell(p, n)
        if cell.m > 40:
            continue
        r = rung_split(cell, e=1)
        print(f"  p={p:4d} n={n:2d} m={cell.m:3d}: E/6m^3q^3={r['E_over_wick']:.3f} C_inf={r['Cinf']:.2f}"
              f"  E3/E={r['E3'] / r['E']:.4f} (terms {r['n_c3']}/{r['n_total']})"
              f"  E2/E={r['E2'] / r['E']:.4f} (terms {r['n_p2']}/{r['n_total']})")
    print()
    print("(D) identity-web dimension law on Z/N (exact two-sided certificate):")
    print("    nullity in [lower, upper] must pinch phi(N)/2 (Kubert-Lang rank);")
    print("    pinned = exact number of independent linear forms in the ladder angles theta_j")
    print("    (j in Z/m minus 0) fixed by the web; HD8-law = max(0, (m-1) - phi(N)/2)")
    hd8_refuted = []
    for (p, n) in cells:
        N = p - 1
        if N > 600:
            continue
        d = dimension_law(N, n)
        ok = d["nullity_lower"] == d["nullity_upper"] == d["phi_half"]
        hd8 = max(0, d["angles"] - d["phi_half"])
        pe = d["pinned_exact"]
        tag = "= HD8-law" if pe == hd8 else f"!= HD8-law {hd8} (REFUTED)"
        print(f"  N={N:4d} n={n:2d} m={d['m']:3d}: rows={d['rows']:5d} rank_P={d['rank_modP']} "
              f"nullity in [{d['nullity_lower']},{d['nullity_upper']}] phi/2={d['phi_half']} "
              f"{'OK' if ok else 'MISMATCH'}; angles={d['angles']} rank_Q(pi V)={d['angles'] - pe if pe is not None else '?'} "
              f"pinned={pe} {tag}")
        for form in d["pinned_forms"]:
            supp = {j + 1: a for j, a in enumerate(form) if a != 0}
            print(f"      pinned form (theta_j coefficients): {supp}")
        if not ok:
            fail(f"dimension law nullity N={N}")
        if pe is None:
            fail(f"pinned count not exact N={N}")
        if pe != hd8:
            hd8_refuted.append((N, n, d["m"], pe, hd8))
    if hd8_refuted:
        print(f"  HD8 dimension law REFUTED in {len(hd8_refuted)} cell(s): " + "; ".join(
            f"N={N} n={n} m={m}: pinned {pe} vs law {hd8}" for (N, n, m, pe, hd8) in hd8_refuted))
    else:
        print("  HD8 dimension law holds in every cell.")
    print()
    if FAILS:
        print(f"FAIL ({len(FAILS)} failures)")
        sys.exit(1)
    print("PASS: HD product relation exact; ladder coset identities (I2)(I3)(I4) exact at all "
          "nondegenerate indices; web nullity = phi(N)/2 certified two-sided and the pinned "
          "ladder-angle count determined exactly in every cell (see HD8 comparison above).")


if __name__ == "__main__":
    main()
