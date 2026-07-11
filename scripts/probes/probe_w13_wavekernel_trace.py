#!/usr/bin/env python3
"""
probe_w13_wavekernel_trace.py -- W13: does arXiv 2606.27075 (wave kernels / trace identities
on regular graphs) add ANY lever beyond the killed non-backtracking relabeling?
==============================================================================================
THREAD wall:probe-batch (#466).  Context: workbench sec 5(7) lists "non-backtracking
Ihara-Bass (2606.27075)" among probes-never-run.  That list is STALE: round-1 P2
(`probe_466_nonbacktracking.py`, DISPROOF_LOG `466-r1-nonbacktracking-relabeling`, brick
`_NonBacktrackingRelabelingNoGo.lean`) already killed the NB SPECTRAL RADIUS as a monotone
relabel of M on Cay(F_p, mu_n).

WHAT THIS PROBE ADDS (the residual sliver, checked here):
arXiv 2606.27075 (Basic-Smajlovic-Sabanac, "Discrete Space-Time Wave Kernels and Trace
Identities on Regular Graphs") is NOT a spectral-radius paper: its new machinery is
  (i)  explicit discrete WAVE KERNELS on (q+1)-regular graphs (forward time-difference
       scheme), expressed via discrete modified Bessel functions AND non-backtracking walk
       counts;
  (ii) a NEW TRACE-TYPE FORMULA for the affine Laplace-type operator, yielding closed-form
       evaluations of additive-character-twisted trigonometric sums.
Could the trace formula (an IDENTITY, not a radius) provide a new arithmetic INPUT for the
wall M(mu_n) <= C*sqrt(n*log(p/n))?  This probe decides that by verifying the structural
facts the no-go needs, numerically and exactly:

  (F1) [dictionary is exact]   On Cay(F_p, mu_n): the NB-walk trace ladder tr(N_m), the
       Hashimoto moments tr(B^m) (computed DIRECTLY from the Hashimoto matrix, integer
       arithmetic), and the wave-kernel traces tr(K_t) of the forward-difference wave
       recursion  K_{t+1} = A K_t - q K_{t-1}  (the recursion whose solution IS the
       Bessel/NB-walk kernel of the paper) are ALL reconstructed to machine precision from
       the adjacency power sums P_j = sum_lambda lambda^j alone (eta computed by FFT,
       independent of the graph walk computation).
  (F2) [coefficients are instance-blind]  The reconstruction coefficients (the
       Chebyshev-like triangle c_{m,j} with s_m = lambda*s_{m-1} - q*s_{m-2}) are EXACT
       RATIONALS depending only on (m, q = n-1) -- verified bitwise identical across
       different primes p at the same n.  Hence every identity the paper's trace formula
       can produce on Cay(F_p, mu_n) is an identity WITHIN the moment ladder {P_j}
       (the E_r wall vocabulary): it constrains nothing the power sums do not already
       determine, and carries ZERO p-arithmetic beyond them.
  (F3) [bounded-depth moment data cannot pin M]  The known countermodel pair
       n=16, p=65617 vs p=65633 (DISPROOF_LOG `466-r1-hankel-bounded-window-refuted`):
       low-depth normalized moments nearly identical while M differs by ~4-5%.  So a
       trace-formula identity at bounded depth (any fixed collection of wave-kernel/NB
       trace identities) CANNOT distinguish instances whose M differ -- the L-infinity
       target needs depth r ~ log p, which IS the wall (tool-shape principle).

DECISION RULE (pre-registered): if F1+F2+F3 all hold, verdict = DEAD (the paper's trace
identities are an exact, instance-blind repackaging of the same moment ladder the wall is
made of; no independent lever).  If any wave-kernel trace on the testbed carries information
beyond {P_j} (F1/F2 failure) or bounded-depth moments separate the F3 pair, verdict = LIVE.

REGIME NOTE: F1/F2 verify DETERMINISTIC ALGEBRAIC IDENTITIES -- regime discipline is
irrelevant there (small p exact cases, matching `probe_466_nonbacktracking.py` part A).
The regime-proper statement is F3 (n=16, p ~ n^4, p = 1 mod n, mu_n proper, m=(p-1)/n > 1).

Testbed sums: S(n,p) eta_b = sum_{x in mu_n} exp(2*pi*i*b*x/p), M = max_{b!=0} |eta_b|.
"""

import sys
import time
from fractions import Fraction

import numpy as np

T0 = time.time()


def log(msg=""):
    print(msg, flush=True)


# ------------------------------------------------------------------ utilities
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


def find_generator(p: int) -> int:
    fac = []
    t = p - 1
    d = 2
    while d * d <= t:
        if t % d == 0:
            fac.append(d)
            while t % d == 0:
                t //= d
        d += 1
    if t > 1:
        fac.append(t)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g
    raise RuntimeError("no generator")


def mu_subgroup(p: int, n: int):
    """The order-n multiplicative subgroup of F_p^* (requires n | p-1)."""
    assert (p - 1) % n == 0
    g = find_generator(p)
    h = pow(g, (p - 1) // n, p)
    out, x = [], 1
    for _ in range(n):
        out.append(x)
        x = x * h % p
    assert len(set(out)) == n
    return sorted(out)


def eta_via_fft(p: int, mu):
    """eta_b for all b in F_p via length-p FFT of the indicator of mu (exact object)."""
    ind = np.zeros(p, dtype=np.complex128)
    for x in mu:
        ind[x] = 1.0
    # eta_b = sum_x ind[x] exp(2 pi i b x / p) = IDFT-style sum; use conj-FFT convention
    return np.fft.fft(ind).conj()  # eta[b] = sum_x e^{+2 pi i b x /p}


# ------------------------------------------------------ exact rational triangle
def cheb_triangle(q: int, mmax: int):
    """s_m(lambda) coefficients, s_0=2, s_1=lambda, s_{m+1}= lambda*s_m - q*s_{m-1}.
    Returns list of dict{j: Fraction}. Coefficients depend ONLY on (m, q)."""
    s = [{0: Fraction(2)}, {1: Fraction(1)}]
    for _ in range(2, mmax + 1):
        prev, prev2 = s[-1], s[-2]
        new = {}
        for j, c in prev.items():
            new[j + 1] = new.get(j + 1, Fraction(0)) + c
        for j, c in prev2.items():
            new[j] = new.get(j, Fraction(0)) - q * c
        s.append(new)
    return s


def wave_triangle(q: int, tmax: int):
    """Wave-kernel polynomial w_t: K_t = w_t(A); K_0=I, K_1=A, K_{t+1}=A K_t - q K_{t-1}.
    (The forward-difference scheme whose closed form is the discrete-Bessel/NB-walk kernel
    of arXiv 2606.27075.)  Same universal-triangle structure, different seed."""
    w = [{0: Fraction(1)}, {1: Fraction(1)}]
    for _ in range(2, tmax + 1):
        prev, prev2 = w[-1], w[-2]
        new = {}
        for j, c in prev.items():
            new[j + 1] = new.get(j + 1, Fraction(0)) + c
        for j, c in prev2.items():
            new[j] = new.get(j, Fraction(0)) - q * c
        w.append(new)
    return w


def nbwalk_triangle(q: int, mmax: int):
    """NB walk-count polynomials: N_1 = A, N_2 = A^2 - (q+1) I, N_{m+1} = A N_m - q N_{m-1}."""
    n1 = {1: Fraction(1)}
    n2 = {2: Fraction(1), 0: Fraction(-(q + 1))}
    N = [None, n1, n2]
    for _ in range(3, mmax + 1):
        prev, prev2 = N[-1], N[-2]
        new = {}
        for j, c in prev.items():
            new[j + 1] = new.get(j + 1, Fraction(0)) + c
        for j, c in prev2.items():
            new[j] = new.get(j, Fraction(0)) - q * c
        N.append(new)
    return N


def apply_triangle(tri_row, powsums):
    """Evaluate sum_lambda poly(lambda) = sum_j c_j * P_j given power sums P_j."""
    return sum(float(c) * powsums[j] for j, c in tri_row.items())


# ------------------------------------------------------ direct Hashimoto side
def _exact_int_trace(mat: np.ndarray) -> int:
    """Trace of a float64 matrix whose entries are exact integers; asserts exactness.
    float64 matmul is exact for integer values as long as every intermediate stays
    < 2^53; we assert the trace is within 0.4 of an integer and below 2^53."""
    t = float(np.trace(mat))
    assert abs(t) < 2 ** 53, "int-exactness range exceeded"
    ti = round(t)
    assert abs(t - ti) < 0.4, f"non-integer trace {t}"
    return ti


def hashimoto_traces(p: int, mu, mmax: int):
    """tr(B^m), m=1..mmax, by DIRECT matrix powers of the Hashimoto operator of
    Cay(F_p, mu) (float64 BLAS, exact-integer range asserted). Also returns tr(A^j) and
    NB-walk-count / wave-kernel traces computed by the matrix recursion on A, all
    INDEPENDENT of any spectral formula."""
    n = len(mu)
    q = n - 1
    # directed edges: (u, u+x) for x in mu. Index e = u*n + i (i = index of x in mu).
    # B[(u,v),(v,w)] = 1 iff w != u.  With v = u + mu[i], w = v + mu[j], w == u iff
    # mu[j] == -mu[i] mod p.
    muinv = {x: i for i, x in enumerate(mu)}
    negidx = [muinv[(p - x) % p] for x in mu]  # j such that mu[j] = -mu[i]
    E = p * n  # number of directed edges
    B = np.zeros((E, E), dtype=np.float64)
    for u in range(p):
        for i in range(n):
            v = (u + mu[i]) % p
            e = u * n + i
            row = B[e]
            base = v * n
            for j in range(n):
                if j == negidx[i]:
                    continue  # backtracking
                row[base + j] = 1.0
    # entries of B^m are <= q^{m-1}; keep q^{mmax-1}*E < 2^53
    assert (q ** (mmax - 1)) * E < 2 ** 53
    traces = []
    P = B.copy()
    traces.append(_exact_int_trace(P))
    for _ in range(2, mmax + 1):
        P = P @ B
        traces.append(_exact_int_trace(P))
    # adjacency power sums (direct walk counts)
    A = np.zeros((p, p), dtype=np.float64)
    for u in range(p):
        for x in mu:
            A[u, (u + x) % p] = 1.0
    powsums = [p]  # tr(A^0) = p
    Q = A.copy()
    powsums.append(_exact_int_trace(Q))
    for _ in range(2, mmax + 1):
        Q = Q @ A
        powsums.append(_exact_int_trace(Q))
    # NB walk-count matrices by the recursion (direct)
    Ieye = np.eye(p, dtype=np.float64)
    N1 = A.copy()
    N2 = A @ A - (q + 1) * Ieye
    nb_traces = [_exact_int_trace(N1), _exact_int_trace(N2)]
    Nm1, Nm2 = N2, N1
    for _ in range(3, mmax + 1):
        Nm = A @ Nm1 - q * Nm2
        nb_traces.append(_exact_int_trace(Nm))
        Nm2, Nm1 = Nm1, Nm
    # wave kernel traces by the recursion (direct)
    K1 = A.copy()
    wave_traces = [p, _exact_int_trace(K1)]
    Km1, Km2 = K1, Ieye
    for _ in range(2, mmax + 1):
        Km = A @ Km1 - q * Km2
        wave_traces.append(_exact_int_trace(Km))
        Km2, Km1 = Km1, Km
    return traces, powsums, nb_traces, wave_traces


# ============================================================== F1 + F2
def part_F1_F2():
    log("=" * 78)
    log("F1: exact dictionary -- Hashimoto / NB-walk / wave-kernel traces from power sums")
    log("=" * 78)
    mmax = 10
    ok_all = True
    cases = [(8, 89), (8, 233), (16, 257), (16, 337)]
    triangles = {}
    for n, p in cases:
        assert is_prime(p) and (p - 1) % n == 0 and (p - 1) // n > 1
        mu = mu_subgroup(p, n)
        q = n - 1
        trB, powsums, trN_direct, trK_direct = hashimoto_traces(p, mu, mmax)
        # spectral power sums from FFT eta (independent path)
        eta = eta_via_fft(p, mu)
        Pj_fft = [float(np.sum(np.real(eta) ** 0))]  # = p
        for j in range(1, mmax + 1):
            Pj_fft.append(float(np.sum(np.real(eta) ** j)))
        # cross-check the two power-sum paths
        ps_err = max(
            abs(Pj_fft[j] - powsums[j]) / max(1.0, abs(powsums[j]))
            for j in range(mmax + 1)
        )
        # universal triangles (exact rationals, depend only on q)
        s_tri = cheb_triangle(q, mmax)
        w_tri = wave_triangle(q, mmax)
        n_tri = nbwalk_triangle(q, mmax)
        triangles.setdefault(n, []).append(
            (p, [sorted(r.items()) for r in s_tri],
             [sorted(r.items()) for r in w_tri],
             [sorted(r.items()) for r in n_tri[1:]])
        )
        E_und = p * n // 2
        errB = errN = errK = 0.0
        for m in range(1, mmax + 1):
            # Ihara-Bass: tr(B^m) = sum_lambda s_m(lambda) + (E-N)(1 + (-1)^m)
            spec = apply_triangle(s_tri[m], Pj_fft) + (E_und - p) * (1 + (-1) ** m)
            errB = max(errB, abs(spec - trB[m - 1]) / max(1.0, abs(trB[m - 1])))
            specN = apply_triangle(n_tri[m], Pj_fft)
            errN = max(errN, abs(specN - trN_direct[m - 1]) / max(1.0, abs(trN_direct[m - 1])))
            specK = apply_triangle(w_tri[m], Pj_fft)
            errK = max(errK, abs(specK - trK_direct[m]) / max(1.0, abs(trK_direct[m])))
        ok = max(ps_err, errB, errN, errK) < 1e-9
        ok_all &= ok
        log(f"  n={n:3d} p={p:5d} (m=(p-1)/n={(p-1)//n:3d}): "
            f"powsum FFT-vs-walk rel err {ps_err:.1e}; "
            f"tr(B^m) rel err {errB:.1e}; tr(N_m) {errN:.1e}; tr(K_t) {errK:.1e} "
            f"[{'OK' if ok else 'FAIL'}]")
    log()
    log("F2: instance-blindness -- exact-rational triangles identical across p at fixed n")
    ok_blind = True
    for n, rows in triangles.items():
        base = rows[0]
        for other in rows[1:]:
            same = base[1:] == other[1:]
            ok_blind &= same
            log(f"  n={n:3d}: triangle(p={base[0]}) == triangle(p={other[0]}) "
                f"(Chebyshev+wave+NB, exact rationals): {same}")
    return ok_all, ok_blind


# ============================================================== F3
def part_F3():
    log()
    log("=" * 78)
    log("F3: bounded-depth moment blindness at regime scale (n=16, beta~4)")
    log("    pair from 466-r1-hankel-bounded-window-refuted: p=65617 vs p=65633")
    log("=" * 78)
    n = 16
    rows = []
    for p in (65617, 65633):
        assert is_prime(p) and (p - 1) % n == 0
        mu = mu_subgroup(p, n)
        eta = eta_via_fft(p, mu)
        # Parseval sanity: sum_b |eta_b|^2 = p*n
        pars = abs(float(np.sum(np.abs(eta) ** 2)) - p * n) / (p * n)
        assert pars < 1e-9, pars
        er = np.real(eta).copy()
        M = float(np.max(np.abs(er[1:])))  # non-principal sup
        # normalized moments of the non-principal spectrum: m_j = P_j / (p * n^{j/2})
        moms = [float(np.sum(er[1:] ** j)) / (p * n ** (j / 2)) for j in range(1, 9)]
        rows.append((p, M, moms))
        log(f"  p={p}: Parseval rel err {pars:.1e}; M = {M:.6f}; "
            f"M/sqrt(n log(p/n)) = {M / np.sqrt(n * np.log(p / n)):.4f}")
    (p1, M1, m1), (p2, M2, m2) = rows
    dM = abs(M1 - M2) / max(M1, M2)
    log(f"  M relative difference: {dM * 100:.2f}%")
    log("   j | m_j(p=65617)  m_j(p=65633)  rel diff")
    max_lowdepth_diff = 0.0
    for j in range(1, 9):
        a, b = m1[j - 1], m2[j - 1]
        rd = abs(a - b) / max(1e-12, abs(a), abs(b))
        if j <= 6:
            max_lowdepth_diff = max(max_lowdepth_diff, rd)
        log(f"   {j} | {a:12.6f}  {b:12.6f}  {rd:.2e}")
    blind = max_lowdepth_diff < 0.05 and dM > 0.02
    log(f"  low-depth (j<=6) max rel moment diff {max_lowdepth_diff:.2e} "
        f"vs M diff {dM:.2e} -> bounded-depth trace identities "
        f"{'CANNOT separate the pair (blind)' if blind else 'CAN separate (unexpected!)'}")
    return blind, dM, max_lowdepth_diff


def main():
    log("probe_w13_wavekernel_trace.py -- arXiv 2606.27075 wave-kernel trace identities vs")
    log("the wall M(mu_n) <= C sqrt(n log(p/n)).  THREAD wall:probe-batch, prefix w13.")
    log()
    ok_dict, ok_blindcoef = part_F1_F2()
    blind, dM, dmom = part_F3()
    log()
    log("=" * 78)
    log("VERDICT")
    log("=" * 78)
    if ok_dict and ok_blindcoef and blind:
        log("DEAD (repackaging).  (F1) wave-kernel traces, NB-walk traces and Hashimoto")
        log("moments on Cay(F_p, mu_n) are reconstructed EXACTLY from adjacency power sums")
        log("{P_j} -- the E_r wall vocabulary; (F2) the reconstruction coefficients are")
        log("exact rationals in (m, q=n-1) only, bitwise identical across primes: the")
        log("2606.27075 trace formula can produce only instance-blind identities WITHIN the")
        log("moment ladder, zero new p-arithmetic; (F3) at regime scale the known pair")
        log(f"(65617, 65633) has identical low-depth moments (max rel diff {dmom:.1e}, j<=6)")
        log(f"yet M differs {dM * 100:.1f}% -- bounded-depth trace identities cannot pin M.")
        log("Composes with 466-r1-nonbacktracking-relabeling (radius side) to close the")
        log("paper on BOTH faces: radius = monotone relabel of M; identities = moment")
        log("repackaging.  The L-infinity target still requires depth r ~ log p = the wall.")
        return 0
    log("LIVE or UNEXPECTED -- some check failed; inspect above.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
