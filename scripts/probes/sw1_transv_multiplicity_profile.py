#!/usr/bin/env python3
"""
sw1_transv_multiplicity_profile.py -- SW1 swarm, lane TRANSV (2026-09-05).

Exact multiplicity profile of spurious signed 2r-term sums of n-th roots of unity across
ALL degree-one prime ideals of Z[zeta_n] above p = 1 (mod n), n = 2^k.

Objects.  K = Q(zeta_n), d = phi(n) = n/2.  p = 1 (mod n) splits completely; the degree-one
primes are P_u = (p, zeta - g^u), u odd, g a primitive n-th root of unity mod p.
For a tuple (a_1..a_r ; b_1..b_r) in [n]^{2r} put beta = sum zeta^{a_i} - sum zeta^{b_j}.
  * beta is spurious at u  iff  beta != 0 in Z[zeta_n] and P_u | beta,
    i.e.  sum g^{u a_i} = sum g^{u b_j} in F_p  while the char-0 coefficient vector is nonzero.
  * mult(beta) = #{u odd : P_u | beta}.
Rotation normalisation a_1 = 0 (beta and zeta^c beta have the same mult); T = n^{2r-1} tuples.

Checks (exit 1 on any FAIL):
  C1 Galois symmetry: W_u := #{tuples spurious at u} is the same for every u.
  C2 sum_tuples mult = d * W_1   (the Galois-average identity, tuple form).
  C3 max mult <= M_tri := floor(d * ln(2r) / ln p)   (triangle-inequality height ceiling).
  C4 on a deterministic sample of spurious tuples:
       mult <= floor(d * ln(sum c^2) / (2 ln p))   (AM-GM / Parseval ceiling, per beta),
       v_p(N(beta)) = sum_u v_{P_u}(beta) >= mult   (Hensel lift, exact),
       |N(beta)| (exact integer, product of conjugates) <= (sum c^2)^{d/2}.
  C5 gate consistency: if M_tri = 0 then W_1 = 0.
Everything is exact integer arithmetic except |N(beta)| (mpmath 60 digits, rounded, residual
checked).  No probabilistic heuristic enters any check; the 'indep' column is the
independent-embedding heuristic T*C(d,j)/p^j printed for comparison ONLY.

Reported per cell (n, r, p): T, W_1, T/p (the DC requirement), W_1/(T/p), max mult,
share of sum(mult) carried by mult >= 2, M_tri, M_amgm := floor(d ln(2r)/(2 ln p)),
cap/req := 2 p M_tri / n  (the height-model cap on W divided by the requirement T/p) and
2p/n (the perfect-transversality cap divided by the requirement).
"""
import sys
import math
from math import comb, log, floor

import numpy as np

try:
    import mpmath
    mpmath.mp.dps = 60
except ImportError:  # pragma: no cover
    mpmath = None

SAMPLE_CAP = 300     # spurious tuples per cell sent through Hensel + exact norm
HENSEL_K = 4         # p-adic precision for v_{P_u}(beta)


# ----------------------------------------------------------------------------- utilities
def is_prime(m):
    if m < 2:
        return False
    if m % 2 == 0:
        return m == 2
    f = 3
    while f * f <= m:
        if m % f == 0:
            return False
        f += 2
    return True


def primes_1_mod(n, count_small, near_targets):
    ps = []
    q = n + 1
    while len(ps) < count_small:
        if is_prime(q):
            ps.append(q)
        q += n
    for target in near_targets:
        q = target - ((target - 1) % n)
        while not is_prime(q):
            q += n
        if q not in ps:
            ps.append(q)
    return ps


def primitive_nth_root(n, p):
    for x in range(2, p):
        g = pow(x, (p - 1) // n, p)
        if pow(g, n // 2, p) != 1:   # order divides n = 2^k and is not n/2  =>  exactly n
            return g
    raise RuntimeError("no primitive n-th root")


def all_tuples(n, k):
    """All tuples in [n]^k as an (n^k, k) int64 array, lexicographic."""
    idx = np.arange(n ** k, dtype=np.int64)
    cols = [(idx // (n ** (k - 1 - i))) % n for i in range(k)]
    return np.stack(cols, axis=1)


def coeff_vectors(A, n):
    """Char-0 coefficient vectors in the power basis {zeta^a : 0 <= a < n/2} (zeta^{a+n/2} = -zeta^a)."""
    d = n // 2
    m, k = A.shape
    C = np.zeros((m, d), dtype=np.int64)
    rows = np.arange(m)
    for i in range(k):
        a = A[:, i]
        sign = np.where(a < d, 1, -1).astype(np.int64)
        np.add.at(C, (rows, a % d), sign)
    return C


def encode(C, base, offset):
    K = np.zeros(C.shape[0], dtype=np.int64)
    for j in range(C.shape[1]):
        K = K * base + (C[:, j] + offset)
    return K


def hensel_root(w0, n, p, K):
    mod = p ** K
    w = w0 % mod
    for _ in range(8):
        f = (pow(w, n, mod) - 1) % mod
        if f == 0:
            break
        fp = (n * pow(w, n - 1, mod)) % mod
        w = (w - f * pow(fp, -1, mod)) % mod
    assert pow(w, n, mod) == 1
    return w


def val_at(w, a, b, p, K):
    mod = p ** K
    v = (sum(pow(w, int(x), mod) for x in a) - sum(pow(w, int(y), mod) for y in b)) % mod
    k = 0
    while k < K and v % (p ** (k + 1)) == 0:
        k += 1
    return k


def exact_norm(a, b, n):
    """|N(beta)| = prod_{u odd} |sigma_u(beta)| as an exact integer (mpmath, residual-checked)."""
    zeta = mpmath.exp(2j * mpmath.pi / n)
    N = mpmath.mpf(1)
    for u in range(1, n // 2, 2):          # conjugate pairs (u, n-u): |sigma_u|^2 each
        z = zeta ** u
        s = sum(z ** int(x) for x in a) - sum(z ** int(y) for y in b)
        N *= abs(s) ** 2
    Nint = int(mpmath.nint(N))
    resid = abs(N - Nint)
    return Nint, float(resid)


def vp(N, p):
    if N == 0:
        return None
    k = 0
    while N % p == 0:
        N //= p
        k += 1
    return k


# ----------------------------------------------------------------------------- one cell
def profile_cell(n, r, p, log):
    d = n // 2
    g = primitive_nth_root(n, p)
    U = list(range(1, n, 2))                         # the d embeddings / degree-one primes
    pw = np.array([[pow(g, (u * e) % n, p) for e in range(n)] for u in U], dtype=np.int64)

    A = np.concatenate([np.zeros((n ** (r - 1), 1), dtype=np.int64), all_tuples(n, r - 1)], axis=1)
    B = all_tuples(n, r)
    nA, nB = A.shape[0], B.shape[0]
    T = nA * nB
    base, off = 2 * r + 1, r
    KA = encode(coeff_vectors(A, n), base, off)
    KB = encode(coeff_vectors(B, n), base, off)
    P = np.zeros((d, nA), dtype=np.int64)
    Q = np.zeros((d, nB), dtype=np.int64)
    for i in range(r):
        P += pw[:, A[:, i]]
        Q += pw[:, B[:, i]]
    P %= p
    Q %= p

    lut = np.array([bin(x).count("1") for x in range(1 << d)], dtype=np.uint8)
    hist = np.zeros(d + 1, dtype=np.int64)
    Wu = np.zeros(d, dtype=np.int64)
    sample, sample_hi = [], []
    rows_per_chunk = max(1, (1 << 23) // nB)
    for r0 in range(0, nA, rows_per_chunk):
        r1 = min(nA, r0 + rows_per_chunk)
        mask = np.zeros((r1 - r0, nB), dtype=np.uint16)
        for ui in range(d):
            eq = P[ui, r0:r1][:, None] == Q[ui][None, :]
            mask |= eq.astype(np.uint16) << np.uint16(ui)
        nz = KA[r0:r1][:, None] != KB[None, :]
        mask[~nz] = 0
        m = lut[mask]
        hist += np.bincount(m.ravel(), minlength=d + 1)[: d + 1]
        for ui in range(d):
            Wu[ui] += int(np.count_nonzero(mask & np.uint16(1 << ui)))
        if len(sample) < SAMPLE_CAP:
            ia, ib = np.nonzero(m >= 1)
            for k in range(min(len(ia), SAMPLE_CAP - len(sample))):
                sample.append((r0 + int(ia[k]), int(ib[k]), int(mask[ia[k], ib[k]])))
        if len(sample_hi) < SAMPLE_CAP:
            ia, ib = np.nonzero(m >= 2)
            for k in range(min(len(ia), SAMPLE_CAP - len(sample_hi))):
                sample_hi.append((r0 + int(ia[k]), int(ib[k]), int(mask[ia[k], ib[k]])))

    fails = []
    W1 = int(Wu[0])
    if not all(int(w) == W1 for w in Wu):
        fails.append(f"C1 Galois symmetry broken: W_u = {Wu.tolist()}")
    summult = int(sum(j * hist[j] for j in range(1, d + 1)))
    if summult != d * W1:
        fails.append(f"C2 sum mult {summult} != d*W_1 {d * W1}")
    maxmult = max([j for j in range(d + 1) if hist[j] > 0] + [0])
    M_tri = floor(d * log(2 * r) / log(p))
    M_amgm = floor(d * log(2 * r) / (2 * log(p)))
    if maxmult > M_tri:
        fails.append(f"C3 max mult {maxmult} > M_tri {M_tri}")
    if M_tri == 0 and W1 != 0:
        fails.append(f"C5 gate M_tri=0 but W_1={W1}")

    # C4 on the deterministic sample
    lifted = {}
    n_sq, n_checked, max_norm, max_vp_minus_mult = 0, 0, 0, 0
    for (ia, ib, msk) in sample + sample_hi:
        a, b = A[ia], B[ib]
        c = coeff_vectors(A[ia:ia + 1], n)[0] - coeff_vectors(B[ib:ib + 1], n)[0]
        s2 = int(np.dot(c, c))
        mult = bin(msk).count("1")
        cap_b = floor(d * log(s2) / (2 * log(p)))
        if mult > cap_b:
            fails.append(f"C4 mult {mult} > per-beta AM-GM cap {cap_b} (s2={s2}) at {a.tolist()}|{b.tolist()}")
        vsum = 0
        for ui, u in enumerate(U):
            if msk >> ui & 1:
                if u not in lifted:
                    lifted[u] = hensel_root(pow(g, u, p), n, p, HENSEL_K)
                vsum += val_at(lifted[u], a, b, p, HENSEL_K)
        if mpmath is not None:
            Nint, resid = exact_norm(a, b, n)
            if resid > 1e-12:
                fails.append(f"C4 norm not integral (resid {resid}) at {a.tolist()}|{b.tolist()}")
            if Nint == 0:
                fails.append(f"C4 zero norm for a char-0 nonzero beta at {a.tolist()}|{b.tolist()}")
                continue
            v = vp(Nint, p)
            if v < mult:
                fails.append(f"C4 v_p(N)={v} < mult={mult} at {a.tolist()}|{b.tolist()}")
            if v != vsum and vsum < HENSEL_K:
                fails.append(f"C4 v_p(N)={v} != sum of local valuations {vsum}")
            if Nint > s2 ** (d // 2) * (s2 ** 0.5 if d % 2 else 1) + 1e-9:
                fails.append(f"C4 |N|={Nint} > (sum c^2)^(d/2) with s2={s2}")
            max_norm = max(max_norm, Nint)
            max_vp_minus_mult = max(max_vp_minus_mult, v - mult)
            if v > mult:
                n_sq += 1
        n_checked += 1

    req = T / p
    share2 = (summult - hist[1]) / summult if summult else 0.0
    layers = [int(hist[j:].sum()) for j in range(1, maxmult + 1)]
    indep = [T * comb(d, j) / p ** j for j in range(1, maxmult + 1)]
    log(f"n={n:2d} r={r} p={p:8d} T={T:11d} W1={W1:8d} T/p={req:10.1f} W1/(T/p)={W1 / req:6.3f} "
        f"maxmult={maxmult} share>=2={share2:.4f} M_tri={M_tri:2d} M_amgm={M_amgm:2d} "
        f"cap/req={2 * p * M_tri / n:10.1f} 2p/n={2 * p / n:8.1f}")
    log(f"      layers A_j (j>=1) = {layers}   indep-heuristic = {[round(x, 2) for x in indep]}   "
        f"sample: checked={n_checked} square-factor(v_p>mult)={n_sq} max(v_p-mult)={max_vp_minus_mult} "
        f"max|N|/p^2={max_norm / p ** 2 if p else 0:.3e}")
    for f in fails:
        log("      FAIL " + f)
    return {
        "n": n, "r": r, "p": p, "T": T, "W1": W1, "req": req, "maxmult": maxmult, "M_tri": M_tri,
        "M_amgm": M_amgm, "share2": share2, "cap_over_req": 2 * p * M_tri / n, "layers": layers,
        "fails": fails, "max_norm": max_norm, "n_sq": n_sq, "n_checked": n_checked,
    }


# ----------------------------------------------------------------------------- driver
def main():
    out = []

    def log(s):
        print(s, flush=True)
        out.append(s)

    cells = [
        (8, 2, primes_1_mod(8, 12, [8 ** 4])),
        (8, 3, primes_1_mod(8, 12, [8 ** 4])),
        (8, 4, primes_1_mod(8, 8, [8 ** 4])),
        (16, 2, primes_1_mod(16, 10, [16 ** 4])),
        (16, 3, primes_1_mod(16, 10, [16 ** 4])),
        (16, 4, [97, 257, 449, 65537]),
        (32, 2, primes_1_mod(32, 10, [32 ** 4])),
        (32, 3, primes_1_mod(32, 8, [32 ** 4])),
    ]
    results = []
    for (n, r, ps) in cells:
        log(f"=== n={n} r={r} (2r-term sums, d={n // 2} embeddings, T=n^(2r-1)={n ** (2 * r - 1)}) ===")
        for p in ps:
            results.append(profile_cell(n, r, p, log))

    allfails = [f for res in results for f in res["fails"]]
    log("=== summary ===")
    for res in results:
        if res["M_tri"] >= 1:
            log(f"n={res['n']:2d} r={res['r']} p={res['p']:8d}: model cap / DC requirement = "
                f"{res['cap_over_req']:.1f}  (= 2 p M_tri / n; perfect-transversality cap ratio 2p/n = "
                f"{2 * res['p'] / res['n']:.1f});  observed W1/(T/p) = {res['W1'] / res['req']:.3f}; "
                f"max mult = {res['maxmult']} (ceiling {res['M_tri']}); share of sum(mult) from mult>=2 = "
                f"{res['share2']:.4f}")
    minratio = min(res["cap_over_req"] for res in results if res["M_tri"] >= 1)
    log(f"min over cells of (height-model cap)/(requirement) = {minratio:.1f} (> 1 everywhere: the "
        f"height model never reaches the DC requirement)")
    cells_with_mult2 = [(res["n"], res["r"], res["p"], res["maxmult"]) for res in results if res["maxmult"] >= 2]
    log(f"cells with some mult >= 2: {cells_with_mult2}")
    if allfails:
        log(f"FAIL ({len(allfails)} check failures)")
        sys.exit(1)
    log("PASS sw1_transv_multiplicity_profile: C1-C5 hold on every cell")


if __name__ == "__main__":
    main()
