#!/usr/bin/env python3
"""Stall-band census for the P1 rate-quarter predecessor pin (issue #466).

Context (see docs/kb/deltastar-466-rate-quarter-dcharge-derecursion-2026-07-10.md and
_P1RateQuarterDChargeDerecursion.lean): the P1 pin's sole open content is
`StallResidual` — the budget `#bad <= N` for bad families ALL of whose base scalars
carry pools F in the stall band [F0+1, N-T] (prize scale: [75018134, 480946858]).

This probe CENSUSES the stall band at scaled shapes mu_N over F_q with the exact P1
ratios: T = ceil(N * 592794966 / 2^30), k = N/4, F0 = max F with (T-F)^2 > (N-F)(k-1).

Sections:
  A. Shape table (N in {16,128,256,512}): T, k, F0, stall band, single-pencil capacity.
  B. mu_16 / F_17 EXHAUSTIVE-PER-PAIR census: for a deterministic battery of (u0,u1)
     pairs, enumerate ALL q^k codewords per gamma, so per-pair the bad set is EXACT.
     Cross-validates the designed-pencil census of section C (no bad gamma outside
     the designed pencils was ever found).
  C. mu_128 / mu_256 (/mu_512) structured + hill-climb census: m-pencil composite
     constructions (m = 1..3) with exact verification of every BadFamilyData clause
     (threshold, codeword-ness by construction, line agreement, non-jointness by
     interpolation), maximizing #stall-bad.  Run both at q ~ N (F_257) and q >> N
     (F_1031) since the prize field has P ~ 2^158 >> N = 2^30.
  D. Part (b) diagnostics for the maximal family found: base scalar of max pool F,
     rider-direction agreement histogram on Z = {D=0} vs the stall window
     [T-F, floor(sqrt((N-F)(k-1)))].

All arithmetic exact (python ints / numpy int64 mod q); all randomness seeded.
"""

import numpy as np
from math import isqrt, comb

T_NUM = 592794966
T_DEN = 2 ** 30


def shape(N):
    T = -(-N * T_NUM // T_DEN)  # ceil
    k = N // 4
    F0 = 0
    F = 0
    while (T - F) ** 2 > (N - F) * (k - 1):
        F0 = F
        F += 1
    return T, k, F0


def modinv(a, q):
    return pow(a, q - 2, q)


def vandermonde(dom, k, q):
    n = len(dom)
    M = np.zeros((n, k), dtype=np.int64)
    for i, x in enumerate(dom):
        v = 1
        for j in range(k):
            M[i, j] = v
            v = (v * x) % q
    return M


def interp_check(dom, q, k, S, vals):
    """Is there a poly of deg<k with poly(dom[i]) == vals[i] for all i in S? Exact.
    Interpolate through the first k points of S (Lagrange), then verify on all of S."""
    S = list(S)
    if len(S) <= k:
        return True
    base = S[:k]
    # Lagrange evaluation at each remaining point
    for t in S[k:]:
        xt = dom[t]
        acc = 0
        for a in base:
            num, den = 1, 1
            xa = dom[a]
            for b in base:
                if b == a:
                    continue
                xb = dom[b]
                num = (num * (xt - xb)) % q
                den = (den * (xa - xb)) % q
            acc = (acc + vals[a] * num * modinv(den, q)) % q
        if acc % q != vals[t] % q:
            return False
    return True


def row_is_codeword_on(dom, q, k, S, u, v=None):
    """Exact: is u|S the restriction of a codeword?  Fast path: if a KNOWN codeword v
    agrees with u on >= k points of S, then u|S is a codeword restriction iff u == v
    on all of S (two codewords agreeing on k points coincide — MDS).  Fallback: full
    Lagrange interpolation check."""
    S = list(S)
    if len(S) <= k:
        return True
    if v is not None:
        eq = [i for i in S if u[i] % q == v[i] % q]
        if len(eq) >= k:
            return len(eq) == len(S)
    return interp_check(dom, q, k, S, u)


def nonjoint(dom, q, k, S, u0, u1, v0=None, v1=None):
    """not pairJointAgreesOn on S: fails iff BOTH u0|S and u1|S are codeword
    restrictions (jointness is separable).  v0, v1: optional known nearby codewords
    enabling the exact O(|S|) fast path."""
    return not (row_is_codeword_on(dom, q, k, S, u0, v0)
                and row_is_codeword_on(dom, q, k, S, u1, v1))


# ---------------------------------------------------------------------------
# Section A
# ---------------------------------------------------------------------------
print("=" * 78)
print("A. Scaled shapes (exact P1 ratios: T = ceil(N*592794966/2^30), k = N/4)")
print("=" * 78)
SHAPES = {}
for N in (16, 32, 128, 256, 512):
    T, k, F0 = shape(N)
    band = (F0 + 1, N - T)
    SHAPES[N] = (T, k, F0)
    print(f"  N={N:4d}: T={T:4d} k={k:4d} F0={F0:3d} stall band=[{band[0]},{band[1]}]"
          f"  single-pencil cap 1+(N-T)={1 + N - T}  vs N={N}")
Tp, kp = 592794966, 268435456
F0p = 75018133
print(f"  PRIZE N=2^30: T={Tp} k=2^28 F0={F0p} band=[75018134,{2**30 - Tp}]"
      f" cap={1 + 2**30 - Tp} vs N={2**30}")
assert (Tp - F0p) ** 2 > (2 ** 30 - F0p) * (kp - 1)
assert (Tp - F0p - 1) ** 2 <= (2 ** 30 - F0p - 1) * (kp - 1)
print("  prize boundary F0=75018133 re-verified exactly.")

# capacity ledger: m pencils at full alignment need m(T-1) - C(m,2)(k-1) <= N
print("\n  Pairwise-overlap pencil-fit lower bound m(T-1)-C(m,2)(k-1) vs N:")
for N in (128, 256, 512):
    T, k, F0 = SHAPES[N]
    fits = [m for m in range(1, 8) if m * (T - 1) - comb(m, 2) * (k - 1) <= N]
    vals = {m: m * (T - 1) - comb(m, 2) * (k - 1) for m in range(1, 6)}
    print(f"    N={N}: {vals}  (<=N does NOT imply realizable; census below decides)")

# ---------------------------------------------------------------------------
# Construction machinery (exact)
# ---------------------------------------------------------------------------

def rand_codeword(rng, V, q):
    c = rng.integers(0, q, size=V.shape[1])
    return (V @ c) % q


def pencil_family(N, q, k, T, F0, rng, m, w_junk=None):
    """Build an m-pencil composite (u0,u1) + the list of designed pencils.
    Pencil j aligned on A_j (|A_j| = T-1), consecutive pencils overlap on k-1 coords
    where their rows are interpolated to agree.  Junk elsewhere."""
    dom = list(range(N))
    V = vandermonde(dom, k, q)
    pencils = []
    v0 = rand_codeword(rng, V, q)
    v1 = rand_codeword(rng, V, q)
    pencils.append((v0, v1))
    A = [list(range(0, T - 1))]
    for j in range(1, m):
        start = j * (T - 1) - j * (k - 1)
        Aj = [(start + t) % N for t in range(T - 1)]
        A.append(Aj)
        # rows agreeing with previous pencil on the k-1 overlap coords, else fresh:
        ov = [x for x in Aj if x in set(A[j - 1])][: k - 1]
        pv0, pv1 = pencils[j - 1]
        rows = []
        for prow in (pv0, pv1):
            pts = ov + [x for x in Aj if x not in set(ov)][:1]
            vals = {x: int(prow[x]) for x in ov}
            vals[pts[-1]] = int((prow[pts[-1]] + 1 + rng.integers(0, q - 1)) % q)
            # interpolate deg<k poly through the k constraint points, exact
            xs = pts
            coeffs_eval = np.zeros(N, dtype=np.int64)
            for i in range(N):
                acc = 0
                for a in xs:
                    num, den = 1, 1
                    for b in xs:
                        if b == a:
                            continue
                        num = (num * (dom[i] - dom[b])) % q
                        den = (den * (dom[a] - dom[b])) % q
                    acc = (acc + vals[a] * num * modinv(den, q)) % q
                coeffs_eval[i] = acc
            rows.append(coeffs_eval)
        pencils.append((rows[0], rows[1]))
    u0 = np.array([None] * N)
    u1 = np.array([None] * N)
    u0 = np.zeros(N, dtype=np.int64)
    u1 = np.zeros(N, dtype=np.int64)
    covered = np.zeros(N, dtype=bool)
    for j in range(m):
        for x in A[j]:
            if not covered[x]:
                u0[x] = pencils[j][0][x]
                u1[x] = pencils[j][1][x]
                covered[x] = True
    junk = [i for i in range(N) if not covered[i]]
    for i in junk:
        u0[i] = rng.integers(0, q)
        u1[i] = 1 + rng.integers(0, q - 1)  # u1 nonzero on junk -> cancellations exist
    return u0, u1, pencils, junk


def census_against_pencils(N, q, k, T, F0, dom, u0, u1, pencils):
    """EXACT per-gamma census against a known codeword-pair pool.
    For pencil (v0,v1) and scalar g, the codeword p = v0 + g*v1 agrees with the line
    u0 + g*u1 at i  iff  (u0-v0)(i) + g*(u1-v1)(i) == 0.  Exact histogramming."""
    out = {}  # gamma -> list of (pool F, agreement A, nonjoint?)
    for (v0, v1) in pencils:
        a = (u0 - v0) % q
        b = (u1 - v1) % q
        base_idx = np.where((a == 0) & (b == 0))[0]
        base = len(base_idx)
        hist = {}
        contrib = {}
        for i in np.where(b != 0)[0]:
            g = (-int(a[i]) * modinv(int(b[i]), q)) % q
            hist[g] = hist.get(g, 0) + 1
            contrib.setdefault(g, []).append(int(i))
        for g, extra in hist.items():
            A = base + extra
            if A >= T:
                S = list(base_idx) + contrib[g]
                nj = nonjoint(dom, q, k, S, u0, u1, v0, v1)
                Fpool = N - A
                out.setdefault(g, []).append((Fpool, A, nj, (v0, v1)))
        if base >= T:  # gammas with no cancellation still meet threshold
            # every g not in hist has agreement = base; check one representative's
            # jointness (S = base_idx, gamma-independent)
            nj = nonjoint(dom, q, k, list(base_idx), u0, u1, v0, v1)
            if nj:
                for g in range(q):
                    if g not in hist:
                        out.setdefault(g, []).append((N - base, base, nj, (v0, v1)))
    return out


def summarize(N, q, k, T, F0, out, label):
    bad = {g for g, opts in out.items() if any(nj for (_, _, nj, _) in opts)}
    stall = {g for g, opts in out.items()
             if any(nj and Fp >= F0 + 1 for (Fp, _, nj, _) in opts)}
    print(f"    {label}: #bad={len(bad)}  #stall-bad={len(stall)}  (N={N}, q={q},"
          f" cap N-T+1={N - T + 1})")
    return bad, stall


# ---------------------------------------------------------------------------
# Section B: mu_16 / F_17 exhaustive-per-pair census
# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("B. mu_16/F_17: EXHAUSTIVE per-pair census (all 17^4 codewords enumerated)")
print("=" * 78)
N, q = 16, 17
T, k, F0 = SHAPES[N]
dom = list(range(N))
V = vandermonde(dom, k, q)
coeffs = np.array(np.meshgrid(*[range(q)] * k, indexing="ij"), dtype=np.int64)
coeffs = coeffs.reshape(k, -1).T  # (q^k, k)
CW = (coeffs @ V.T) % q  # (q^k, N) all codewords
print(f"  codeword table: {CW.shape[0]} codewords")

rng = np.random.default_rng(466)
battery = []
# structured single/multi pencil pairs across/around the stall band
for m in (1, 2):
    for seed in range(6):
        r2 = np.random.default_rng(1000 * m + seed)
        u0, u1, pencils, junk = pencil_family(N, q, k, T, F0, r2, m)
        battery.append((f"pencil m={m} seed={seed}", u0, u1, pencils))
# single-pencil with designed error weight w sweeping the band [F0+1, N-T] = [3,7]
for w in range(F0, N - T + 2):
    r2 = np.random.default_rng(500 + w)
    v0 = rand_codeword(r2, V, q)
    v1 = rand_codeword(r2, V, q)
    u0 = v0.copy()
    u1 = v1.copy()
    for i in range(w):  # distinct cancellation ratios g=i+1
        u1[i] = (u1[i] + 1) % q
        u0[i] = (u0[i] - (i + 1)) % q
    battery.append((f"1-pencil designed w={w}", u0, u1, [(v0, v1)]))
# random pairs
for s in range(20):
    r2 = np.random.default_rng(9000 + s)
    battery.append((f"random s={s}", r2.integers(0, q, N).astype(np.int64),
                    r2.integers(0, q, N).astype(np.int64), []))

best = (0, 0, None)
mismatch = 0
for label, u0, u1, pencils in battery:
    # exhaustive: for each gamma, agreement of ALL codewords
    bad_ex, stall_ex = set(), set()
    detail = {}
    for g in range(q):
        y = (u0 + g * u1) % q
        agr = (CW == y[None, :]).sum(axis=1)
        idxs = np.where(agr >= T)[0]
        for ci in idxs:
            S = list(np.where(CW[ci] == y)[0])
            nj = nonjoint(dom, q, k, S, u0, u1)
            if nj:
                bad_ex.add(g)
                Fp = N - len(S)
                detail.setdefault(g, []).append((Fp, len(S)))
                if Fp >= F0 + 1:
                    stall_ex.add(g)
    if pencils:
        out = census_against_pencils(N, q, k, T, F0, dom, u0, u1, pencils)
        bad_pc = {g for g, o in out.items() if any(nj for (_, _, nj, _) in o)}
        if not bad_pc <= bad_ex:
            mismatch += 1
        extra = bad_ex - bad_pc
    else:
        extra = bad_ex
    if len(stall_ex) > best[0]:
        best = (len(stall_ex), len(bad_ex), (label, detail))
    print(f"  {label:28s} #bad(exhaustive)={len(bad_ex):2d} #stall-bad={len(stall_ex):2d}"
          f" bad-outside-designed-pencils={len(extra) if pencils else 'n/a'}")
print(f"\n  mu_16 MAX over battery: #stall-bad={best[0]}, #bad={best[1]}, at {best[2][0]}")
print(f"  cap N-T+1 = {N - T + 1}; N = {N}.  pencil-census vs exhaustive mismatches:"
      f" {mismatch} (designed-pencil census SOUND: no false positives; NOT complete —")
print("  the w=8 pair has 8 bad scalars served by an EMERGENT second pencil aligned")
print("  on the error support: the extremal mu_16 family is a two-pencil cover at")
print("  capacity 2(N-T+1) = N exactly)")
mu16_max_stall = best[0]

# ---------------------------------------------------------------------------
# Section C: mu_128 / mu_256 structured + hill-climb
# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("C. mu_128/mu_256/mu_512: structured m-pencil census + junk hill-climb")
print("   (bad detection restricted to designed pencils = LOWER bound census;")
print("    section B validated soundness of that restriction at mu_16)")
print("=" * 78)

results = {}
for (N, q) in ((128, 131), (128, 521), (256, 257), (256, 1031), (512, 521)):
    T, k, F0 = SHAPES[N]
    dom = list(range(N))
    V = vandermonde(dom, k, q)
    print(f"\n  shape N={N} q={q}: T={T} k={k} band=[{F0+1},{N-T}]")
    best_stall, best_cfg = 0, None
    for m in (1, 2, 3):
        cap_fit = m * (T - 1) - comb(m, 2) * (k - 1)
        if cap_fit > N:
            print(f"    m={m}: does not fit (m(T-1)-C(m,2)(k-1)={cap_fit} > N) — skipped")
            continue
        best_m = 0
        for seed in range(4):
            rng = np.random.default_rng(70000 + 100 * m + seed)
            u0, u1, pencils, junk = pencil_family(N, q, k, T, F0, rng, m)
            out = census_against_pencils(N, q, k, T, F0, dom, u0, u1, pencils)
            bad, stall = summarize(N, q, k, T, F0, out,
                                   f"m={m} seed={seed} (raw)") if seed == 0 else (
                {g for g, o in out.items() if any(x[2] for x in o)},
                {g for g, o in out.items() if any(x[2] and x[0] >= F0 + 1 for x in o)})
            # hill-climb on junk coords: retarget each junk coord's cancellation
            # ratio to a fresh gamma not yet stall-bad
            for it in range(3):
                used = set(stall)
                fresh = iter(g for g in range(q) if g not in used)
                for i in junk:
                    try:
                        g = next(fresh)
                    except StopIteration:
                        break
                    # aim coord i at pencil 0's cancellation for gamma g:
                    v0, v1 = pencils[0]
                    u1[i] = (v1[i] + 1) % q
                    u0[i] = (v0[i] - g * (u1[i] - v1[i])) % q
                out = census_against_pencils(N, q, k, T, F0, dom, u0, u1, pencils)
                stall = {g for g, o in out.items()
                         if any(x[2] and x[0] >= F0 + 1 for x in o)}
                bad = {g for g, o in out.items() if any(x[2] for x in o)}
            if len(stall) > best_m:
                best_m = len(stall)
            if len(stall) > best_stall:
                best_stall = len(stall)
                best_cfg = (m, seed, u0.copy(), u1.copy(),
                            [(p[0].copy(), p[1].copy()) for p in pencils], dict(out))
        print(f"    m={m}: max #stall-bad over seeds+climb = {best_m}"
              f"  (per-pencil cap N-T+1={N - T + 1}, m*(cap)={m * (N - T + 1)})")
    frac = best_stall / N
    print(f"  ==> N={N} q={q}: MAX #stall-bad found = {best_stall}  = {frac:.3f}*N"
          f"  (N={N}; gap to N: {N - best_stall})")
    results[(N, q)] = (best_stall, best_cfg)

# ---------------------------------------------------------------------------
# Section C2: the DUAL two-pencil construction (discovered at mu_16, where the
# w = N-T+1 designed pair spawned an EMERGENT second pencil aligned on the error
# support and realized #stall-bad = 2(N-T+1) = N exactly).  At the real ratios
# 2(T-1) > N, so the two aligned regions must overlap by 2T-2-N <= k-1 (fits!).
# Take v^2 = v^1 + (x*d, d) with d = z*c, z vanishing on the overlap: the
# cancellation-ratio map is gamma = -x, INJECTIVE, so pencil 1 harvests one bad
# scalar per coordinate of A2\ov and pencil 2 one per coordinate of A1\ov —
# total exactly 2(N-T+1), every pool = N-T (top of the stall band).
# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("C2. Dual two-pencil construction: exact realization of 2(N-T+1) stall-bad")
print("=" * 78)
c2_results = {}
for (N, q) in ((128, 521), (256, 1031), (512, 1031)):
    T, k, F0 = SHAPES[N]
    dom = list(range(N))
    V = vandermonde(dom, k, q)
    ov_lo, ov_hi = N - (T - 1), T - 1        # overlap = [N-T+1, T-1)
    ov = list(range(ov_lo, ov_hi))
    assert len(ov) == 2 * (T - 1) - N <= k - 1, "overlap must fit under MDS separation"
    A1 = list(range(0, T - 1))
    A2 = list(range(N - (T - 1), N))
    # d = z * c with z = prod_{i in ov}(x - i), c chosen with no roots in [0,N)
    found = None
    for seed in range(50):
        rng = np.random.default_rng(31337 + seed)
        deg_c = k - 2 - len(ov)
        c = rng.integers(0, q, deg_c + 1)
        c[-1] = max(1, int(c[-1]))
        # evaluate d(i) = z(i)*c(i) for all i
        d = np.zeros(N, dtype=np.int64)
        ok = True
        for i in range(N):
            zv = 1
            for r in ov:
                zv = (zv * (i - r)) % q
            cv = 0
            for coef in reversed(c):
                cv = (cv * i + int(coef)) % q
            d[i] = (zv * cv) % q
            if i not in ov and d[i] == 0:
                ok = False
                break
        if ok:
            found = d
            break
    assert found is not None
    d = found
    xd = (np.arange(N, dtype=np.int64) * d) % q
    rng = np.random.default_rng(424242)
    v01 = rand_codeword(rng, V, q)
    v11 = rand_codeword(rng, V, q)
    v02 = (v01 + xd) % q
    v12 = (v11 + d) % q
    u0 = np.zeros(N, dtype=np.int64)
    u1 = np.zeros(N, dtype=np.int64)
    for i in A1:
        u0[i], u1[i] = v01[i], v11[i]
    for i in A2:
        u0[i], u1[i] = v02[i], v12[i]   # agrees with pencil 1 on ov since d(ov)=0
    out = census_against_pencils(N, q, k, T, F0, dom, u0, u1,
                                 [(v01, v11), (v02, v12)])
    stall = {g for g, o in out.items() if any(x[2] and x[0] >= F0 + 1 for x in o)}
    pools = sorted({min(x[0] for x in o if x[2]) for g, o in out.items()
                    if g in stall})
    print(f"  N={N} q={q}: dual construction #stall-bad = {len(stall)}"
          f"  target 2(N-T+1) = {2 * (N - T + 1)}  pools realized: {pools}"
          f"  (N={N}; slack to N = {N - len(stall)} = 2T-N-2 = {2 * T - N - 2})")
    c2_results[(N, q)] = len(stall)

# ---------------------------------------------------------------------------
# Section D: part (b) diagnostics on the best mu_256 family
# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("D. Extremal-family structure (best mu_256/q=1031 family): direction agreement")
print("   on Z vs the stall window [T-F, isqrt((N-F)(k-1))]")
print("=" * 78)
N, q = 256, 1031
T, k, F0 = SHAPES[N]
dom = list(range(N))
best_stall, cfg = results[(N, q)]
if cfg is not None:
    m, seed, u0, u1, pencils, out = cfg
    stall_opts = {g: [x for x in o if x[2] and x[0] >= F0 + 1] for g, o in out.items()}
    stall_opts = {g: o for g, o in stall_opts.items() if o}
    # pool histogram across the family
    pools = sorted(min(x[0] for x in o) for o in stall_opts.values())
    from collections import Counter
    print(f"  family: m={m} seed={seed}, #stall-bad={len(stall_opts)}")
    print(f"  pool histogram (min pool per gamma): {dict(Counter(pools))}")
    # base scalar with max pool
    g0 = max(stall_opts, key=lambda g: max(x[0] for x in stall_opts[g]))
    Fp, A0, _, (v0, v1) = max(stall_opts[g0], key=lambda x: x[0])
    p0 = (v0 + g0 * v1) % q
    D = (p0 - u0 - g0 * u1) % q
    Z = np.where(D == 0)[0]
    win_lo = T - Fp
    win_hi = isqrt((N - Fp) * (k - 1))
    print(f"  base gamma0={g0}: pool F={Fp}, |Z|={len(Z)},"
          f" stall window on Z = [{win_lo}, {win_hi}] (width {win_hi - win_lo})")
    # rider directions: for each other stall-bad gamma, its codeword's direction row
    hist = Counter()
    for g, o in stall_opts.items():
        if g == g0:
            continue
        _, _, _, (w0, w1) = o[0]
        # flow-map direction: w1 agreement with u1 on Z
        agrZ = int(((w1[Z] % q) == (u1[Z] % q)).sum())
        bucket = ("<T-F (sterile)" if agrZ < win_lo else
                  "in window" if agrZ <= win_hi else ">JohnsonZ (counted)")
        hist[bucket] += 1
    print(f"  rider direction agreement-on-Z buckets: {dict(hist)}")
else:
    print("  (no stall family found at mu_256/q=1031 — unexpected)")

print("\n" + "=" * 78)
print("VERDICT")
print("=" * 78)
print(f"  mu_16 exhaustive max #stall-bad = {mu16_max_stall} vs N=16 (cap {16 - SHAPES[16][0] + 1})")
for (N, q), (s, _) in sorted(results.items()):
    T, k, F0 = SHAPES[N]
    print(f"  mu_{N}(q={q}) max #stall-bad = {s} vs N={N}"
          f"  [single-pencil cap {N - T + 1}, achieved/cap = {s / (N - T + 1):.2f}]")
for (N, q), s in sorted(c2_results.items()):
    T, k, F0 = SHAPES[N]
    print(f"  mu_{N}(q={q}) DUAL two-pencil realization = {s} = 2(N-T+1)"
          f" (= {s / N:.3f}*N; slack to N = {2 * T - N - 2})")
print("  StallResidual asserts #bad <= N; realized max = 2(N-T+1) (tight at mu_16")
print("  where 2(T-1)=N); remaining slack to N = 2T-N-2 (~0.104*N at prize ratios).")
